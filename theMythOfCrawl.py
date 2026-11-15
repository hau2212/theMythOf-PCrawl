# -*- coding: utf-8 -*-
from __future__ import unicode_literals
"""
theMythOfCrawl - Burp Suite extension (Jython 2.7, legacy Extender API)

Multi-role API request cloning and grouped Repeater dispatching for
authorization / access-control testing of applications you are permitted to test.

  * N role profiles, each with header/cookie/JWT rules (REPLACE / ADD / REMOVE / COOKIE_SET / COOKIE_REMOVE)
  * Proxy capture with scope, static-extension, API-regex, method and dedup filters
  * Manual trigger via context menu (Proxy, Target, Repeater, Logger, ...)
  * 1-to-N cloning: one request per enabled role, method/URL/params/body preserved
  * Optional background replay recording status, length, time and full req/resp
  * Grouped Repeater tabs: "[G01:POST /v1/transfer] 01_Admin"
  * Feature / Button Action Batching (Tên 1: API 1, API 2... | Tên 2: API 3, API 4...)
  * Color-coded permission & error highlighting (Yellow INFO when any role call fails or differs)

Threading model
  * Burp listener threads only copy bytes and enqueue work (never block).
  * One single-thread "capture" executor builds groups (deterministic IDs + dedup).
  * A resizable thread pool performs all network I/O (makeHttpRequest).
  * Worker threads never touch Swing: they only record what changed. A single Swing
    Timer (UI_TICK_MS) drains that record on the EDT, so a burst of 500 captured APIs
    costs a handful of repaints instead of 500 full tree rebuilds.
  * Role requests are virtual: a group keeps the original request plus each role's
    rule snapshot, and the role request is built only when it is viewed, sent or
    pushed to Repeater. Responses live in Burp's temp file, not on the heap.
"""

import base64
import json
import random
import re
import sys
import threading
import time
import traceback
from collections import deque

from burp import IBurpExtender
from burp import ITab
from burp import IHttpListener
from burp import IContextMenuFactory
from burp import IExtensionStateListener
from burp import IMessageEditorController
from burp import IHttpRequestResponse

from java.awt import (BorderLayout, FlowLayout, GridBagLayout, GridBagConstraints, GridLayout,
                      Insets, Dimension, Color, Font, Toolkit, RenderingHints, Cursor)
from java.awt.datatransfer import StringSelection
from java.awt.event import MouseAdapter, ActionListener, FocusAdapter, WindowAdapter
from java.lang import Runnable, Boolean, Integer, String, Throwable
from java.util import ArrayList, Arrays
from java.util.concurrent import Executors, TimeUnit
from java.io import File
from java.nio.file import Files
from javax.swing import (JPanel, JLabel, JButton, JCheckBox, JTextField, JTable, JScrollPane,
                         JSplitPane, JTabbedPane, JTextArea, JMenuItem, JPopupMenu, JOptionPane,
                         JFileChooser, JDialog, JComboBox, JSpinner, SpinnerNumberModel,
                         ListSelectionModel, SwingUtilities, BorderFactory, DefaultCellEditor,
                         BoxLayout, Box, JTree, JRadioButton, ButtonGroup, JFrame)
from javax.swing import Timer, UIManager, Icon, Scrollable, JComponent, KeyStroke, AbstractAction
from javax.swing.event import (ListSelectionListener, TreeSelectionListener, ChangeListener,
                               TreeWillExpandListener, DocumentListener)
from javax.swing.table import AbstractTableModel, DefaultTableCellRenderer
from javax.swing.tree import (DefaultMutableTreeNode, DefaultTreeModel, DefaultTreeCellRenderer,
                              TreeSelectionModel, TreePath, TreeCellRenderer)
from javax.swing.filechooser import FileNameExtensionFilter

try:
    basestring
    _UNICODE_TYPE = unicode
    _BYTES_TYPE = str
except NameError:  # CPython 3 (offline unit tests only)
    basestring = str
    _UNICODE_TYPE = str
    _BYTES_TYPE = bytes


def u_text(val):
    """
    Convert any value (Python 2 str/unicode, Python 3 str/bytes, or Java String)
    into a clean Unicode string, automatically healing UTF-8-as-Latin-1 mojibake.
    """
    if val is None:
        return ""
    if isinstance(val, _BYTES_TYPE):
        try:
            s = val.decode("utf-8")
        except Exception:
            s = val.decode("latin-1", "replace")
    elif isinstance(val, _UNICODE_TYPE):
        s = val
    else:
        try:
            s = _UNICODE_TYPE(val)
        except Exception:
            s = "%s" % val
    # Heal UTF-8 bytes that were previously decoded as Latin-1 (e.g. "Chá»©c nÄƒng")
    if any(0x80 <= ord(ch) <= 0xFF for ch in s):
        try:
            healed = s.encode("latin-1").decode("utf-8")
            if healed != s:
                return healed
        except Exception:
            pass
    return s


# =============================================================================
# Constants
# =============================================================================

EXT_NAME = "theMythOfCrawl"
EXT_VERSION = "1.10.0"
SETTINGS_KEY_ROLES = "tmoc.roles.v1"
SETTINGS_KEY_ORIGINAL = "tmoc.original_profile.v1"
SETTINGS_KEY_ROLE_SCOPES = "tmoc.role_scopes.v1"
SETTINGS_KEY_TARGET_HITS = "tmoc.target_hits.v1"
ORIGINAL_PROFILE_NAME = "00_API GỐC (Acc Crawl)"
ORIGINAL_LABEL = "[API GỐC] 00_Original (Acc Crawl)"
SETTINGS_KEY_CONFIG = "tmoc.config.v2"
SETTINGS_KEY_TARGETS = "tmoc.targets.v1"

REMOVE_TOKEN = "[REMOVE]"
MODE_REPLACE = "REPLACE"              # overwrite first occurrence (drop duplicates) or add if missing
MODE_ADD = "ADD"                      # always append a new header line (allows duplicates)
MODE_REMOVE = "REMOVE"                # strip every occurrence of the header
MODE_COOKIE_SET = "COOKIE_SET"        # set/replace a single cookie key=value inside Cookie header
MODE_COOKIE_REMOVE = "COOKIE_REMOVE"  # remove a single cookie key from Cookie header
HEADER_MODES = [MODE_REPLACE, MODE_ADD, MODE_REMOVE, MODE_COOKIE_SET, MODE_COOKIE_REMOVE]

# Grouping / View Modes (Default: Per-API Grouping, switchable to Hierarchical Tree)
GROUP_MODE_PER_API = "PER_API"
GROUP_MODE_HIERARCHY = "HIERARCHY"
DEFAULT_HIERARCHY_PATH = 'Toppage > menu > button "Search"'

# Audit / Color Highlighting Levels
AUDIT_NONE = "NONE"          # Not replayed yet
AUDIT_OK = "OK"              # Green: All roles 2xx OK with consistent response
AUDIT_INFO = "INFO"          # Yellow INFO: Role call failed (401/403/4xx/5xx/Error) or permission diff across roles
AUDIT_WARN = "WARN"          # Orange WARN: Guest/unauthenticated role returned 2xx (suspected auth bypass)
AUDIT_ERROR = "ERROR"        # Red ERROR: Server 5xx / connection timeout across roles
AUDIT_REDIRECT = "REDIRECT"  # Blue: 3xx Redirect

AUDIT_FILTER_ALL = "ALL"
AUDIT_FILTER_OPTIONS = [
    ("Tất cả API (All)", AUDIT_FILTER_ALL),
    ("Vàng INFO: Có Role lỗi / Lệch quyền", AUDIT_INFO),
    ("Cam WARN: Nghi vấn Bypass (Guest 2xx)", AUDIT_WARN),
    ("Đỏ ERROR: Có lỗi 5xx / Mất kết nối", AUDIT_ERROR),
    ("Xanh OK: Tất cả Role 2xx", AUDIT_OK),
    ("Chưa Gửi / Chưa Replay (Pending)", AUDIT_NONE),
]

DEFAULT_STATIC_EXT = ("js,mjs,css,map,png,jpg,jpeg,gif,bmp,ico,svg,webp,avif,tif,tiff,"
                      "woff,woff2,ttf,otf,eot,mp3,mp4,m4a,webm,wav,ogg,avi,mov,flv,swf")
DEFAULT_API_REGEX = r"(?i)(/api/|/v[0-9]+(/|$)|/graphql|/rest/|/rpc/|/services?/|\.json$)"

# Strict manual-by-default: neither auto_send nor auto_repeater is active unless user explicitly allows
DEFAULT_CONFIG = {
    "capture_enabled": False,
    "in_scope_only": True,
    "ignore_static": True,
    "static_ext": DEFAULT_STATIC_EXT,
    "api_regex_enabled": True,
    "api_regex": DEFAULT_API_REGEX,
    "ignore_options_head": True,
    "dedup": True,
    "dedup_normalize_ids": False,
    "dedup_per_feature": False,
    "auto_repeater": False,
    "auto_send": False,
    "number_roles_in_tab": True,
    "include_feature_in_tab": False,
    "threads": 5,
    "short_path_len": 40,
    "store_on_disk": True,
    # Outgoing request pacing (see SendDispatcher)
    "auto_send_original": False,
    "send_profile": "HUMAN",
    "send_delay_ms": 700,
    "send_jitter_pct": 40,
    "host_concurrency": 1,
    "max_retries": 3,
    # Target API list imported from Excel (see TargetList)
    "target_only": False,
    "target_use_position": True,
    "target_allow_prefix": False,
    "target_ids_as_params": True,
    "target_query_mode": "ignore",
    # "STT. path" copy (see copy_label_for)
    "copy_format": "{stt}. {path}",
    "copy_stt_fallback": "none",
    "copy_counter": 1,
    "excel_position_copy_format": True,
}

TARGET_MATCH_KEYS = ("target_allow_prefix", "target_ids_as_params", "target_query_mode")
TARGET_QUERY_MODES = [
    ("ignore", "Bỏ qua query trong file (mặc định)"),
    ("names", "Request phải có đúng tên tham số query của dòng"),
    ("values", "Tên + giá trị query phải khớp (app định tuyến kiểu ?action=getUser)"),
]
COPY_STT_FALLBACKS = [
    ("none", "Không đánh số (chỉ copy path)"),
    ("counter", "Số tăng dần theo lần copy (1, 2, 3...) - dễ đếm"),
    ("api", "Dùng số API # (thứ tự bắt)"),
]

# (key, label, delay_ms, jitter_pct, per-host concurrency); CUSTOM keeps the user's numbers.
SEND_PROFILES = [
    ("HUMAN", "Như người dùng thật - an toàn (khuyên dùng)", 700, 40, 1),
    ("BALANCED", "Cân bằng", 250, 30, 2),
    ("FAST", "Nhanh - dễ bị chặn 429", 60, 10, 4),
    ("CUSTOM", "Tùy chỉnh", None, None, None),
]
RETRYABLE_STATUS = (429, 503)

# One Swing timer flushes every pending UI change; nothing else repaints tables or trees.
UI_TICK_MS = 200
LOG_SYSTEM_MAX = 3000      # system / action lines kept for the Log tab
LOG_PER_API_MAX = 200      # log lines kept per captured API

STATE_ORIGIN = "GỐC (Proxy)"
STATE_NOT_SENT = "Not sent"
STATE_QUEUED = "Queued"
STATE_RETRY = "Chờ thử lại"
STATE_SENDING = "Sending"
STATE_DONE = "Done"
STATE_ERROR = "Error"

_UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$")
_NUM_RE = re.compile(r"^[0-9]+$")
_HEX_RE = re.compile(r"^[0-9a-fA-F]{16,}$")
_ROLE_NUM_PREFIX_RE = re.compile(r"^[0-9]+[_\-. ]")
_JWT_RE = re.compile(r"(eyJ[A-Za-z0-9_\-]+\.eyJ[A-Za-z0-9_\-]+\.[A-Za-z0-9_\-]*)")

# =============================================================================
# Pure logic (no Burp / Swing dependency -> unit-testable under CPython)
# =============================================================================


def sanitize_header_name(name):
    """Header names: trimmed, no CR/LF/colon/whitespace. Returns '' if invalid."""
    if name is None:
        return ""
    n = ("%s" % name).strip()
    if not n or re.search(r"[\r\n:\s]", n):
        return ""
    return n


def sanitize_header_value(value):
    """Values: CR/LF removed so a rule can never produce a malformed request."""
    if value is None:
        return ""
    return ("%s" % value).replace("\r", "").replace("\n", "").strip()


def normalize_mode(mode, value):
    m = ("%s" % (mode or "")).strip().upper()
    is_rm_val = value is not None and ("%s" % value).strip().upper() == REMOVE_TOKEN
    if m in (MODE_COOKIE_SET, MODE_COOKIE_REMOVE):
        return MODE_COOKIE_REMOVE if (m == MODE_COOKIE_REMOVE or is_rm_val) else MODE_COOKIE_SET
    if is_rm_val:
        return MODE_REMOVE
    if m in HEADER_MODES:
        return m
    return MODE_REPLACE


def _header_name_of(line):
    idx = line.find(":")
    if idx <= 0:
        return None
    return line[:idx].strip().lower()


def _parse_cookie_pairs(headers):
    """Extract ordered (key, raw_segment) pairs across all Cookie headers."""
    pairs = []
    for h in headers:
        if _header_name_of(h) != "cookie":
            continue
        val = h.split(":", 1)[1]
        for seg in val.split(";"):
            s = seg.strip()
            if not s:
                continue
            k = s.split("=", 1)[0].strip() if "=" in s else s
            pairs.append((k, s))
    return pairs


def apply_cookie_rule(headers, cookie_name, cookie_value, remove=False):
    """
    Modify a single cookie key inside the Cookie header while preserving all
    other cookies on the request.
    """
    cname = sanitize_header_name(cookie_name)
    if not cname:
        return list(headers)
    cval = sanitize_header_value(cookie_value)
    pairs = _parse_cookie_pairs(headers)
    has_cookie_hdr = any(_header_name_of(h) == "cookie" for h in headers)
    if remove:
        new_segs = [seg for k, seg in pairs if k != cname]
    else:
        target_seg = "%s=%s" % (cname, cval)
        new_segs = []
        replaced = False
        for k, seg in pairs:
            if k == cname:
                if not replaced:
                    new_segs.append(target_seg)
                    replaced = True
            else:
                new_segs.append(seg)
        if not replaced:
            new_segs.append(target_seg)
    if not new_segs:
        return [h for h in headers if _header_name_of(h) != "cookie"]
    cookie_line = "Cookie: %s" % "; ".join(new_segs)
    if not has_cookie_hdr:
        return list(headers) + [cookie_line]
    out = []
    emitted = False
    for h in headers:
        if _header_name_of(h) == "cookie":
            if not emitted:
                out.append(cookie_line)
                emitted = True
        else:
            out.append(h)
    return out


def apply_header_rules(header_lines, rules):
    """
    header_lines: list of str, index 0 is the request line ("GET /x HTTP/1.1").
    rules: list of {"name", "value", "mode"} applied in order.
      - REPLACE / ADD / REMOVE operate on whole HTTP headers.
      - COOKIE_SET / COOKIE_REMOVE operate on individual cookie keys in Cookie:.
    Returns a new list; the request line is never modified.
    """
    lines = [("%s" % l) for l in header_lines]
    if not lines:
        return lines
    request_line = lines[0]
    headers = lines[1:]
    for rule in rules or []:
        name = sanitize_header_name(rule.get("name"))
        if not name:
            continue
        raw_value = rule.get("value")
        mode = normalize_mode(rule.get("mode"), raw_value)
        if mode == MODE_COOKIE_REMOVE:
            headers = apply_cookie_rule(headers, name, "", remove=True)
            continue
        if mode == MODE_COOKIE_SET:
            headers = apply_cookie_rule(headers, name, raw_value, remove=False)
            continue
        lname = name.lower()
        if mode == MODE_REMOVE:
            headers = [h for h in headers if _header_name_of(h) != lname]
            continue
        new_line = "%s: %s" % (name, sanitize_header_value(raw_value))
        if mode == MODE_ADD:
            headers.append(new_line)
            continue
        out = []
        replaced = False
        for h in headers:
            if _header_name_of(h) == lname:
                if not replaced:
                    out.append(new_line)
                    replaced = True
            else:
                out.append(h)
        if not replaced:
            out.append(new_line)
        headers = out
    return [request_line] + headers


def format_jwt_bearer(token, prefix="Bearer"):
    """Normalize a raw JWT or Bearer string into 'Bearer <token>' (or [REMOVE])."""
    t = sanitize_header_value(token)
    if not t:
        return ""
    if t.upper() == REMOVE_TOKEN:
        return REMOVE_TOKEN
    if t.lower().startswith("authorization:"):
        t = t.split(":", 1)[1].strip()
    pfx = "Bearer" if prefix is None else ("%s" % prefix).strip()
    if pfx and not t.lower().startswith(pfx.lower() + " "):
        return "%s %s" % (pfx, t)
    return t


def _b64url_decode(seg):
    s = ("%s" % seg).strip().replace("-", "+").replace("_", "/")
    pad = len(s) % 4
    if pad:
        s += "=" * (4 - pad)
    raw = base64.b64decode(s.encode("ascii"))
    return raw.decode("utf-8", "replace")


def decode_jwt_preview(text):
    """
    Find all JWTs in text (or role rules) and return a human-readable decoded
    preview of Header + Payload (including sub/role/exp).
    """
    matches = _JWT_RE.findall("%s" % (text or ""))
    if not matches:
        return "No JWT (eyJ...) found in this role's rules."
    blocks = []
    for idx, tok in enumerate(matches):
        parts = tok.split(".")
        try:
            hdr_txt = _b64url_decode(parts[0])
            pay_txt = _b64url_decode(parts[1])
            try:
                hdr_obj = json.loads(hdr_txt)
                hdr_pretty = json.dumps(hdr_obj, indent=2)
            except Exception:
                hdr_pretty = hdr_txt
            try:
                pay_obj = json.loads(pay_txt)
                pay_pretty = json.dumps(pay_obj, indent=2)
            except Exception:
                pay_obj = {}
                pay_pretty = pay_txt
            summary = []
            for k in ("sub", "user", "username", "email", "role", "roles", "scope", "tenant", "iss", "exp", "iat"):
                if isinstance(pay_obj, dict) and k in pay_obj:
                    summary.append("%s=%s" % (k, pay_obj[k]))
            head_line = "JWT #%d" % (idx + 1)
            if summary:
                head_line += "  [" + ", ".join(summary) + "]"
            blocks.append("%s\nHeader:\n%s\nPayload:\n%s" % (head_line, hdr_pretty, pay_pretty))
        except Exception as e:
            blocks.append("JWT #%d: decode error (%s)" % (idx + 1, e))
    return "\n\n".join(blocks)


def parse_static_extensions(text):
    exts = set()
    for part in re.split(r"[,\s;]+", text or ""):
        p = part.strip().lower().lstrip(".")
        if p:
            exts.add(p)
    return exts


def strip_query(path):
    return (path or "/").split("?", 1)[0].split("#", 1)[0] or "/"


def path_extension(path):
    last = strip_query(path).rsplit("/", 1)[-1]
    if "." not in last:
        return ""
    return last.rsplit(".", 1)[-1].lower()


def is_static_path(path, ext_set):
    ext = path_extension(path)
    return bool(ext) and ext in ext_set


def normalize_path_ids(path):
    out = []
    for s in strip_query(path).split("/"):
        if _NUM_RE.match(s) or _UUID_RE.match(s) or _HEX_RE.match(s):
            out.append("{id}")
        else:
            out.append(s)
    return "/".join(out)


def dedup_key(method, protocol, host, port, path, normalize_ids=False):
    p = normalize_path_ids(path) if normalize_ids else strip_query(path)
    return "%s|%s://%s:%s|%s" % ((method or "").upper(), (protocol or "").lower(),
                                 (host or "").lower(), port, p)


def short_path(path, max_len=40):
    p = strip_query(path)
    if max_len and len(p) > max_len:
        p = "..." + p[-max(max_len - 3, 1):]
    return p


def format_group_id(gid):
    return "G%02d" % gid


def format_api_label(gid):
    return "API %d" % gid


def split_hierarchy_path(path_text):
    """
    Split a hierarchical group path like 'Toppage > menu > button "Search"' into
    clean non-empty hierarchy segments: ['Toppage', 'menu', 'button "Search"'].
    """
    raw = u_text(path_text or "").strip()
    if not raw:
        return ["Toppage"]
    parts = [p.strip() for p in raw.split(">") if p.strip()]
    return parts if parts else [raw]


def normalize_hierarchy_path(parts_or_text):
    """Return canonical 'Level1 > Level2 > Level3' string."""
    if isinstance(parts_or_text, (list, tuple)):
        parts = [u_text(p).strip() for p in parts_or_text if u_text(p).strip()]
    else:
        parts = split_hierarchy_path(parts_or_text)
    return " > ".join(parts) if parts else "Toppage"


def hierarchy_matches_prefix(group_path, prefix_path):
    """
    True if group_path is inside prefix_path in the hierarchy tree.
    Example:
      group_path  = 'Toppage > menu > button "Search"'
      prefix_path = 'Toppage'               -> True
      prefix_path = 'Toppage > menu'        -> True
      prefix_path = 'Toppage > menu > button "Search"' -> True
      prefix_path = 'Settings'              -> False
    """
    if not prefix_path:
        return True
    g_parts = [p.lower() for p in split_hierarchy_path(group_path)]
    p_parts = [p.lower() for p in split_hierarchy_path(prefix_path)]
    if len(p_parts) > len(g_parts):
        return False
    return g_parts[:len(p_parts)] == p_parts


def split_hierarchy_3_boxes(path_text):
    """Split a hierarchy path into 3 quick UI boxes: (Page, Menu, Action/Button)."""
    parts = split_hierarchy_path(path_text)
    p1 = parts[0] if len(parts) >= 1 else "Toppage"
    p2 = parts[1] if len(parts) >= 2 else ""
    p3 = " > ".join(parts[2:]) if len(parts) >= 3 else ""
    return p1, p2, p3


def join_hierarchy_3_boxes(p1, p2, p3):
    """Combine the 3 quick UI boxes (Page, Menu, Action/Button) into a canonical path."""
    parts = []
    for seg in (p1, p2, p3):
        for sub in u_text(seg or "").split(">"):
            s = sub.strip()
            if s:
                parts.append(s)
    return " > ".join(parts) if parts else "Toppage"


def append_hierarchy_segment(path_text, new_segment):
    """Append 1 or more sub-folder levels (separated by '>') to path_text."""
    parts = split_hierarchy_path(path_text)
    for sub in u_text(new_segment or "").split(">"):
        s = sub.strip()
        if s:
            parts.append(s)
    return normalize_hierarchy_path(parts)


def pop_hierarchy_segment(path_text):
    """Remove the last sub-folder level from path_text (keeps at least 1 level)."""
    parts = split_hierarchy_path(path_text)
    if len(parts) > 1:
        parts = parts[:-1]
    return normalize_hierarchy_path(parts)


def replace_hierarchy_segment_at(path_text, index, new_segment):
    """Replace segment at 0-based index (can expand into multiple segments if '>' is used)."""
    parts = split_hierarchy_path(path_text)
    if not (0 <= index < len(parts)):
        return normalize_hierarchy_path(parts)
    replacement = [s.strip() for s in u_text(new_segment or "").split(">") if s.strip()]
    if not replacement:
        return delete_hierarchy_segment_at(path_text, index)
    new_parts = parts[:index] + replacement + parts[index + 1:]
    return normalize_hierarchy_path(new_parts)


def insert_hierarchy_segment_after(path_text, index, new_segment):
    """Insert 1 or more sub-folder segments right after 0-based index."""
    parts = split_hierarchy_path(path_text)
    inserted = [s.strip() for s in u_text(new_segment or "").split(">") if s.strip()]
    if not inserted:
        return normalize_hierarchy_path(parts)
    pos = max(0, min(len(parts), index + 1))
    new_parts = parts[:pos] + inserted + parts[pos:]
    return normalize_hierarchy_path(new_parts)


def delete_hierarchy_segment_at(path_text, index):
    """Delete segment at 0-based index from path_text (keeps 'Toppage' if last segment removed)."""
    parts = split_hierarchy_path(path_text)
    if 0 <= index < len(parts):
        del parts[index]
    return normalize_hierarchy_path(parts) if parts else "Toppage"


def replace_hierarchy_prefix(full_path, old_prefix, new_prefix):
    """
    If full_path starts with old_prefix, replace those leading segments with new_prefix
    while keeping all deeper child sub-folders intact!
    """
    if not hierarchy_matches_prefix(full_path, old_prefix):
        return normalize_hierarchy_path(full_path)
    f_parts = split_hierarchy_path(full_path)
    old_parts = split_hierarchy_path(old_prefix)
    new_parts = split_hierarchy_path(new_prefix)
    tail = f_parts[len(old_parts):]
    return normalize_hierarchy_path(new_parts + tail)


def fast_extract_method_and_path(req_bytes):
    """
    Ultra-fast extraction of (method, path) from the first line of raw request bytes
    WITHOUT copying the full request/response array or invoking Java analyzeRequest.
    """
    if req_bytes is None:
        return None, None
    try:
        limit = min(len(req_bytes), 512)
        if isinstance(req_bytes, _BYTES_TYPE):
            first_chunk = req_bytes[:limit]
            if not isinstance(first_chunk, str):
                first_chunk = first_chunk.decode("latin-1", "replace")
        else:
            chars = []
            for i in range(limit):
                b = req_bytes[i]
                if b == 13 or b == 10:  # CR or LF
                    break
                chars.append(chr(b & 0xFF))
            first_chunk = "".join(chars)
        line = first_chunk.split("\r", 1)[0].split("\n", 1)[0]
        parts = line.split(" ")
        if len(parts) >= 2:
            method = parts[0].strip().upper()
            target = parts[1].strip()
            if target.startswith("http://") or target.startswith("https://"):
                idx = target.find("/", target.find("://") + 3)
                path = target[idx:] if idx >= 0 else "/"
            else:
                path = target or "/"
            return method, path
    except Exception:
        pass
    return None, None


def format_feature_label(fid, name):
    clean = u_text(name).strip()
    if not clean or clean == ("%d" % fid):
        return "Tên %d" % fid
    return "Tên %d: %s" % (fid, clean)


def display_role_name(role_name, index, number_roles):
    name = u_text(role_name) or ("role%d" % (index + 1))
    if number_roles and not _ROLE_NUM_PREFIX_RE.match(name):
        return "%02d_%s" % (index + 1, name)
    return name


def repeater_tab_name(gid, method, path, role_display, max_len=40, fid=None, include_feature=False):
    grp_tag = format_group_id(gid)
    if include_feature and fid is not None:
        grp_tag = "F%02d-%s" % (fid, grp_tag)
    return "[%s:%s %s] %s" % (grp_tag, (method or "").upper(),
                              short_path(path, max_len), u_text(role_display))


def compact_repeater_tab_name(gid, role_display, fid=None, include_feature=False):
    """
    Ultra-compact Repeater tab name (e.g. 'G01•01_Admin' or 'F01•G01•01_Admin')
    so 10 role tabs take up minimal width on Burp Repeater's tab bar.
    """
    grp_tag = format_group_id(gid)
    if include_feature and fid is not None:
        grp_tag = "F%02d•%s" % (fid, grp_tag)
    return "%s•%s" % (grp_tag, u_text(role_display))


def is_stripped_auth_role(role_dict):
    """
    True if a role represents an unauthenticated / stripped-credentials profile
    (e.g. Guest / Anon or removes Authorization/Cookie without setting any token).
    """
    if not isinstance(role_dict, dict):
        return False
    rname = u_text(role_dict.get("name", "")).lower()
    if any(tag in rname for tag in ("guest", "anon", "unauth", "noauth", "public", "khach")):
        return True
    rules = role_dict.get("headers", []) or []
    if not rules:
        return False
    auth_removed = False
    auth_added = False
    for r in rules:
        hn = u_text(r.get("name", "")).lower()
        mode = r.get("mode", MODE_REPLACE)
        if hn in ("authorization", "cookie", "x-auth-token", "x-api-key") or mode in (MODE_COOKIE_SET, MODE_COOKIE_REMOVE):
            if mode in (MODE_REMOVE, MODE_COOKIE_REMOVE):
                auth_removed = True
            else:
                auth_added = True
    return auth_removed and not auth_added


def evaluate_role_result(group, res):
    """
    Classify a single role's replay result for color highlighting:
      - AUDIT_INFO (Yellow Info): Role call failed (401/403/4xx/5xx/Connection error) or body length differs
      - AUDIT_WARN (Orange Warn): Guest / stripped-auth role returned 2xx when other roles failed or matched Admin
      - AUDIT_OK (Green OK)     : Role call succeeded (2xx) with normal body length
      - AUDIT_REDIRECT (Blue)   : Role call returned 3xx redirect
      - AUDIT_NONE              : Not replayed yet
    Returns (audit_level, badge_text) and caches on res for O(1) table rendering.
    """
    if res is None:
        return AUDIT_NONE, "-"
    if getattr(res, "is_original", False):
        if res.status is None:
            lvl, badge = AUDIT_NONE, "API GỐC (Chưa có Response)"
        elif 200 <= int(res.status) < 300:
            lvl, badge = AUDIT_OK, "API GỐC (Acc Crawl: %d)" % int(res.status)
        elif 300 <= int(res.status) < 400:
            lvl, badge = AUDIT_REDIRECT, "API GỐC (Redirect: %d)" % int(res.status)
        else:
            lvl, badge = AUDIT_INFO, "API GỐC (Status: %d)" % int(res.status)
        res._audit_level = lvl
        res._audit_badge = badge
        return lvl, badge
    if res.state == STATE_ERROR:
        err_msg = u_text(res.error or "Timeout / Connection Error")
        if len(err_msg) > 34:
            err_msg = err_msg[:31] + "..."
        lvl, badge = AUDIT_INFO, "INFO: Lỗi gọi API (%s)" % err_msg
        res._audit_level = lvl
        res._audit_badge = badge
        return lvl, badge
    if res.status is None:
        lvl, badge = AUDIT_NONE, u_text(res.state)
        res._audit_level = lvl
        res._audit_badge = badge
        return lvl, badge
    code = int(res.status)
    if code == 401:
        lvl, badge = AUDIT_INFO, "INFO: Chưa xác thực (401)"
    elif code == 403:
        lvl, badge = AUDIT_INFO, "INFO: Không đủ quyền (403)"
    elif 400 <= code < 500:
        lvl, badge = AUDIT_INFO, "INFO: Role gọi lỗi (%d)" % code
    elif code >= 500:
        lvl, badge = AUDIT_INFO, "INFO: Lỗi Server (%d)" % code
    elif 300 <= code < 400:
        lvl, badge = AUDIT_REDIRECT, "INFO: Chuyển hướng (%d)" % code
    elif 200 <= code < 300:
        results = getattr(group, "results", []) if group is not None else []
        any_denied = any(r.status in (401, 403) for r in results if r is not res and r.status is not None)
        if getattr(res, "is_stripped_auth", False) and any_denied:
            lvl, badge = AUDIT_WARN, "WARN: Guest trả về %d!" % code
        else:
            base_len = None
            if results:
                for r in results:
                    if r.status is not None and 200 <= r.status < 300 and r.length is not None:
                        base_len = r.length
                        break
            if base_len is None and group is not None:
                base_len = getattr(group, "orig_length", None)
            if base_len is not None and res.length is not None and res.length != base_len:
                delta = res.length - base_len
                lvl, badge = AUDIT_INFO, "INFO: 2xx lệch Body (%+dB)" % delta
            else:
                lvl, badge = AUDIT_OK, "OK: Thành công (%d)" % code
    else:
        lvl, badge = AUDIT_INFO, "INFO: Status %d" % code
    res._audit_level = lvl
    res._audit_badge = badge
    return lvl, badge


def evaluate_group_audit(group):
    """
    Evaluate all role results of an API Group to determine its row highlight color and summary:
      - If ANY role in the API failed (401/403/4xx/5xx/STATE_ERROR) or roles differ in status/length
        -> returns (AUDIT_INFO, "INFO: ...") for Yellow Info highlighting.
      - If all replayed roles succeeded with 2xx -> returns (AUDIT_OK, "OK: ...").
      - If not replayed yet -> returns (AUDIT_NONE, "Chưa Gửi (1 Gốc + N Role)").
    Caches on group._audit_level / group._audit_summary for O(1) Swing table rendering.
    """
    if group is None:
        return AUDIT_NONE, "-"
    if not getattr(group, "results", None):
        # No role was enabled at capture time: the API stands on its original request alone.
        orig = getattr(group, "orig_result", None)
        status = orig.status if orig is not None else None
        if status is None:
            lvl, summary = AUDIT_NONE, "API gốc (chưa có response)"
        else:
            code = int(status)
            if 200 <= code < 300:
                lvl = AUDIT_OK
            elif 300 <= code < 400:
                lvl = AUDIT_REDIRECT
            else:
                lvl = AUDIT_INFO
            summary = "API gốc (%d)" % code
        group._audit_level = lvl
        group._audit_summary = summary
        return lvl, summary
    done = [r for r in group.results if r.status is not None or r.state == STATE_ERROR]
    if not done:
        lvl, summary = AUDIT_NONE, "Chưa Gửi (1 Gốc + %d Role)" % len(group.results)
        group._audit_level = lvl
        group._audit_summary = summary
        return lvl, summary
    ok_list = [r for r in done if r.status is not None and 200 <= r.status < 300]
    err_list = [r for r in done if r.state == STATE_ERROR or (r.status is not None and r.status >= 400)]
    redir_list = [r for r in done if r.status is not None and 300 <= r.status < 400]

    if err_list:
        codes = []
        for r in err_list:
            c_label = "ERR" if r.state == STATE_ERROR else ("%d" % r.status)
            if c_label not in codes:
                codes.append(c_label)
        codes_str = ",".join(codes[:4])
        if ok_list:
            lvl, summary = AUDIT_INFO, "INFO: %d OK / %d Lỗi (%s)" % (len(ok_list), len(err_list), codes_str)
        else:
            lvl, summary = AUDIT_INFO, "INFO: Cả %d Role lỗi (%s)" % (len(err_list), codes_str)
    elif ok_list:
        lengths = set([r.length for r in ok_list if r.length is not None])
        if redir_list:
            lvl, summary = AUDIT_INFO, "INFO: %d OK / %d Redirect (3xx)" % (len(ok_list), len(redir_list))
        elif len(lengths) > 1:
            lvl, summary = AUDIT_INFO, "INFO: Cả %d Role 2xx (Lệch Body)" % len(ok_list)
        else:
            lvl, summary = AUDIT_OK, "OK: Cả %d Role 2xx" % len(ok_list)
    elif redir_list:
        lvl, summary = AUDIT_REDIRECT, "INFO: %d Role Redirect (3xx)" % len(redir_list)
    else:
        lvl, summary = AUDIT_NONE, "Đang xử lý"

    group._audit_level = lvl
    group._audit_summary = summary
    return lvl, summary


def audit_from_counts(total, flagged, ok):
    """(audit_level, summary) of a branch from its API counters."""
    if total <= 0:
        return AUDIT_NONE, "-"
    if flagged > 0:
        return AUDIT_INFO, "INFO: %d/%d API có Role lỗi/lệch" % (flagged, total)
    if ok > 0:
        return AUDIT_OK, "OK: %d/%d API 2xx" % (ok, total)
    return AUDIT_NONE, "Chưa Gửi (%d API)" % total


def _group_level(g):
    lvl = getattr(g, "_audit_level", None)
    if lvl is None:
        lvl, _ = evaluate_group_audit(g)
    return lvl


def evaluate_feature_audit(feature_groups):
    """Summarize the audit status across all API groups belonging to a Feature/Hierarchy node."""
    flagged = 0
    ok = 0
    total = 0
    for g in feature_groups or []:
        total += 1
        lvl = _group_level(g)
        if lvl in (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR):
            flagged += 1
        elif lvl == AUDIT_OK:
            ok += 1
    return audit_from_counts(total, flagged, ok)


def hierarchy_key(parts):
    """Case-insensitive identity of a hierarchy prefix (matches hierarchy_matches_prefix)."""
    return " > ".join([p.lower() for p in parts])


class HierarchyStats(object):
    """
    Everything the tables, the trees and the status bar need to know about the captured
    APIs, computed in ONE pass. Views read these counters instead of re-filtering the
    whole API list per cell / per folder.
    """

    def __init__(self, features=None, groups=None):
        self.features = list(features or [])
        self.groups = list(groups or [])
        self.by_fid = {}
        self.prefix = {}       # hierarchy_key -> [total, flagged, ok]
        self.paths = []        # ordered unique canonical paths (branches first, then stray API paths)
        self.total = 0
        self.flagged = 0
        self.ok = 0
        self.info_exact = 0
        self.target_hits = set()
        seen = set()
        for f in self.features:
            np = normalize_hierarchy_path(f.name)
            if np not in seen:
                seen.add(np)
                self.paths.append(np)
        for g in self.groups:
            self.by_fid.setdefault(getattr(g, "fid", 1), []).append(g)
            if getattr(g, "target", None) is not None:
                self.target_hits.add(id(g.target))
            lvl = _group_level(g)
            is_flagged = lvl in (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR)
            is_ok = (lvl == AUDIT_OK)
            self.total += 1
            if is_flagged:
                self.flagged += 1
            if is_ok:
                self.ok += 1
            if lvl == AUDIT_INFO:
                self.info_exact += 1
            parts = split_hierarchy_path(getattr(g, "feature_name", "") or DEFAULT_HIERARCHY_PATH)
            np = " > ".join(parts)
            if np not in seen:
                seen.add(np)
                self.paths.append(np)
            lowered = [p.lower() for p in parts]
            for i in range(len(lowered)):
                key = " > ".join(lowered[:i + 1])
                c = self.prefix.get(key)
                if c is None:
                    c = [0, 0, 0]
                    self.prefix[key] = c
                c[0] += 1
                if is_flagged:
                    c[1] += 1
                if is_ok:
                    c[2] += 1

    def prefix_counts(self, parts):
        return self.prefix.get(hierarchy_key(parts), (0, 0, 0))

    def groups_of(self, fid):
        return self.by_fid.get(fid, [])


EXCEL_TOKEN = u"[Excel #%s]"


def excel_badge(group):
    """'[Excel #200]' when the API matches a row of the imported file, else ''."""
    e = getattr(group, "target", None)
    if e is None or e.stt is None or u_text(e.stt).strip() == "":
        return u""
    return EXCEL_TOKEN % u_text(e.stt)


def roles_label(group):
    return u"API gốc" if not group.results else u"1 gốc + %d role" % len(group.results)


def group_tree_label(g, audit_summary):
    badge = excel_badge(g)
    text = u"%s   ·   %s %s%s   ·   %s" % (format_api_label(g.gid), g.method, (badge + u" ") if badge else u"",
                                         short_path(g.path, 48), roles_label(g))
    if audit_summary and not audit_summary.startswith(u"API gốc"):
        text += u"   ·   %s" % audit_summary
    elif audit_summary and not g.results and u"(" in audit_summary:
        text += u"   ·   %s" % audit_summary[audit_summary.index(u"("):]
    return text


def result_tree_label(r, badge):
    status = r.status if r.status is not None else r.state
    length = ("%d B" % r.length) if r.length is not None else "-"
    return "%s   ·   %s   ·   %s   ·   %s" % (r.role_name, status, length, badge)


def build_feature_rows(stats, active_fid):
    """Rows of the branch table: (cells, audit_level, feature_or_None); row 0 is [All]."""
    groups = stats.groups
    lvl, summary = audit_from_counts(stats.total, stats.flagged, stats.ok)
    rows = [(["ALL", "[Tất cả: %d chức năng]" % len(stats.features), len(groups), summary,
              ("%s .. %s" % (format_api_label(groups[0].gid), format_api_label(groups[-1].gid))
               if groups else "-")], lvl, None)]
    for f in stats.features:
        f_groups = stats.groups_of(f.fid)
        f_lvl, f_sum = evaluate_feature_audit(f_groups)
        if not f_groups:
            apis = "(chưa có API)"
        elif len(f_groups) <= 3:
            apis = ", ".join([format_api_label(g.gid) for g in f_groups])
        else:
            apis = "%s .. %s (%d)" % (format_api_label(f_groups[0].gid),
                                      format_api_label(f_groups[-1].gid), len(f_groups))
        rows.append(([("* #%d" % f.fid) if f.fid == active_fid else ("#%d" % f.fid),
                      format_feature_label(f.fid, f.name), len(f_groups), f_sum, apis], f_lvl, f))
    return rows


def compile_api_regex(pattern):
    """Returns (compiled_or_None, error_message_or_None)."""
    if not pattern:
        return None, None
    try:
        return re.compile(pattern), None
    except Exception as e:
        return None, "%s" % e


def _as_bool(v, default=False):
    if isinstance(v, bool):
        return v
    if v is None:
        return default
    if isinstance(v, (int, float)):
        return v != 0
    return ("%s" % v).strip().lower() in ("1", "true", "yes", "on", "y")


def normalize_role(obj, index=0):
    """Accept flexible JSON role shapes and return a canonical role dict."""
    if not isinstance(obj, dict):
        raise ValueError("Role #%d is not a JSON object" % (index + 1))
    name = u_text(obj.get("name") or "").strip() or ("Role_%02d" % (index + 1))
    enabled = _as_bool(obj.get("enabled", True), True)
    raw = obj.get("headers", [])
    if isinstance(raw, dict):
        raw = [{"name": k, "value": raw[k]} for k in raw]
    headers = []
    for h in raw or []:
        if isinstance(h, (basestring, _BYTES_TYPE)):
            h_str = u_text(h)
            if ":" not in h_str:
                continue
            k, v = h_str.split(":", 1)
            h = {"name": k, "value": v}
        if not isinstance(h, dict):
            continue
        hn = sanitize_header_name(u_text(h.get("name")))
        if not hn:
            continue
        hv = h.get("value")
        hv = "" if hv is None else u_text(hv)
        headers.append({"name": hn, "value": sanitize_header_value(hv),
                        "mode": normalize_mode(h.get("mode"), hv)})
    return {"name": name, "enabled": enabled, "headers": headers}


def roles_from_json(text):
    data = json.loads(u_text(text))
    if isinstance(data, dict):
        data = data.get("roles", [])
    if not isinstance(data, list):
        raise ValueError("Expected a JSON list of roles or an object with a 'roles' list")
    return [normalize_role(r, i) for i, r in enumerate(data)]


def roles_to_json(roles):
    return json.dumps({"extension": EXT_NAME, "version": 1, "roles": roles}, indent=2)


def default_role_templates():
    """Return 10 starter role profiles (01_Admin .. 10_Guest) for quick setup."""
    specs = [
        ("01_Admin", [{"name": "Authorization", "value": "Bearer ADMIN_TOKEN", "mode": MODE_REPLACE},
                      {"name": "X-Role", "value": "admin", "mode": MODE_REPLACE}]),
        ("02_Manager", [{"name": "Authorization", "value": "Bearer MANAGER_TOKEN", "mode": MODE_REPLACE},
                        {"name": "X-Role", "value": "manager", "mode": MODE_REPLACE}]),
        ("03_Auditor", [{"name": "Authorization", "value": "Bearer AUDITOR_TOKEN", "mode": MODE_REPLACE}]),
        ("04_Support", [{"name": "JSESSIONID", "value": "SUPPORT_SESSION", "mode": MODE_COOKIE_SET},
                        {"name": "Authorization", "value": REMOVE_TOKEN, "mode": MODE_REMOVE}]),
        ("05_UserA_TenantA", [{"name": "Authorization", "value": "Bearer USER_A_TOKEN", "mode": MODE_REPLACE},
                              {"name": "X-Tenant-ID", "value": "tenant-a", "mode": MODE_REPLACE}]),
        ("06_UserB_TenantA", [{"name": "Authorization", "value": "Bearer USER_B_TOKEN", "mode": MODE_REPLACE},
                              {"name": "X-Tenant-ID", "value": "tenant-a", "mode": MODE_REPLACE}]),
        ("07_UserC_TenantB", [{"name": "Authorization", "value": "Bearer USER_C_TOKEN", "mode": MODE_REPLACE},
                              {"name": "X-Tenant-ID", "value": "tenant-b", "mode": MODE_REPLACE}]),
        ("08_TenantSwap", [{"name": "X-Tenant-ID", "value": "tenant-b", "mode": MODE_REPLACE}]),
        ("09_ExpiredToken", [{"name": "Authorization", "value": "Bearer EXPIRED_TOKEN", "mode": MODE_REPLACE}]),
        ("10_Guest", [{"name": "Authorization", "value": REMOVE_TOKEN, "mode": MODE_REMOVE},
                      {"name": "Cookie", "value": REMOVE_TOKEN, "mode": MODE_REMOVE},
                      {"name": "X-Role", "value": REMOVE_TOKEN, "mode": MODE_REMOVE},
                      {"name": "X-Tenant-ID", "value": REMOVE_TOKEN, "mode": MODE_REMOVE}]),
    ]
    return [normalize_role({"name": n, "enabled": True, "headers": hs}, i)
            for i, (n, hs) in enumerate(specs)]


def groups_to_matrix_json(groups, features=None):
    """Serialize captured Features, API groups and per-role status/length metrics to JSON."""
    items = []
    for g in groups or []:
        g_lvl, g_sum = evaluate_group_audit(g)
        roles_out = []
        for r in g.results:
            r_lvl, r_badge = evaluate_role_result(g, r)
            delta = (r.length - g.orig_length) if (r.length is not None and g.orig_length is not None) else None
            roles_out.append({
                "role": r.role_name,
                "state": r.state,
                "status": r.status,
                "length": r.length,
                "delta_vs_orig": delta,
                "audit_level": r_lvl,
                "audit_note": r_badge,
                "elapsed_ms": r.elapsed_ms,
                "sends": r.sent_count,
                "repeater_tab": r.tab_name,
                "error": r.error or None,
            })
        items.append({
            "api_number": g.gid,
            "api_label": format_api_label(g.gid),
            "group_id": format_group_id(g.gid),
            "feature_id": getattr(g, "fid", 1),
            "feature_name": getattr(g, "feature_name", ""),
            "feature_label": format_feature_label(getattr(g, "fid", 1), getattr(g, "feature_name", "")),
            "audit_level": g_lvl,
            "audit_summary": g_sum,
            "source": g.source,
            "created": g.created,
            "method": g.method,
            "url": g.url,
            "host": g.host,
            "port": g.port,
            "protocol": g.protocol,
            "path": g.path,
            "orig_status": g.orig_status,
            "orig_length": g.orig_length,
            "role_count": len(g.results),
            "roles": roles_out,
        })
    feat_list = []
    if features is not None:
        for f in features:
            f_groups = [g for g in (groups or []) if getattr(g, "fid", 1) == f.fid]
            f_lvl, f_sum = evaluate_feature_audit(f_groups)
            feat_list.append({
                "feature_id": f.fid,
                "name": f.name,
                "label": format_feature_label(f.fid, f.name),
                "created": f.created,
                "api_count": len(f_groups),
                "audit_level": f_lvl,
                "audit_summary": f_sum,
                "apis": [format_api_label(g.gid) for g in f_groups],
            })
    return json.dumps({
        "extension": EXT_NAME,
        "version": 1,
        "feature_count": len(feat_list) if feat_list else len(set([getattr(g, "fid", 1) for g in (groups or [])])),
        "api_count": len(items),
        "features": feat_list,
        "groups": items,
    }, indent=2)


# ----------------------------------------------------------------------------- Excel import (target list)

HTTP_METHODS = ("GET", "POST", "PUT", "PATCH", "DELETE", "HEAD", "OPTIONS", "TRACE", "CONNECT")
ANY_METHOD = "ANY"

# A path parameter is any bracketed token, whatever its name: {id} [id] (id) <id> ${id} {{id}} %id%,
# a whole ":name" segment, or "*".
_PLACEHOLDER_RE = re.compile(r"\{\{[^{}/]*\}\}|\$\{[^{}/]*\}|\{[^{}/]*\}|\[[^\[\]/]*\]|"
                             r"\([^()/]*\)|<[^<>/]*>|%[A-Za-z_][A-Za-z0-9_\-]*%|\*")

_HEADER_ALIASES = {
    "stt": ("stt", "no", "no.", "#", "so thu tu", "so tt", "index", "idx", "order", "id"),
    "method": ("method", "protocol", "phuong thuc", "http method", "verb", "methods", "request method"),
    "path": ("path", "url", "endpoint", "api", "uri", "duong dan", "link", "route", "api path"),
    "position": ("position", "vi tri", "location", "vi tri tim thay", "man hinh", "screen", "feature",
                 "chuc nang", "nhanh", "branch"),
}


def _fold(text):
    """Lower-case, accent-free form used to recognise column headers ('Vị trí' -> 'vi tri')."""
    t = u_text(text).strip().lower().replace(u"đ", u"d")
    try:
        import unicodedata
        t = u"".join([ch for ch in unicodedata.normalize("NFD", t) if unicodedata.category(ch) != "Mn"])
    except Exception:
        pass
    return u" ".join(t.replace(u"_", u" ").split())


_PCT_RE = re.compile(r"%([0-9A-Fa-f]{2})")
_ID_SEG_RE = re.compile(r"^(?:[0-9]+|[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}"
                        r"|[0-9a-fA-F]{16,})$")


def _pct_decode(text):
    """Decode %XX escapes except %2F (an encoded '/' must not split a path segment)."""
    def sub(m):
        code = int(m.group(1), 16)
        if code == 0x2F or code < 0x20:
            return "%" + m.group(1).upper()
        return unichr(code) if code < 0x80 else m.group(0)
    return _PCT_RE.sub(sub, text)


try:
    unichr
except NameError:  # CPython 3 (offline tests)
    unichr = chr


def normalize_request_path(raw):
    """
    Canonical path used on BOTH sides of the Excel comparison:
    'https://h/a/b;jsessionid=1/?q#f' -> '/a/b'. Host, query and fragment dropped, %XX decoded
    (except %2F), ';matrix' parameters removed from each segment, '//' collapsed, trailing '/'
    removed. Placeholders such as {id} are left untouched.
    """
    p = u_text(raw).strip()
    low = p.lower()
    if low.startswith("http://") or low.startswith("https://"):
        idx = p.find("/", p.find("://") + 3)
        p = p[idx:] if idx >= 0 else "/"
    for sep in ("?", "#"):
        p = p.split(sep, 1)[0]
    p = _pct_decode(p.strip())
    segs = []
    for seg in p.split("/"):
        if ";" in seg:
            seg = seg.split(";", 1)[0]
        if seg:
            segs.append(seg)
    return "/" + "/".join(segs)


# Backwards-compatible name (older callers / tests)
normalize_target_path = normalize_request_path


def split_host_and_query(raw):
    """(host or None, [(name, value_or_None)]) declared by an Excel PATH cell."""
    text = u_text(raw).strip()
    host = None
    low = text.lower()
    if low.startswith("http://") or low.startswith("https://"):
        rest = text[text.find("://") + 3:]
        host = rest.split("/", 1)[0].split("?", 1)[0].split("@")[-1].split(":", 1)[0].lower() or None
    query = []
    if "?" in text:
        qs = text.split("?", 1)[1].split("#", 1)[0]
        for part in qs.split("&"):
            if not part:
                continue
            name, _, value = part.partition("=")
            name = _pct_decode(name).strip()
            if name:
                query.append((name, _pct_decode(value) if "=" in part else None))
    return host, query


def parse_query(path):
    """{name: [values]} of a request path's query string."""
    out = {}
    if "?" not in (path or ""):
        return out
    qs = path.split("?", 1)[1].split("#", 1)[0]
    for part in qs.split("&"):
        if not part:
            continue
        name, _, value = part.partition("=")
        out.setdefault(_pct_decode(name), []).append(_pct_decode(value))
    return out


def _segment_regex(seg, ids_as_params):
    """(regex, is_literal) of one documented path segment."""
    if seg.startswith(":") and len(seg) > 1:
        return u"[^/]+", False
    if ids_as_params and _ID_SEG_RE.match(seg):
        return u"[^/]+", False
    out = []
    pos = 0
    has_param = False
    for m in _PLACEHOLDER_RE.finditer(seg):
        out.append(re.escape(seg[pos:m.start()]))
        out.append(u"[^/]*" if m.group(0) == u"*" else u"[^/]+")
        pos = m.end()
        has_param = True
    out.append(re.escape(seg[pos:]))
    return u"".join(out), not has_param


def compile_path_template(raw_path, ids_as_params=False):
    """
    (exact_regex, prefixed_regex, literal_segments) for a documented path. Placeholders match one
    segment. `prefixed_regex` also accepts extra leading segments (an unknown base path like /api/v1).
    With `ids_as_params`, purely numeric / UUID / long-hex segments in the file are parameters too.
    """
    path = normalize_request_path(raw_path)
    parts = []
    literal = 0
    for seg in [x for x in path.split("/") if x]:
        rx, is_literal = _segment_regex(seg, ids_as_params)
        parts.append(rx)
        literal += 1 if is_literal else 0
    body = u"/" + u"/".join(parts) if parts else u""
    exact = re.compile(u"^" + (body or u"") + u"/?$", re.IGNORECASE)
    prefixed = re.compile(u"^(?:/[^/]+)*" + (body or u"") + u"/?$", re.IGNORECASE)
    return exact, prefixed, literal


def parse_methods(raw):
    """'GET' / 'get, post' / 'GET/POST' / '' / 'ANY' -> ['GET'] / ['GET','POST'] / ['ANY']"""
    words = [w.strip().upper() for w in re.split(r"[\s,;/|]+", u_text(raw)) if w.strip()]
    methods = [w for w in words if w in HTTP_METHODS]
    return methods or [ANY_METHOD]


class TargetEntry(object):
    def __init__(self, stt, methods, path, position, row_no):
        self.stt = stt
        self.methods = list(methods)
        self.path = u_text(path)
        self.position = u_text(position or "").strip()
        self.row_no = row_no
        self.host, self.query = split_host_and_query(self.path)
        self.norm = normalize_request_path(self.path)
        self.segments = [x for x in self.norm.split("/") if x]
        # both variants are compiled once, the 'ids as parameters' option just picks one
        self._rx = {False: compile_path_template(self.path, False), True: compile_path_template(self.path, True)}
        self.exact, self.prefixed, self.literal = self._rx[False]

    def patterns(self, ids_as_params):
        return self._rx[bool(ids_as_params)]

    def method_label(self):
        return ", ".join(self.methods)

    def query_ok(self, params, mode="values"):
        for name, value in self.query:
            got = params.get(name)
            if got is None:
                return False
            if mode == "names" or value is None or _PLACEHOLDER_RE.search(value):
                continue
            if value not in got:
                return False
        return True

    def to_dict(self):
        return {"stt": self.stt, "methods": self.methods, "path": self.path,
                "position": self.position, "row": self.row_no}


def _bare_host(host):
    h = u_text(host or "").lower().strip()
    if h.startswith("[") and "]" in h:
        return h[:h.index("]") + 1]
    return h.split(":", 1)[0]


class TargetList(object):
    """API list from the user's Excel file; answers 'which row does METHOD /path belong to?'."""

    def __init__(self, entries, source="", sheet="", headers=None):
        self.entries = list(entries)
        self.source = u_text(source)
        self.sheet = u_text(sheet)
        self.headers = list(headers or ["STT", "PROTOCOL", "PATH", "POSITION"])
        self._by_method = {}
        for e in self.entries:
            for m in e.methods:
                self._by_method.setdefault(m, []).append(e)

    def __len__(self):
        return len(self.entries)

    def match(self, method, path, allow_prefix=False, host=None, ids_as_params=False, query_mode="ignore"):
        """
        Best row for this request. A row only matches if its host (full URL in the file) agrees and,
        with query_mode 'names' / 'values', if the request carries the row's query parameters
        (e.g. ?action=getUser). Ranking: exact before prefixed, then rows naming this host, rows
        with more query constraints, more literal segments, earlier rows.
        """
        p = normalize_request_path(path)
        params = parse_query(path) if "?" in (path or "") else {}
        req_host = _bare_host(host) if host else None
        candidates = self._by_method.get((method or "").upper(), []) + self._by_method.get(ANY_METHOD, [])
        best = None
        best_key = None
        for e in candidates:
            if e.host and req_host and e.host != req_host:
                continue
            exact, prefixed, literal = e.patterns(ids_as_params)
            if exact.match(p):
                kind = 2
            elif allow_prefix and prefixed.match(p):
                kind = 1
            else:
                continue
            use_query = query_mode in ("names", "values") and e.query
            if use_query and not e.query_ok(params, query_mode):
                continue
            key = (kind, 1 if (e.host and req_host) else 0, len(e.query) if use_query else 0, literal, -e.row_no)
            if best_key is None or key > best_key:
                best, best_key = e, key
        return best

    def duplicates(self):
        """Rows declaring the same method(s) + path as an earlier row."""
        seen = {}
        dup = []
        for e in self.entries:
            key = (tuple(sorted(e.methods)), e.norm.lower(), tuple(e.query), e.host)
            if key in seen:
                dup.append((e, seen[key]))
            else:
                seen[key] = e
        return dup

    def to_json(self):
        return json.dumps({"source": self.source, "sheet": self.sheet, "headers": self.headers,
                           "entries": [e.to_dict() for e in self.entries]})

    @staticmethod
    def from_json(text):
        data = json.loads(text)
        entries = [TargetEntry(d.get("stt"), d.get("methods") or [ANY_METHOD], d.get("path", "/"),
                               d.get("position", ""), d.get("row", i + 1))
                   for i, d in enumerate(data.get("entries", []))]
        return TargetList(entries, data.get("source", ""), data.get("sheet", ""), data.get("headers"))


HIT_NEW, HIT_DUP, HIT_FILTERED = "new", "dup", "filtered"
HIT_LABELS = {HIT_NEW: u"Bắt mới", HIT_DUP: u"Gặp lại (đã bắt)", HIT_FILTERED: u"Bị lọc"}


def targets_signature(targets):
    if not targets:
        return None
    return u"%s|%s|%d" % (targets.source, targets.sheet, len(targets))


class TargetHitLog(object):
    """
    Every time a request matching a row of the Excel list goes through the proxy: when, which real
    path, which branch you were on, and whether it was captured, already captured (duplicate) or
    filtered. Counted per Excel row; the last MAX_EVENTS events of each row are kept.
    """
    MAX_EVENTS = 300

    def __init__(self):
        self._lock = threading.Lock()
        self.signature = None
        self._rows = {}
        self.dirty = False

    def reset(self, signature=None):
        with self._lock:
            self.signature = signature
            self._rows = {}
            self.dirty = True

    def record(self, entry, event):
        with self._lock:
            rec = self._rows.get(entry.row_no)
            if rec is None:
                rec = {"count": 0, "new": 0, "dup": 0, "filtered": 0, "events": []}
                self._rows[entry.row_no] = rec
            rec["count"] += 1
            kind = event.get("result", HIT_NEW)
            rec[kind] = rec.get(kind, 0) + 1
            ev = dict(event)
            ev["n"] = rec["count"]
            rec["events"].append(ev)
            if len(rec["events"]) > self.MAX_EVENTS:
                del rec["events"][0]
            self.dirty = True
            return rec["count"]

    def count(self, entry):
        rec = self._rows.get(getattr(entry, "row_no", None))
        return rec["count"] if rec else 0

    def stats(self, entry):
        """(count, new, dup, filtered)"""
        rec = self._rows.get(getattr(entry, "row_no", None))
        if not rec:
            return 0, 0, 0, 0
        return rec["count"], rec.get("new", 0), rec.get("dup", 0), rec.get("filtered", 0)

    def events(self, entry):
        with self._lock:
            rec = self._rows.get(getattr(entry, "row_no", None))
            return [dict(e) for e in rec["events"]] if rec else []

    def positions(self, entry):
        """Branches the row was met on, most recent first, each once."""
        out = []
        for ev in reversed(self.events(entry)):
            b = ev.get("branch") or u""
            if b and b not in out:
                out.append(b)
        return out

    def total(self):
        return sum([r["count"] for r in self._rows.values()])

    def rows_seen(self):
        return len([1 for r in self._rows.values() if r["count"]])

    def to_json(self):
        with self._lock:
            self.dirty = False
            return json.dumps({"signature": self.signature,
                               "rows": dict([(u_text(k), v) for k, v in self._rows.items()])})

    def load_json(self, raw, signature):
        try:
            data = json.loads(raw) if raw else {}
        except Exception:
            data = {}
        with self._lock:
            self.signature = signature
            self._rows = {}
            if data.get("signature") == signature and signature is not None:
                for k, v in (data.get("rows") or {}).items():
                    try:
                        self._rows[int(k)] = v
                    except (ValueError, TypeError):
                        pass
            self.dirty = False


def hit_cell(hits, entry):
    """'5 lần (1 mới · 4 gặp lại)' for the coverage table."""
    if hits is None:
        return u""
    n, new, dup, filtered = hits.stats(entry)
    if not n:
        return u"0"
    parts = []
    if new:
        parts.append(u"%d mới" % new)
    if dup:
        parts.append(u"%d gặp lại" % dup)
    if filtered:
        parts.append(u"%d bị lọc" % filtered)
    return u"%d lần (%s)" % (n, u" · ".join(parts))


class NearMissIndex(object):
    """
    For Excel rows nobody captured: the closest captured API, to catch typos, version drift
    (/v1 vs /v2) and a missing base path. Indexed by segment count so it stays cheap.
    """

    def __init__(self, groups):
        self._by_len = {}
        self._by_last = {}
        for g in groups:
            segs = [x for x in normalize_request_path(g.path).split("/") if x]
            item = (g, [x.lower() for x in segs])
            self._by_len.setdefault(len(segs), []).append(item)
            if segs:
                self._by_last.setdefault(segs[-1].lower(), []).append(item)

    @staticmethod
    def _method_ok(entry, g):
        return ANY_METHOD in entry.methods or g.method.upper() in entry.methods

    def suggest(self, entry):
        """(group, note) or (None, '')."""
        want = entry.segments
        n = len(want)
        best = None
        for g, segs in self._by_len.get(n, []):
            if not self._method_ok(entry, g):
                continue
            diffs = []
            for a, b in zip(want, segs):
                rx, is_literal = _segment_regex(a, True)
                if is_literal and a.lower() != b:
                    diffs.append((a, b))
                    if len(diffs) > 1:
                        break
            if len(diffs) == 1 and (best is None or g.gid < best[0].gid):
                best = (g, u"khác 1 đoạn: %s → %s" % diffs[0])
        if best is not None or not want:
            return best or (None, u"")
        exact, prefixed, _ = entry.patterns(True)
        for g, segs in self._by_last.get(want[-1].lower(), []):
            if len(segs) > n and self._method_ok(entry, g) and prefixed.match("/" + "/".join(segs)):
                extra = "/" + "/".join(segs[:len(segs) - n])
                return g, u"có thêm tiền tố %s (bật 'cho phép tiền tố')" % extra
        return None, u""


_XLSX_MAX_PART = 40 * 1024 * 1024
_ON_JYTHON = sys.platform.startswith("java")


def _xml_local(tag):
    return tag.rsplit("}", 1)[-1]


class _El(object):
    """Tiny read-only element (tag / attrib / text / children) shared by both XML back-ends."""

    def __init__(self, tag, attrib, text):
        self.tag = tag
        self.attrib = attrib
        self.text = text
        self.children = []

    def get(self, key, default=None):
        return self.attrib.get(key, default)

    def __iter__(self):
        return iter(self.children)

    def iter(self):
        stack = [self]
        while stack:
            el = stack.pop()
            yield el
            stack.extend(reversed(el.children))


def _from_etree(node):
    el = _El(node.tag, dict(node.attrib), node.text)
    el.children = [_from_etree(c) for c in node]
    return el


def _from_dom(node):
    from org.w3c.dom import Node
    ns = node.getNamespaceURI()
    local = node.getLocalName() or node.getNodeName()
    attrib = {}
    attrs = node.getAttributes()
    for i in range(attrs.getLength()):
        a = attrs.item(i)
        a_ns = a.getNamespaceURI()
        if a_ns == "http://www.w3.org/2000/xmlns/":
            continue
        a_local = a.getLocalName() or a.getNodeName()
        attrib[(u"{%s}%s" % (a_ns, a_local)) if a_ns else a_local] = a.getValue()
    texts = []
    el = _El((u"{%s}%s" % (ns, local)) if ns else local, attrib, None)
    child = node.getFirstChild()
    while child is not None:
        kind = child.getNodeType()
        if kind == Node.ELEMENT_NODE:
            el.children.append(_from_dom(child))
        elif kind in (Node.TEXT_NODE, Node.CDATA_SECTION_NODE):
            texts.append(child.getNodeValue())
        child = child.getNextSibling()
    el.text = u"".join(texts) if texts else None
    return el


def _jdk_dom_factory():
    """The JDK's own DOM parser: Jython's bundled Xerces is not reachable from Burp's class loader."""
    from javax.xml.parsers import DocumentBuilderFactory
    try:
        factory = DocumentBuilderFactory.newDefaultInstance()
    except AttributeError:  # JDK < 13
        factory = DocumentBuilderFactory.newInstance()
    factory.setNamespaceAware(True)
    # Spreadsheet parts never declare a DTD; refusing them rules out entity-expansion tricks.
    factory.setFeature("http://apache.org/xml/features/disallow-doctype-decl", True)
    factory.setXIncludeAware(False)
    factory.setExpandEntityReferences(False)
    return factory


class _XlsxArchive(object):
    """Reads the parts of an .xlsx: JDK zip + DOM under Jython (Burp), stdlib under CPython (tests)."""

    def __init__(self, path):
        if _ON_JYTHON:
            from java.util.zip import ZipFile as JavaZip
            self._z = JavaZip(File(path))
            self._names = set([e.getName() for e in list(self._z.entries())])
            self._factory = _jdk_dom_factory()
        else:
            import zipfile
            self._z = zipfile.ZipFile(path)
            self._names = set(self._z.namelist())

    def names(self):
        return self._names

    def root(self, name):
        if name not in self._names:
            raise ValueError("Missing part %s - is this really an .xlsx file?" % name)
        if _ON_JYTHON:
            entry = self._z.getEntry(name)
            if entry.getSize() > _XLSX_MAX_PART:
                raise ValueError("Excel part %s is too large" % name)
            stream = self._z.getInputStream(entry)
            try:
                return _from_dom(self._factory.newDocumentBuilder().parse(stream).getDocumentElement())
            finally:
                stream.close()
        info = self._z.getinfo(name)
        if info.file_size > _XLSX_MAX_PART:
            raise ValueError("Excel part %s is too large" % name)
        data = self._z.read(name)
        if b"<!doctype" in data[:4096].lower() or b"<!entity" in data.lower():
            raise ValueError("Unsupported XML in %s" % name)
        import xml.etree.ElementTree as ET
        return _from_etree(ET.fromstring(data))

    def close(self):
        self._z.close()


def _xlsx_col_index(ref):
    n = 0
    for ch in ref:
        if "A" <= ch <= "Z":
            n = n * 26 + (ord(ch) - 64)
        elif "a" <= ch <= "z":
            n = n * 26 + (ord(ch) - 96)
        else:
            break
    return n - 1


def read_xlsx_rows(path, sheet_index=0):
    """(sheet_name, rows) of one worksheet; each row is a list of cell values (None for blanks)."""
    z = _XlsxArchive(path)
    try:
        names = z.names()
        wb = z.root("xl/workbook.xml")
        sheets = [el for el in wb.iter() if _xml_local(el.tag) == "sheet"]
        if not sheets:
            raise ValueError("The workbook has no worksheet")
        sheet_el = sheets[min(sheet_index, len(sheets) - 1)]
        sheet_name = sheet_el.get("name", "Sheet1")
        rel_id = None
        for k, v in sheet_el.attrib.items():
            if k.startswith("{") and _xml_local(k) == "id":
                rel_id = v
        target = "worksheets/sheet%d.xml" % (sheet_index + 1)
        if rel_id and "xl/_rels/workbook.xml.rels" in names:
            for rel in z.root("xl/_rels/workbook.xml.rels").iter():
                if _xml_local(rel.tag) == "Relationship" and rel.get("Id") == rel_id:
                    target = rel.get("Target")
        part = target.lstrip("/") if target.startswith("/") else "xl/" + target
        shared = []
        if "xl/sharedStrings.xml" in names:
            for si in z.root("xl/sharedStrings.xml"):
                if _xml_local(si.tag) == "si":
                    shared.append(u"".join([t.text or u"" for t in si.iter() if _xml_local(t.tag) == "t"]))
        rows = []
        for row_el in z.root(part).iter():
            if _xml_local(row_el.tag) != "row":
                continue
            cells = {}
            seq = 0
            for c in row_el:
                if _xml_local(c.tag) != "c":
                    continue
                ref = c.get("r")
                col = _xlsx_col_index(ref) if ref else seq
                seq = col + 1
                kind = c.get("t")
                v = None
                for child in c:
                    if _xml_local(child.tag) == "v":
                        v = child.text
                if kind == "s":
                    value = shared[int(v)] if v is not None and int(v) < len(shared) else None
                elif kind == "inlineStr":
                    value = u"".join([t.text or u"" for t in c.iter() if _xml_local(t.tag) == "t"])
                elif kind == "b":
                    value = (v == "1")
                elif kind in ("str", "e"):
                    value = v
                elif v is None:
                    value = None
                else:
                    try:
                        f = float(v)
                        value = int(f) if f == int(f) else f
                    except ValueError:
                        value = v
                cells[col] = value
            if cells:
                width = max(cells.keys()) + 1
                rows.append([cells.get(i) for i in range(width)])
            else:
                rows.append([])
        return sheet_name, rows
    finally:
        z.close()


def xlsx_sheet_names(path):
    z = _XlsxArchive(path)
    try:
        wb = z.root("xl/workbook.xml")
        return [el.get("name", "Sheet") for el in wb.iter() if _xml_local(el.tag) == "sheet"]
    finally:
        z.close()


def detect_target_columns(rows):
    """(header_row_index or -1, {field: column}, header_texts) from the first rows of the sheet."""
    for r_idx, row in enumerate(rows[:15]):
        cols = {}
        for c_idx, value in enumerate(row):
            if value is None:
                continue
            folded = _fold(value)
            for field, aliases in _HEADER_ALIASES.items():
                if field not in cols and folded in aliases:
                    cols[field] = c_idx
        if "path" in cols:
            headers = [u_text(v) if v is not None else u"" for v in row]
            return r_idx, cols, headers
    # No header row: the documented layout STT | METHOD | PATH | POSITION
    return -1, {"stt": 0, "method": 1, "path": 2, "position": 3}, ["STT", "PROTOCOL", "PATH", "POSITION"]


def build_target_list(rows, source="", sheet=""):
    header_idx, cols, header_texts = detect_target_columns(rows)
    entries = []
    for r_idx in range(header_idx + 1, len(rows)):
        row = rows[r_idx]

        def cell(field):
            c = cols.get(field)
            return row[c] if c is not None and c < len(row) else None
        raw_path = cell("path")
        if raw_path is None or not u_text(raw_path).strip():
            continue
        text_path = u_text(raw_path).strip()
        if "/" not in text_path and not text_path.lower().startswith("http"):
            continue
        stt = cell("stt")
        if stt is None or u_text(stt).strip() == "":
            stt = len(entries) + 1
        entries.append(TargetEntry(stt, parse_methods(cell("method") or ""), text_path,
                                   cell("position"), r_idx + 1))
    def header_for(field, default):
        c = cols.get(field)
        if header_idx >= 0 and c is not None and c < len(header_texts) and header_texts[c]:
            return header_texts[c]
        return default
    headers = [header_for("stt", "STT"), header_for("method", "PROTOCOL"),
               header_for("path", "PATH"), header_for("position", "POSITION")]
    return TargetList(entries, source, sheet, headers)


def coverage_rows(targets, groups):
    """Per Excel row: (entry, [matched groups])."""
    by_entry = {}
    for g in groups or []:
        e = getattr(g, "target", None)
        if e is not None:
            by_entry.setdefault(id(e), []).append(g)
    return [(e, by_entry.get(id(e), [])) for e in (targets.entries if targets else [])]


# ----------------------------------------------------------------------------- Excel export

EXPORT_API_HEADER = ["STT", "Method", "Path", "Vị trí tìm thấy", "Host", "URL đầy đủ",
                     "Status gốc", "Đánh giá", "Đã gửi", "Nguồn", "Thời gian", "STT trong file Excel",
                     "Path để copy", "Đã copy"]
EXPORT_API_WIDTHS = [6, 9, 48, 44, 26, 70, 11, 40, 9, 9, 10, 12, 50, 9]
EXPORT_ROLE_HEADER = ["STT", "API #", "Method", "Path", "Vị trí tìm thấy", "Role", "Trạng thái",
                      "Status", "Body Len", "Lệch so với gốc", "Thời gian (ms)", "Đánh giá"]
EXPORT_ROLE_WIDTHS = [6, 7, 9, 44, 40, 22, 12, 8, 10, 14, 14, 40]


def api_export_rows(groups, label_fn=None):
    """(api_rows, role_rows) for the Excel export, ordered by API number."""
    api_rows = []
    role_rows = []
    for idx, g in enumerate(sorted(groups or [], key=lambda x: x.gid), 1):
        _, g_sum = evaluate_group_audit(g)
        done = len([r for r in g.results if r.state in (STATE_DONE, STATE_ERROR)])
        api_rows.append([idx, g.method, strip_query(g.path), g.feature_name, g.host, g.url,
                         g.orig_status, g_sum, "%d/%d" % (done, len(g.results)), g.source, g.created,
                         g.target.stt if getattr(g, "target", None) is not None else None,
                         label_fn(g) if label_fn else None,
                         u"Có" if getattr(g, "copied_label", None) else None])
        for r in g.results:
            _, badge = evaluate_role_result(g, r)
            delta = (r.length - g.orig_length) if (r.length is not None and g.orig_length is not None) else None
            role_rows.append([len(role_rows) + 1, g.gid, g.method, strip_query(g.path), g.feature_name,
                              r.role_name, r.state, r.status, r.length, delta, r.elapsed_ms, badge])
    return api_rows, role_rows


_XML_BAD = re.compile(u"[\x00-\x08\x0b\x0c\x0e-\x1f\ufffe\uffff]")


def _xml_escape(value):
    text = _XML_BAD.sub(u"", u_text(value))
    return (text.replace(u"&", u"&amp;").replace(u"<", u"&lt;")
            .replace(u">", u"&gt;").replace(u'"', u"&quot;"))


def _xlsx_col(index):
    name = ""
    index += 1
    while index:
        index, rem = divmod(index - 1, 26)
        name = chr(65 + rem) + name
    return name


def _xlsx_sheet(header, rows, widths):
    last_col = _xlsx_col(len(header) - 1)
    out = [u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
           u'<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
           u'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">',
           u'<sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" '
           u'activePane="bottomLeft" state="frozen"/></sheetView></sheetViews>',
           u'<sheetFormatPr defaultRowHeight="15"/><cols>']
    for i, w in enumerate(widths):
        out.append(u'<col min="%d" max="%d" width="%d" customWidth="1"/>' % (i + 1, i + 1, w))
    out.append(u'</cols><sheetData>')
    for r_idx, row in enumerate([header] + list(rows)):
        style = u' s="1"' if r_idx == 0 else u''
        cells = []
        for c_idx, value in enumerate(row):
            if value is None:
                continue
            ref = u"%s%d" % (_xlsx_col(c_idx), r_idx + 1)
            if isinstance(value, (int, float)) and not isinstance(value, bool) and r_idx > 0:
                cells.append(u'<c r="%s"%s><v>%s</v></c>' % (ref, style, value))
            else:
                cells.append(u'<c r="%s" t="inlineStr"%s><is><t xml:space="preserve">%s</t></is></c>'
                             % (ref, style, _xml_escape(value)))
        out.append(u'<row r="%d">%s</row>' % (r_idx + 1, u"".join(cells)))
    out.append(u'</sheetData><autoFilter ref="A1:%s%d"/></worksheet>' % (last_col, len(rows) + 1))
    return u"".join(out)


def build_xlsx(sheets):
    """
    Minimal but valid .xlsx (Office Open XML) from [(name, header, rows, widths), ...].
    Bold coloured header row, frozen + auto-filtered. Standard library only (zipfile).
    """
    import zipfile
    from io import BytesIO
    ns_main = u"http://schemas.openxmlformats.org/spreadsheetml/2006/main"
    ns_rel = u"http://schemas.openxmlformats.org/officeDocument/2006/relationships"
    ns_pkg = u"http://schemas.openxmlformats.org/package/2006/relationships"
    buf = BytesIO()
    z = zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED)

    def put(name, text):
        z.writestr(name, text.encode("utf-8"))

    overrides = [u'<Override PartName="/xl/workbook.xml" ContentType="application/'
                 u'vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>',
                 u'<Override PartName="/xl/styles.xml" ContentType="application/'
                 u'vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>']
    sheet_tags = []
    rels = []
    names = []
    for i, (name, header, rows, widths) in enumerate(sheets, 1):
        put(u"xl/worksheets/sheet%d.xml" % i, _xlsx_sheet(header, rows, widths))
        overrides.append(u'<Override PartName="/xl/worksheets/sheet%d.xml" ContentType="application/'
                         u'vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>' % i)
        sheet_tags.append(u'<sheet name="%s" sheetId="%d" r:id="rId%d"/>' % (_xml_escape(name[:31]), i, i))
        rels.append(u'<Relationship Id="rId%d" Type="%s/worksheet" Target="worksheets/sheet%d.xml"/>'
                    % (i, ns_rel, i))
        names.append(u'<definedName name="_xlnm._FilterDatabase" localSheetId="%d" hidden="1">'
                     u"&apos;%s&apos;!$A$1:$%s$%d</definedName>"
                     % (i - 1, _xml_escape(name[:31]), _xlsx_col(len(header) - 1), len(rows) + 1))
    rels.append(u'<Relationship Id="rId%d" Type="%s/styles" Target="styles.xml"/>' % (len(sheets) + 1, ns_rel))
    put(u"[Content_Types].xml",
        u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
        u'<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
        u'<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
        u'<Default Extension="xml" ContentType="application/xml"/>' + u"".join(overrides) + u'</Types>')
    put(u"_rels/.rels",
        u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="%s">'
        u'<Relationship Id="rId1" Type="%s/officeDocument" Target="xl/workbook.xml"/></Relationships>'
        % (ns_pkg, ns_rel))
    put(u"xl/workbook.xml",
        u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="%s" xmlns:r="%s">'
        u'<sheets>%s</sheets><definedNames>%s</definedNames></workbook>'
        % (ns_main, ns_rel, u"".join(sheet_tags), u"".join(names)))
    put(u"xl/_rels/workbook.xml.rels",
        u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="%s">%s</Relationships>'
        % (ns_pkg, u"".join(rels)))
    put(u"xl/styles.xml",
        u'<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="%s">'
        u'<fonts count="2"><font><sz val="11"/><name val="Calibri"/></font>'
        u'<font><b/><sz val="11"/><color rgb="FFFFFFFF"/><name val="Calibri"/></font></fonts>'
        u'<fills count="3"><fill><patternFill patternType="none"/></fill>'
        u'<fill><patternFill patternType="gray125"/></fill>'
        u'<fill><patternFill patternType="solid"><fgColor rgb="FF2563EB"/><bgColor indexed="64"/>'
        u'</patternFill></fill></fills>'
        u'<borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders>'
        u'<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>'
        u'<cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/>'
        u'<xf numFmtId="0" fontId="1" fillId="2" borderId="0" xfId="0" applyFont="1" applyFill="1"/>'
        u'</cellXfs><cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles>'
        u'</styleSheet>' % ns_main)
    z.close()
    return buf.getvalue()


COVERAGE_EXTRA_HEADER = ["Trạng thái", "Số lần bắt", "API #", "Path thực tế", "Vị trí tìm thấy", "Đánh giá",
                         "Path để copy", "Đã copy", "Gợi ý gần đúng (dòng chưa bắt)", "Lượt gặp",
                         "Các vị trí đã gặp"]
COVERAGE_WIDTHS = [6, 12, 48, 44, 12, 11, 10, 48, 44, 40, 50, 9, 60, 26, 60]
HITS_HEADER = ["STT (file)", "Method (file)", "Path (trong file)", "Lần", "Thời gian", "Kết quả", "API #",
               "Method", "Path thực tế", "Host", "Vị trí đang đứng", "Lưu vào nhánh", "Nguồn", "Ghi chú"]
HITS_WIDTHS = [8, 10, 44, 6, 17, 16, 8, 9, 48, 24, 44, 44, 9, 30]


def hits_export_rows(targets, hits):
    rows = []
    if not targets or hits is None:
        return rows
    for e in targets.entries:
        for ev in hits.events(e):
            rows.append([e.stt, e.method_label(), e.path, ev.get("n"), ev.get("time"),
                         HIT_LABELS.get(ev.get("result"), ev.get("result")),
                         format_api_label(ev["gid"]) if ev.get("gid") else None, ev.get("method"), ev.get("path"),
                         ev.get("host"), ev.get("branch"), ev.get("filed"), ev.get("source"), ev.get("note") or None])
    return rows
OUTSIDE_HEADER = ["STT", "API #", "Method", "Path", "Vị trí tìm thấy", "Host", "Status gốc", "Path để copy"]
OUTSIDE_WIDTHS = [6, 8, 9, 48, 44, 26, 11, 50]


def coverage_export_rows(targets, groups, copy_format=None, position_as_copy=False, hits=None):
    """
    Rows mirroring the user's file (STT, method, path, position) + what was found for each row.
    POSITION keeps what the user wrote; when empty it is filled with where the API was found,
    as 'STT. path' (copy format) when `position_as_copy` is on.
    """
    out = []
    near = NearMissIndex(groups or [])
    for e, found in coverage_rows(targets, groups):
        found = sorted(found, key=lambda g: g.gid)
        first = found[0] if found else None
        found_positions = []
        for g in found:
            if g.feature_name not in found_positions:
                found_positions.append(g.feature_name)
        copy_line = format_copy_line(copy_format, e.stt, found_positions[0]) if found_positions else None
        if e.position:
            position = e.position
        elif position_as_copy and copy_line:
            position = copy_line
        else:
            position = u"; ".join(found_positions) or None
        hint = u""
        if not found:
            g, note = near.suggest(e)
            if g is not None:
                hint = u"%s %s %s (%s)" % (format_api_label(g.gid), g.method, strip_query(g.path), note)
        out.append([e.stt, e.method_label(), e.path, position,
                    u"Đã bắt" if found else u"Chưa bắt", len(found),
                    u", ".join([format_api_label(g.gid) for g in found]) or None,
                    strip_query(first.path) if first else None,
                    u"; ".join(found_positions) or None,
                    (getattr(first, "_audit_summary", None) or evaluate_group_audit(first)[1]) if first else None,
                    copy_line, u"Có" if any([getattr(g, "copied_label", None) for g in found]) else None,
                    hint or None, hit_cell(hits, e) or None,
                    u"; ".join(hits.positions(e)) if hits is not None else None])
    return out


def outside_list_rows(groups, label_fn=None):
    """Captured APIs that match no row of the Excel file (possible out-of-scope / undocumented)."""
    rows = []
    for g in sorted(groups or [], key=lambda x: x.gid):
        if getattr(g, "target", None) is None:
            rows.append([len(rows) + 1, g.gid, g.method, strip_query(g.path), g.feature_name, g.host,
                         g.orig_status, label_fn(g) if label_fn else None])
    return rows


def build_api_workbook(groups, targets=None, copy_format=None, position_as_copy=False, label_fn=None, hits=None):
    api_rows, role_rows = api_export_rows(groups, label_fn)
    sheets = []
    if targets is not None and len(targets):
        sheets.append((u"Độ phủ", list(targets.headers) + COVERAGE_EXTRA_HEADER,
                       coverage_export_rows(targets, groups, copy_format, position_as_copy, hits), COVERAGE_WIDTHS))
        if hits is not None:
            sheets.append((u"Nhật ký lượt gặp", HITS_HEADER, hits_export_rows(targets, hits), HITS_WIDTHS))
        sheets.append((u"API ngoài danh sách", OUTSIDE_HEADER, outside_list_rows(groups, label_fn), OUTSIDE_WIDTHS))
    sheets.append((u"API", EXPORT_API_HEADER, api_rows, EXPORT_API_WIDTHS))
    sheets.append((u"Kết quả Role", EXPORT_ROLE_HEADER, role_rows, EXPORT_ROLE_WIDTHS))
    return build_xlsx(sheets)


def build_history_summary_text(features, groups):
    """
    Build a structured audit report grouping sequential APIs (API 1, API 2, ...)
    under their user-named Features (Tên 1, Tên 2, ...).
    """
    features = list(features or [])
    groups = list(groups or [])
    lines = []
    lines.append("======================================================================")
    lines.append("%s - BÁO CÁO LỊCH SỬ CHỨC NĂNG & API (AUDIT HISTORY)" % EXT_NAME)
    lines.append("Tổng số chức năng (Features): %d   |   Tổng số API đã đi qua: %d" % (len(features), len(groups)))
    lines.append("======================================================================")
    if not features and not groups:
        lines.append("\nChưa có API nào được ghi nhận.")
        return "\n".join(lines)
    by_fid = {}
    for g in groups:
        fid = getattr(g, "fid", 1)
        by_fid.setdefault(fid, []).append(g)
    seen_fids = set()
    for f in features:
        seen_fids.add(f.fid)
        f_groups = by_fid.get(f.fid, [])
        api_range = ("%s .. %s" % (format_api_label(f_groups[0].gid), format_api_label(f_groups[-1].gid))
                     if f_groups else "chưa có API")
        _, f_audit = evaluate_feature_audit(f_groups)
        lines.append("")
        lines.append("[*] %s  (Số lượng API: %d | %s | Đánh giá: %s | Lúc: %s)" %
                     (format_feature_label(f.fid, f.name), len(f_groups), api_range, f_audit, f.created))
        lines.append("-" * 70)
        if not f_groups:
            lines.append("   (Chưa có API nào trong chức năng này)")
            continue
        for idx, g in enumerate(f_groups, 1):
            _, g_audit = evaluate_group_audit(g)
            orig_info = "Orig Status=%s, Orig Len=%s" % (
                g.orig_status if g.orig_status is not None else "-",
                g.orig_length if g.orig_length is not None else "-")
            lines.append("   %d. %s [%s]  %s %s://%s:%s%s  (%s | %d roles)  --> [%s]" % (
                idx, format_api_label(g.gid), format_group_id(g.gid),
                g.method, g.protocol, g.host, g.port, g.path, orig_info, len(g.results), g_audit))
            replayed = [r for r in g.results if r.status is not None or r.state == STATE_ERROR]
            if replayed:
                status_summary = ", ".join([
                    "%s:%s(len=%s)" % (r.role_name, r.status if r.status is not None else "ERR", r.length)
                    for r in replayed
                ])
                lines.append("      -> Kết quả Replay: %s" % status_summary)
    for fid in sorted(by_fid.keys()):
        if fid in seen_fids:
            continue
        f_groups = by_fid[fid]
        lines.append("")
        lines.append("[*] %s  (Số lượng API: %d)" % (format_feature_label(fid, ""), len(f_groups)))
        for idx, g in enumerate(f_groups, 1):
            lines.append("   %d. %s [%s]  %s %s" % (
                idx, format_api_label(g.gid), format_group_id(g.gid), g.method, g.path))
    return "\n".join(lines)


def parse_bulk_cookies(text):
    """
    Parse a raw 'Cookie: a=1; b=2' header or 'a=1; b=2' / newline pairs into
    individual COOKIE_SET (or COOKIE_REMOVE) rules.
    """
    out = []
    for line in (text or "").splitlines():
        s = line.strip()
        if not s:
            continue
        if s.lower().startswith("cookie:"):
            s = s.split(":", 1)[1].strip()
        for part in s.split(";"):
            p = part.strip()
            if not p or "=" not in p:
                continue
            k, v = p.split("=", 1)
            name = sanitize_header_name(k)
            if not name:
                continue
            val = sanitize_header_value(v)
            mode = MODE_COOKIE_REMOVE if val.upper() == REMOVE_TOKEN else MODE_COOKIE_SET
            out.append({"name": name, "value": val, "mode": mode})
    return out



def parse_bulk_headers(text):
    """Parse pasted 'Name: value' lines into rule dicts."""
    out = []
    for line in (text or "").splitlines():
        line = line.strip()
        if not line or ":" not in line:
            continue
        k, v = line.split(":", 1)
        name = sanitize_header_name(k)
        if not name:
            continue
        out.append({"name": name, "value": sanitize_header_value(v), "mode": normalize_mode(None, v)})
    return out


def merge_config(stored):
    cfg = dict(DEFAULT_CONFIG)
    if isinstance(stored, dict):
        for k in DEFAULT_CONFIG:
            if k in stored:
                cfg[k] = stored[k]
    for k, v in DEFAULT_CONFIG.items():
        if isinstance(v, bool):
            cfg[k] = _as_bool(cfg[k], v)
        elif isinstance(v, int):
            try:
                cfg[k] = int(cfg[k])
            except Exception:
                cfg[k] = v
        else:
            cfg[k] = "" if cfg[k] is None else "%s" % cfg[k]
    cfg["threads"] = max(1, min(64, cfg["threads"]))
    if cfg["send_profile"] not in [p[0] for p in SEND_PROFILES]:
        cfg["send_profile"] = DEFAULT_CONFIG["send_profile"]
    for key, label, delay, jitter, conc in SEND_PROFILES:
        if key == cfg["send_profile"] and delay is not None:
            cfg["send_delay_ms"], cfg["send_jitter_pct"], cfg["host_concurrency"] = delay, jitter, conc
    cfg["send_delay_ms"] = max(0, min(60000, cfg["send_delay_ms"]))
    cfg["send_jitter_pct"] = max(0, min(100, cfg["send_jitter_pct"]))
    cfg["host_concurrency"] = max(1, min(16, cfg["host_concurrency"]))
    cfg["max_retries"] = max(0, min(10, cfg["max_retries"]))
    if cfg["target_query_mode"] not in [k for k, _ in TARGET_QUERY_MODES]:
        cfg["target_query_mode"] = "ignore"
    if cfg["copy_stt_fallback"] not in [k for k, _ in COPY_STT_FALLBACKS]:
        cfg["copy_stt_fallback"] = "none"
    cfg["copy_counter"] = max(1, cfg["copy_counter"])
    if not cfg["copy_format"].strip():
        cfg["copy_format"] = DEFAULT_CONFIG["copy_format"]
    cfg["short_path_len"] = max(8, min(200, cfg["short_path_len"]))
    return cfg


# =============================================================================
# Threading helpers
# =============================================================================


class _Task(Runnable):
    """Explicit Runnable wrapper (avoids Runnable/Callable ambiguity in Jython)."""

    def __init__(self, fn, log_fn=None):
        self._fn = fn
        self._log = log_fn

    def run(self):
        try:
            self._fn()
        except Throwable as t:
            msg = "Unhandled Java exception in task: %s" % u_text(t)
            try:
                if self._log:
                    self._log(msg)
            except Exception:
                pass
        except Exception:
            msg = "Unhandled exception in task:\n%s" % u_text(traceback.format_exc())
            try:
                if self._log:
                    self._log(msg)
            except Exception:
                pass


def ui_call(fn):
    """Run fn on the Swing Event Dispatch Thread."""
    if SwingUtilities.isEventDispatchThread():
        fn()
    else:
        SwingUtilities.invokeLater(_Task(fn))


def parse_retry_after(header_lines, now=None):
    """Seconds to wait from a Retry-After header (delta-seconds or HTTP-date), capped at 300."""
    for h in header_lines or []:
        line = u_text(h)
        if ":" not in line:
            continue
        name, value = line.split(":", 1)
        if name.strip().lower() != "retry-after":
            continue
        v = value.strip()
        if v.isdigit():
            return float(min(int(v), 300))
        try:
            import email.utils
            parsed = email.utils.parsedate_tz(v)
            if parsed:
                secs = email.utils.mktime_tz(parsed) - (now if now is not None else time.time())
                return float(max(0, min(secs, 300)))
        except Exception:
            pass
        return None
    return None


class _SendJob(object):
    def __init__(self, group, res):
        self.group = group
        self.res = res
        self.key = (group.protocol, group.host, group.port)
        self.retries = 0


class _HostState(object):
    def __init__(self):
        self.queue = deque()
        self.inflight = 0
        self.next_ok = 0.0
        self.paused_until = 0.0
        self.penalty = 1.0
        self.ok_streak = 0


class SendDispatcher(object):
    """
    Single gate for EVERY outgoing request (auto-send after capture, bulk send, single send).

    Per target host:
      * requests leave in FIFO order, at most `host_concurrency` at a time;
      * consecutive requests are spaced by `send_delay_ms` +/- `send_jitter_pct`, measured
        from when the previous answer arrived - the rhythm of a person clicking around;
      * a 429 / 503 answer pauses that host (Retry-After is honoured, otherwise an
        exponential back-off), halves its speed, forces one-at-a-time and puts the request
        back at the head of the queue (up to `max_retries`). Successful streaks speed back up.
    Workers never sleep: pacing is done by scheduling a wake-up for the next ready host.
    """
    MAX_PENALTY = 16.0
    RECOVER_AFTER = 8

    def __init__(self, run_fn, executor, scheduler, cfg_fn, log_fn=None, clock=None, rand=None):
        self._run_fn = run_fn
        self._executor = executor
        self._scheduler = scheduler
        self._cfg_fn = cfg_fn
        self._log = log_fn
        self._clock = clock or time.time
        self._rand = rand or random.random
        self._lock = threading.RLock()
        self._hosts = {}
        self._order = []
        self._wake_at = None

    def _host(self, key):
        h = self._hosts.get(key)
        if h is None:
            h = _HostState()
            self._hosts[key] = h
            self._order.append(key)
        return h

    def _pacing(self):
        cfg = self._cfg_fn()
        return (cfg.get("send_delay_ms", 0) / 1000.0, cfg.get("send_jitter_pct", 0) / 100.0,
                max(1, cfg.get("host_concurrency", 1)), cfg.get("max_retries", 0))

    def _gap(self, h, delay, jitter):
        gap = delay * h.penalty
        if jitter > 0:
            gap *= 1.0 + jitter * (2.0 * self._rand() - 1.0)
        return max(0.0, gap)

    def submit(self, jobs):
        with self._lock:
            for job in jobs:
                self._host(job.key).queue.append(job)
        self.pump()

    def cancel_all(self):
        """Drop every queued (not yet sent) job and return them."""
        dropped = []
        with self._lock:
            for h in self._hosts.values():
                dropped.extend(h.queue)
                h.queue.clear()
        return dropped

    def snapshot(self):
        """(queued, in_flight, slowest_penalty, seconds_until_resume)"""
        with self._lock:
            now = self._clock()
            queued = sum([len(h.queue) for h in self._hosts.values()])
            inflight = sum([h.inflight for h in self._hosts.values()])
            penalty = max([h.penalty for h in self._hosts.values()] or [1.0])
            wait = max([h.paused_until - now for h in self._hosts.values()] or [0.0])
        return queued, inflight, penalty, max(0.0, wait)

    def _wake(self):
        with self._lock:
            self._wake_at = None
        self.pump()

    def pump(self):
        run = []
        wake_delay = None
        with self._lock:
            now = self._clock()
            delay, jitter, conc, _ = self._pacing()
            earliest = None
            for key in self._order:
                h = self._hosts[key]
                limit = 1 if h.penalty > 1.0 else conc
                while h.queue and h.inflight < limit:
                    ready = max(h.next_ok, h.paused_until)
                    if ready > now:
                        earliest = ready if earliest is None else min(earliest, ready)
                        break
                    job = h.queue.popleft()
                    h.inflight += 1
                    h.next_ok = now + self._gap(h, delay, jitter)
                    run.append(job)
            if earliest is not None and (self._wake_at is None or earliest < self._wake_at - 0.005):
                self._wake_at = earliest
                wake_delay = earliest - now
        if wake_delay is not None:
            self._scheduler.schedule(_Task(self._wake, self._log),
                                     int(wake_delay * 1000) + 1, TimeUnit.MILLISECONDS)
        for job in run:
            self._executor.execute(_Task((lambda j=job: self._run_fn(j)), self._log))

    def will_retry(self, job, status):
        return status in RETRYABLE_STATUS and job.retries < self._pacing()[3]

    def done(self, job, status, retry_after=None):
        """Report a finished request. Returns False when it was queued again for a retry."""
        requeued = False
        notice = None
        with self._lock:
            now = self._clock()
            h = self._host(job.key)
            h.inflight = max(0, h.inflight - 1)
            delay, jitter, conc, max_retries = self._pacing()
            if status in RETRYABLE_STATUS:
                h.ok_streak = 0
                h.penalty = min(self.MAX_PENALTY, h.penalty * 2.0)
                wait = retry_after if retry_after is not None else min(60.0, max(2.0, delay * h.penalty * 2.0))
                if now + wait > h.paused_until + 0.5:
                    notice = (job.key, status, wait, h.penalty)
                h.paused_until = max(h.paused_until, now + wait)
                if job.retries < max_retries:
                    job.retries += 1
                    h.queue.appendleft(job)
                    requeued = True
            else:
                h.ok_streak += 1
                if h.penalty > 1.0 and h.ok_streak >= self.RECOVER_AFTER:
                    h.penalty = max(1.0, h.penalty / 2.0)
                    h.ok_streak = 0
                h.next_ok = max(h.next_ok, now + self._gap(h, delay, jitter))
        if notice is not None and self._log is not None:
            self._log("Host %s trả HTTP %d -> tạm dừng %.1fs, giảm tốc x%d, gửi từng request một."
                      % (notice[0][1], notice[1], notice[2], int(notice[3])))
        self.pump()
        return not requeued


# =============================================================================
# Domain model
# =============================================================================


class FeatureGroup(object):
    """Represents a user-named feature / hierarchical action path (e.g. Toppage > menu > button "Search")."""

    def __init__(self, fid, name="", created=None):
        self.fid = fid
        clean = u_text(name).strip()
        self.name = clean if clean else ("Chức năng %d" % fid)
        self.created = created or time.strftime("%H:%M:%S")
        self._audit_level = None
        self._audit_summary = None

    def hierarchy_parts(self):
        return split_hierarchy_path(self.name)

    def label(self):
        return format_feature_label(self.fid, self.name)


class _BytesMessage(IHttpRequestResponse):
    """Minimal IHttpRequestResponse over byte arrays, so Burp can move them to its temp file."""

    def __init__(self, service, request, response):
        self._service = service
        self._request = request
        self._response = response

    def getRequest(self):
        return self._request

    def getResponse(self):
        return self._response

    def getHttpService(self):
        return self._service

    def getComment(self):
        return None

    def getHighlight(self):
        return None

    def setRequest(self, message):
        self._request = message

    def setResponse(self, message):
        self._response = message

    def setComment(self, comment):
        pass

    def setHighlight(self, color):
        pass

    def setHttpService(self, service):
        self._service = service


class RoleResult(object):
    """
    One row of an API group: the original request, or one role's variant of it.

    A role variant is VIRTUAL: it keeps only the role's rule snapshot (taken at capture
    time) and builds its request from the group's original on demand. `request` holds
    real bytes only for the original or after the user edited the request by hand.
    """

    def __init__(self, role_name, role_index, request_bytes=None, is_stripped_auth=False, is_original=False,
                 group=None, rules=None):
        self.role_name = u_text(role_name)
        self.role_index = role_index
        self._request = request_bytes
        self._group = group
        self.rules = rules
        self.is_stripped_auth = bool(is_stripped_auth)
        self.is_original = bool(is_original)
        self._response = None
        self._store = None
        self.status = None
        self.length = None
        self.elapsed_ms = None
        self.state = STATE_ORIGIN if is_original else STATE_NOT_SENT
        self.error = ""
        self.sent_count = 0
        self.tab_name = ""
        self.role_key = None      # the role's own name (display names may carry a 01_ prefix)
        self._audit_level = None
        self._audit_badge = None

    def _get_request(self):
        if self._request is not None:
            return self._request
        g = self._group
        if g is None:
            return None
        if self.is_original and not self.rules:
            return g.orig_request
        return g.build_request(self)

    def _set_request(self, value):
        self._request = value

    request = property(_get_request, _set_request)

    def has_custom_request(self):
        return self._request is not None

    def _get_response(self):
        if self._store is not None:
            return self._store.getResponse()
        if self._response is not None:
            return self._response
        if self.is_original and self._group is not None:
            return self._group.orig_response
        return None

    def _set_response(self, value):
        self._store = None
        self._response = value

    response = property(_get_response, _set_response)

    def set_response_store(self, store):
        """Keep the response in Burp's temp file (store: IHttpRequestResponsePersisted)."""
        self._response = None
        self._store = store


class ApiGroup(object):
    def __init__(self, gid, service, method, path, url, orig_request, orig_response, source,
                 fid=1, feature_name=""):
        self.gid = gid
        self.fid = fid
        self.feature_name = u_text(feature_name).strip() or ("Chức năng %d" % fid)
        self.service = service
        self.host = u_text(service.getHost())
        self.port = service.getPort()
        self.protocol = u_text(service.getProtocol())
        self.method = u_text(method)
        self.path = u_text(path)
        self.url = u_text(url)
        self._store = None
        self._orig_request = orig_request
        self._orig_response = orig_response
        self.has_orig_response = orig_response is not None
        self.base_headers = None
        self.body_offset = 0
        self.message_builder = None
        self.orig_status = None
        self.orig_length = None
        self.source = u_text(source)
        self.created = time.strftime("%H:%M:%S")
        self.orig_result = RoleResult(
            "[API GỐC] 00_Original (Acc Crawl)", -1, None,
            is_stripped_auth=False, is_original=True, group=self
        )
        self.orig_result.state = STATE_ORIGIN if self.has_orig_response else STATE_NOT_SENT
        self.orig_result.tab_name = repeater_tab_name(gid, method, path, "00_Original_Crawl")
        self.results = []
        self.target = None      # TargetEntry of the imported Excel list this API matched, if any
        self.role_overrides = {}  # {role name: enabled} set for this API only
        self.copy_stt = None      # number given by the "STT tăng dần" copy mode
        self.copied_label = None  # last "STT. path" line copied for this API
        self._audit_level = None
        self._audit_summary = None

    def _get_orig_request(self):
        if self._store is not None:
            return self._store.getRequest()
        return self._orig_request

    def _set_orig_request(self, value):
        self._orig_request = value

    orig_request = property(_get_orig_request, _set_orig_request)

    def _get_orig_response(self):
        if self._orig_response is not None:
            return self._orig_response
        if self._store is not None:
            return self._store.getResponse()
        return None

    def _set_orig_response(self, value):
        self._orig_response = value
        self.has_orig_response = value is not None

    orig_response = property(_get_orig_response, _set_orig_response)

    def attach_store(self, store):
        """Hand the original request/response over to Burp's temp file and drop the heap copies."""
        if store is not None:
            self._store = store
            self._orig_request = None
            self._orig_response = None

    def build_request(self, res):
        """Materialize a role's request: original headers + the role's rule snapshot + original body."""
        if self.base_headers is None or self.message_builder is None:
            return None
        headers = apply_header_rules(self.base_headers, res.rules or [])
        return self.message_builder(headers, self.orig_request, self.body_offset)

    def sync_original_meta(self, short_path_len=40, include_feature=False):
        self.orig_result.status = self.orig_status
        self.orig_result.length = self.orig_length
        if self.orig_result.state in (STATE_ORIGIN, STATE_NOT_SENT):
            self.orig_result.state = STATE_ORIGIN if self.has_orig_response else STATE_NOT_SENT
        self.orig_result.tab_name = repeater_tab_name(
            self.gid, self.method, self.path, "00_Original_Crawl",
            short_path_len, self.fid, include_feature
        )
        evaluate_role_result(self, self.orig_result)

    def all_entries(self):
        """Return [1 API gốc] + [N API roles thêm]."""
        return [self.orig_result] + list(self.results)

    def recalc_audit(self):
        """Pre-compute and cache audit status for O(1) Swing table rendering."""
        evaluate_role_result(self, self.orig_result)
        for r in self.results:
            evaluate_role_result(self, r)
        return evaluate_group_audit(self)

    def use_https(self):
        return (self.protocol or "").lower() == "https"


class RoleStore(object):
    """Thread-safe ordered role list; returns deep copies."""

    def __init__(self):
        self._lock = threading.RLock()
        self._roles = []

    @staticmethod
    def _copy(r):
        return {"name": u_text(r.get("name", "")), "enabled": bool(r.get("enabled", True)),
                "headers": [dict(h) for h in r.get("headers", [])]}

    def all(self):
        with self._lock:
            return [self._copy(r) for r in self._roles]

    def enabled(self):
        with self._lock:
            return [self._copy(r) for r in self._roles if r.get("enabled")]

    def count(self):
        with self._lock:
            return len(self._roles)

    def enabled_count(self):
        with self._lock:
            return len([r for r in self._roles if r.get("enabled")])

    def get(self, idx):
        with self._lock:
            return self._copy(self._roles[idx])

    def set_all(self, roles):
        with self._lock:
            self._roles = [self._copy(r) for r in roles]

    def add(self, role):
        with self._lock:
            self._roles.append(self._copy(role))
            return len(self._roles) - 1

    def update(self, idx, role):
        with self._lock:
            self._roles[idx] = self._copy(role)

    def set_enabled(self, idx, enabled):
        with self._lock:
            if 0 <= idx < len(self._roles):
                self._roles[idx]["enabled"] = bool(enabled)

    def set_all_enabled(self, enabled):
        with self._lock:
            for r in self._roles:
                r["enabled"] = bool(enabled)

    def remove(self, indices):
        with self._lock:
            for i in sorted(set(indices), reverse=True):
                if 0 <= i < len(self._roles):
                    del self._roles[i]

    def move(self, idx, delta):
        with self._lock:
            j = idx + delta
            if 0 <= idx < len(self._roles) and 0 <= j < len(self._roles):
                self._roles[idx], self._roles[j] = self._roles[j], self._roles[idx]
                return j
            return idx


# =============================================================================
# Table models (EDT only)
# =============================================================================


class RoleTableModel(AbstractTableModel):
    COLS = ["#", "Enabled", "Role Name", "Rules (Header / Cookie / JWT)"]

    def __init__(self, ext):
        self._ext = ext
        self._rows = []

    def reload(self):
        self._rows = self._ext.roles.all()
        self.fireTableDataChanged()

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c == 0:
            return Integer
        if c == 1:
            return Boolean
        return String

    def isCellEditable(self, r, c):
        return c == 1

    def setValueAt(self, value, r, c):
        if c == 1 and 0 <= r < len(self._rows):
            enabled = bool(value)
            self._rows[r]["enabled"] = enabled
            self._ext.roles.set_enabled(r, enabled)
            self._ext.save_roles()
            self.fireTableCellUpdated(r, c)
            self._ext.update_status()

    def getValueAt(self, r, c):
        role = self._rows[r]
        if c == 0:
            return Integer(r + 1)
        if c == 1:
            return Boolean(role["enabled"])
        if c == 2:
            return u_text(role["name"])
        parts = []
        for h in role["headers"]:
            mode = h.get("mode", MODE_REPLACE)
            name = u_text(h.get("name", ""))
            val = u_text(h.get("value", ""))
            has_jwt = bool(_JWT_RE.search(val))
            if mode == MODE_REMOVE:
                parts.append("-%s" % name)
            elif mode == MODE_ADD:
                parts.append("+%s%s" % (name, "[JWT]" if has_jwt else ""))
            elif mode == MODE_COOKIE_SET:
                parts.append("Cookie:%s%s" % (name, "[JWT]" if has_jwt else ""))
            elif mode == MODE_COOKIE_REMOVE:
                parts.append("-Cookie:%s" % name)
            else:
                parts.append("%s%s" % (name, "[JWT]" if has_jwt else ""))
        return ", ".join(parts)


class FeatureTableModel(AbstractTableModel):
    """
    Lists all Feature batches (Tên 1, Tên 2, ...) plus row 0 = [All Features].
    Column 1 (Tên chức năng) is directly editable for Feature rows.
    Cells come from a snapshot (build_feature_rows) refreshed by the UI tick, so painting is O(1).
    """
    COLS = ["#", "Tên chức năng", "Số API", "Trạng thái Role (Màu)", "Danh sách API"]

    def __init__(self, ext):
        self._ext = ext
        self._rows = build_feature_rows(HierarchyStats(ext.features_list(), []), ext.active_feature_id())

    def reload(self, rows):
        same_size = len(rows) == len(self._rows)
        self._rows = rows
        if same_size:
            # Row-level event: keeps the selection, unlike fireTableDataChanged.
            self.fireTableRowsUpdated(0, len(rows) - 1)
        else:
            self.fireTableDataChanged()
        return same_size

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c == 2:
            return Integer
        return String

    def isCellEditable(self, r, c):
        return r > 0 and c == 1

    def feature_at_row(self, r):
        if 0 < r < len(self._rows):
            return self._rows[r][2]
        return None

    def audit_level_at(self, r):
        if 0 <= r < len(self._rows):
            return self._rows[r][1]
        return AUDIT_NONE

    def accent_key_at(self, r):
        f = self.feature_at_row(r)
        return None if f is None else f.fid

    def setValueAt(self, value, r, c):
        f = self.feature_at_row(r)
        if f is None or c != 1:
            return
        raw = u_text(value or "").strip()
        m = re.match(r"^(?:T[êe]n\s*\d+\s*[:\-]\s*)(.+)$", raw, re.IGNORECASE)
        if m:
            raw = m.group(1).strip()
        self._ext.rename_feature(f.fid, raw or ("Chức năng %d" % f.fid))

    def getValueAt(self, r, c):
        v = self._rows[r][0][c]
        if c == 2:
            return Integer(v)
        return v


class GroupTableModel(AbstractTableModel):
    COLS = ["API #", "Group", "Group Path (Click đúp để chọn/đổi)", "Đánh giá / Màu (Info)", "Method", "Host", "Path",
            "Orig", "Orig Len", "1 Gốc + Roles", "Đã gửi", "Source", "Time", "📋 Đã copy", "Copy", "Excel"]
    COPY_COL = 14
    EXCEL_COL = 15

    def __init__(self, ext=None):
        self._ext = ext
        self._all_rows = []
        self._rows = []
        self._row_of = {}
        self._filter_fid = None
        self._filter_prefix = None
        self._filter_audit = AUDIT_FILTER_ALL

    def _matches(self, g):
        if self._filter_fid is not None and g.fid != self._filter_fid:
            return False
        if self._filter_prefix and not hierarchy_matches_prefix(g.feature_name, self._filter_prefix):
            return False
        if self._filter_audit and self._filter_audit != AUDIT_FILTER_ALL:
            lvl = g._audit_level if g._audit_level is not None else evaluate_group_audit(g)[0]
            if self._filter_audit == AUDIT_ERROR:
                return any(r.state == STATE_ERROR or (r.status is not None and r.status >= 500)
                           for r in g.results)
            if self._filter_audit == AUDIT_WARN:
                return any((r._audit_level or evaluate_role_result(g, r)[0]) == AUDIT_WARN for r in g.results)
            if lvl != self._filter_audit:
                return False
        return True

    def _rebuild_view(self):
        self._rows = [g for g in self._all_rows if self._matches(g)]
        self._row_of = dict([(id(g), i) for i, g in enumerate(self._rows)])

    # Filter setters are no-ops when nothing changes: a redundant fireTableDataChanged
    # would drop the user's selection and re-sort the whole table.
    def set_feature_filter(self, fid):
        if fid == self._filter_fid and self._filter_prefix is None:
            return
        self._filter_fid = fid
        self._filter_prefix = None
        self._rebuild_view()
        self.fireTableDataChanged()

    def set_hierarchy_filter(self, prefix_path):
        prefix = u_text(prefix_path).strip() if prefix_path else None
        if prefix == self._filter_prefix and self._filter_fid is None:
            return
        self._filter_fid = None
        self._filter_prefix = prefix
        self._rebuild_view()
        self.fireTableDataChanged()

    def hierarchy_filter(self):
        return self._filter_prefix

    def feature_filter(self):
        return self._filter_fid

    def set_audit_filter(self, audit_level):
        level = audit_level or AUDIT_FILTER_ALL
        if level == self._filter_audit:
            return
        self._filter_audit = level
        self._rebuild_view()
        self.fireTableDataChanged()

    def accent_key_at(self, r):
        g = self.group_at(r)
        return None if g is None else g.fid

    def method_at(self, r):
        g = self.group_at(r)
        return None if g is None else g.method

    def audit_level_at(self, r):
        g = self.group_at(r)
        if g is None:
            return AUDIT_NONE
        if g._audit_level is not None:
            return g._audit_level
        lvl, _ = evaluate_group_audit(g)
        return lvl

    def isCellEditable(self, r, c):
        # Allow per-API Group Path selection directly on Column 2
        return c == 2 and 0 <= r < len(self._rows)

    def setValueAt(self, value, r, c):
        if c != 2 or not (0 <= r < len(self._rows)):
            return
        g = self._rows[r]
        raw = u_text(value or "").strip()
        if not raw:
            return
        m = re.match(r"^(?:T[êe]n\s*\d+\s*[:\-]\s*)(.+)$", raw, re.IGNORECASE)
        if m:
            raw = m.group(1).strip()
        if self._ext is not None:
            self._ext.assign_group_to_path(g, raw)

    def add(self, group):
        self.add_many([group])

    def add_many(self, groups):
        """Append a batch of captured groups with ONE table event."""
        first = len(self._rows)
        for group in groups:
            self._all_rows.append(group)
            if self._matches(group):
                self._row_of[id(group)] = len(self._rows)
                self._rows.append(group)
        if len(self._rows) > first:
            self.fireTableRowsInserted(first, len(self._rows) - 1)

    def remove_groups(self, groups):
        ids = set([id(g) for g in groups])
        self._all_rows = [g for g in self._all_rows if id(g) not in ids]
        self._rebuild_view()
        self.fireTableDataChanged()

    def clear(self):
        self._all_rows = []
        self._rows = []
        self._row_of = {}
        self.fireTableDataChanged()

    def group_count(self):
        return len(self._all_rows)

    def row_of(self, group):
        return self._row_of.get(id(group), -1)

    def group_at(self, r):
        if 0 <= r < len(self._rows):
            return self._rows[r]
        return None

    def all_groups(self):
        return list(self._all_rows)

    def groups_for_feature(self, fid):
        return [g for g in self._all_rows if g.fid == fid]

    def groups_for_hierarchy_prefix(self, prefix_path):
        if not prefix_path:
            return list(self._all_rows)
        return [g for g in self._all_rows if hierarchy_matches_prefix(g.feature_name, prefix_path)]

    def refresh_group(self, group):
        """True if only that row was repainted; False if the filtered view had to be rebuilt."""
        i = self._row_of.get(id(group), -1)
        matches = self._matches(group)
        if i >= 0 and matches:
            self.fireTableRowsUpdated(i, i)
            return True
        if i < 0 and not matches:
            return True
        self._rebuild_view()
        self.fireTableDataChanged()
        return False

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (7, 8):
            return Integer
        return String

    def getValueAt(self, r, c):
        g = self._rows[r]
        if c == 0:
            return format_api_label(g.gid)
        if c == 1:
            return format_group_id(g.gid)
        if c == 2:
            return g.feature_name
        if c == 3:
            if g._audit_summary is not None:
                return g._audit_summary
            _, summary = evaluate_group_audit(g)
            return summary
        if c == 4:
            return g.method
        if c == 5:
            default_port = ((g.protocol == "https" and g.port == 443) or
                            (g.protocol == "http" and g.port == 80))
            return g.host if default_port else "%s:%s" % (g.host, g.port)
        if c == 6:
            return g.path
        if c == 7:
            return None if g.orig_status is None else Integer(g.orig_status)
        if c == 8:
            return None if g.orig_length is None else Integer(g.orig_length)
        if c == 9:
            return roles_label(g)
        if c == 10:
            done = len([x for x in g.results if x.state in (STATE_DONE, STATE_ERROR)])
            return "%d/%d" % (done, len(g.results))
        if c == 11:
            return g.source
        if c == 12:
            return g.created
        if c == 13:
            return getattr(g, "copied_label", None) or ""
        if c == 14:
            return ""
        if c == 15:
            e = getattr(g, "target", None)
            if e is None:
                return ""
            hits = getattr(self._ext, "target_hits", None)
            n = hits.count(e) if hits is not None else 0
            return (u"#%s · gặp %d" % (u_text(e.stt), n)) if n else (u"#%s" % u_text(e.stt))
        return ""


class ResultTableModel(AbstractTableModel):
    """
    Displays:
      Row 0     : [API GỐC] 00_Original (Acc Crawl) - original Proxy request/response
      Rows 1..N : Cloned Role requests (01_Admin .. N_Role)
    """
    COLS = ["#", "Loại / Role", "Đánh giá Role (Màu)", "State", "Status", "Body Len",
            "Delta vs Orig", "Time (ms)", "Sends", "Repeater Tab / Error"]

    def __init__(self):
        self._group = None

    def set_group(self, group):
        self._group = group
        self._last_n = self.getRowCount()
        self.fireTableDataChanged()

    def rows_updated(self):
        """Repaint every row without dropping the selection (full refresh if roles were added / removed)."""
        n = self.getRowCount()
        if n != getattr(self, "_last_n", n):
            self.fireTableDataChanged()
        elif n > 0:
            self.fireTableRowsUpdated(0, n - 1)
        self._last_n = n

    def accent_key_at(self, r):
        res = self.result_at(r)
        if res is None:
            return None
        return "ORIG" if getattr(res, "is_original", False) else None

    def group(self):
        return self._group

    def _entries(self):
        if self._group is None:
            return []
        if getattr(self._group, "orig_result", None) is not None:
            return [self._group.orig_result] + list(self._group.results)
        return list(self._group.results)

    def result_at(self, r):
        entries = self._entries()
        if 0 <= r < len(entries):
            return entries[r]
        return None

    def audit_level_at(self, r):
        res = self.result_at(r)
        if res is None:
            return AUDIT_NONE
        if res._audit_level is not None:
            return res._audit_level
        lvl, _ = evaluate_role_result(self._group, res)
        return lvl

    def getRowCount(self):
        return len(self._entries())

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (4, 5, 6, 7, 8):
            return Integer
        return String

    def getValueAt(self, r, c):
        g = self._group
        entries = self._entries()
        res = entries[r]
        if c == 0:
            return "GỐC" if getattr(res, "is_original", False) else ("Role %d" % r)
        if c == 1:
            return res.role_name
        if c == 2:
            if res._audit_badge is not None:
                return res._audit_badge
            _, badge = evaluate_role_result(g, res)
            return badge
        if c == 3:
            return res.state
        if c == 4:
            return None if res.status is None else Integer(res.status)
        if c == 5:
            return None if res.length is None else Integer(res.length)
        if c == 6:
            if getattr(res, "is_original", False):
                return Integer(0) if res.length is not None else None
            if res.length is None or g.orig_length is None:
                return None
            return Integer(res.length - g.orig_length)
        if c == 7:
            return None if res.elapsed_ms is None else Integer(res.elapsed_ms)
        if c == 8:
            return Integer(res.sent_count)
        if c == 9:
            return res.error if res.error else res.tab_name
        return ""


class CoverageTableModel(AbstractTableModel):
    """One row per line of the imported Excel list, with what was captured for it."""
    COLS = ["STT", "Method", "Path (trong file)", "POSITION", "Trạng thái", "API #", "Path thực tế",
            "Vị trí tìm thấy", "Đánh giá", "📋 Đã copy", "Gợi ý gần đúng (dòng chưa bắt)", "Lượt gặp",
            "Các vị trí đã gặp (mới nhất trước)"]
    HITS_COL = 11
    PLACES_COL = 12
    FILTERS = ["Tất cả dòng", "Chưa bắt", "Đã bắt", "Đã gặp", "Chưa gặp lần nào"]

    def __init__(self):
        self._rows = []
        self._filter = 0

    def entry_at(self, r):
        return self._rows[r][3] if 0 <= r < len(self._rows) else None

    def row_of_entry(self, entry):
        for i, row in enumerate(self._rows):
            if row[3] is entry:
                return i
        return -1

    def reload(self, targets, groups, filter_idx=None, hits=None):
        if filter_idx is not None:
            self._filter = filter_idx
        rows = []
        near = NearMissIndex(groups or [])
        for e, found in coverage_rows(targets, groups):
            if (self._filter == 1 and found) or (self._filter == 2 and not found):
                continue
            met = hits.count(e) if hits is not None else 0
            if (self._filter == 3 and not met) or (self._filter == 4 and met):
                continue
            found = sorted(found, key=lambda g: g.gid)
            first = found[0] if found else None
            if first is None:
                level, state = AUDIT_NONE, u"Chưa bắt"
            else:
                level = _group_level(first)
                sent = any([r.state in (STATE_DONE, STATE_ERROR) for r in (first.results or [first.orig_result])])
                state = u"Đã bắt · %s" % (u"đã gửi" if sent else u"chưa gửi")
                if len(found) > 1:
                    state += u" (%d lần)" % len(found)
                if level == AUDIT_NONE:
                    level = AUDIT_REDIRECT  # captured but not sent yet: blue, distinct from "not captured"
            positions = []
            for g in found:
                if g.feature_name not in positions:
                    positions.append(g.feature_name)
            cells = [u_text(e.stt), e.method_label(), e.path, e.position, state,
                     u", ".join([format_api_label(g.gid) for g in found[:4]]) + (u" ..." if len(found) > 4 else u""),
                     strip_query(first.path) if first else u"",
                     u"; ".join(positions),
                     (getattr(first, "_audit_summary", None) or evaluate_group_audit(first)[1]) if first else u""]
            copied = [g.copied_label for g in found if getattr(g, "copied_label", None)]
            cells.append(copied[0] if copied else u"")
            hint = u""
            if not found:
                g, note = near.suggest(e)
                if g is not None:
                    hint = u"%s %s %s  (%s)" % (format_api_label(g.gid), g.method, strip_query(g.path), note)
            cells.append(hint)
            cells.append(hit_cell(hits, e))
            cells.append(u"; ".join(hits.positions(e)[:6]) if hits is not None else u"")
            rows.append((cells, level, found, e))
        self._rows = rows
        self.fireTableDataChanged()

    def groups_at(self, r):
        return self._rows[r][2] if 0 <= r < len(self._rows) else []

    def audit_level_at(self, r):
        return self._rows[r][1] if 0 <= r < len(self._rows) else AUDIT_NONE

    def accent_key_at(self, r):
        return None

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getValueAt(self, r, c):
        return self._rows[r][0][c]


def _mix(c1, c2, t):
    """Blend colour c1 towards c2 by t (0..1)."""
    return Color(int(c1.getRed() + (c2.getRed() - c1.getRed()) * t),
                 int(c1.getGreen() + (c2.getGreen() - c1.getGreen()) * t),
                 int(c1.getBlue() + (c2.getBlue() - c1.getBlue()) * t))


class RowPalette(object):
    """
    Row colours derived from the component's own background/foreground, so the same
    scheme reads well in Burp's light AND dark themes:
      * every row is zebra-striped (two shades), including audit-coloured rows;
      * audit levels tint the row instead of replacing its colour;
      * HTTP methods and branches get their own stable accent colours.
    """
    HUES = {
        AUDIT_INFO: (240, 185, 30),
        AUDIT_OK: (55, 175, 90),
        AUDIT_WARN: (245, 125, 25),
        AUDIT_ERROR: (225, 60, 60),
        AUDIT_REDIRECT: (65, 135, 235),
    }
    METHOD_HUES = {
        "GET": (25, 135, 70),
        "POST": (20, 100, 200),
        "PUT": (185, 105, 0),
        "PATCH": (125, 75, 190),
        "DELETE": (200, 40, 40),
    }
    ACCENTS = [(66, 133, 244), (234, 88, 12), (22, 163, 74), (168, 85, 247),
               (219, 39, 119), (13, 148, 136), (202, 138, 4), (100, 116, 139)]
    ORIG_ACCENT = (37, 99, 235)
    # Folder level 1, 2, 3 ... (cycles): same level -> same colour in every tree.
    LEVEL_HUES = [(37, 99, 235), (13, 148, 136), (147, 51, 234), (217, 119, 6),
                  (219, 39, 119), (22, 163, 74), (71, 85, 105)]
    MODE_HUES = {
        "REPLACE": (37, 99, 235),
        "ADD": (22, 163, 74),
        "REMOVE": (220, 38, 38),
        "COOKIE_SET": (147, 51, 234),
        "COOKIE_REMOVE": (234, 88, 12),
    }

    _cache = {}

    @classmethod
    def of(cls, bg, fg):
        key = (bg.getRGB(), fg.getRGB())
        pal = cls._cache.get(key)
        if pal is None:
            if len(cls._cache) > 8:
                cls._cache.clear()
            pal = cls(bg, fg)
            cls._cache[key] = pal
        return pal

    def __init__(self, bg, fg):
        self.dark = (bg.getRed() * 299 + bg.getGreen() * 587 + bg.getBlue() * 114) < 128000
        self.fg = fg
        self.zebra = (bg, _mix(bg, fg, 0.07))
        self.grid = _mix(bg, fg, 0.14)
        white = Color(255, 255, 255)
        black = Color(0, 0, 0)
        self.row_bg = {}
        self.audit_fg = {}
        for lvl, rgb in self.HUES.items():
            hue = Color(rgb[0], rgb[1], rgb[2])
            self.row_bg[lvl] = (_mix(bg, hue, 0.17), _mix(bg, hue, 0.27))
            self.audit_fg[lvl] = _mix(hue, white, 0.35) if self.dark else _mix(hue, black, 0.45)
        self.method_fg = {}
        for name, rgb in self.METHOD_HUES.items():
            hue = Color(rgb[0], rgb[1], rgb[2])
            self.method_fg[name] = _mix(hue, white, 0.40) if self.dark else hue
        self.accents = [Color(r, g, b) for (r, g, b) in self.ACCENTS]
        self.orig_accent = Color(self.ORIG_ACCENT[0], self.ORIG_ACCENT[1], self.ORIG_ACCENT[2])
        self.orig_fg = _mix(self.orig_accent, white, 0.45) if self.dark else self.orig_accent
        self._stripe_borders = {}
        self.pad_border = BorderFactory.createEmptyBorder(0, 6, 0, 6)
        self.muted = _mix(fg, bg, 0.42)
        self.dots = {}
        for lvl, rgb in self.HUES.items():
            self.dots[lvl] = Color(rgb[0], rgb[1], rgb[2])
        self.dot_none = _mix(bg, fg, 0.35)
        self.levels = []
        for rgb in self.LEVEL_HUES:
            hue = Color(rgb[0], rgb[1], rgb[2])
            fill = _mix(bg, hue, 0.20 if self.dark else 0.10)
            edge = _mix(bg, hue, 0.75)
            text = _mix(hue, white, 0.55) if self.dark else _mix(hue, black, 0.30)
            self.levels.append((fill, edge, text, hue))
        self.modes = {}
        for name, rgb in self.MODE_HUES.items():
            hue = Color(rgb[0], rgb[1], rgb[2])
            self.modes[name] = (_mix(bg, hue, 0.22 if self.dark else 0.12),
                                _mix(hue, white, 0.45) if self.dark else _mix(hue, black, 0.15),
                                _mix(bg, hue, 0.6))

    def level(self, depth):
        """(fill, edge, text, hue) of a folder at 1-based depth."""
        return self.levels[(max(depth, 1) - 1) % len(self.levels)]

    def dot(self, lvl):
        return self.dots.get(lvl, self.dot_none)

    def background(self, lvl, view_row):
        pair = self.row_bg.get(lvl, self.zebra)
        return pair[view_row & 1]

    def status_fg(self, code):
        if 200 <= code < 300:
            return self.audit_fg[AUDIT_OK]
        if 300 <= code < 400:
            return self.audit_fg[AUDIT_REDIRECT]
        if 400 <= code < 500:
            return self.audit_fg[AUDIT_INFO]
        if code >= 500:
            return self.audit_fg[AUDIT_ERROR]
        return self.fg

    def accent(self, key):
        if key is None:
            return None
        if key == "ORIG":
            return self.orig_accent
        return self.accents[(int(key) - 1) % len(self.accents)]

    def stripe_border(self, key):
        """Left colour bar marking which branch (or the original request) a row belongs to."""
        border = self._stripe_borders.get(key)
        if border is None:
            colour = self.accent(key)
            if colour is None:
                border = BorderFactory.createEmptyBorder(0, 10, 0, 6)
            else:
                border = BorderFactory.createCompoundBorder(
                    BorderFactory.createMatteBorder(0, 4, 0, 0, colour),
                    BorderFactory.createEmptyBorder(0, 6, 0, 6))
            self._stripe_borders[key] = border
        return border


class AuditTableRenderer(DefaultTableCellRenderer):
    """
    Shared cell renderer of the branch, API and role tables:
      - zebra-striped rows, tinted by audit level (yellow INFO / green OK / orange WARN /
        red ERROR / blue REDIRECT) - see RowPalette;
      - a colour bar in the first column per branch, so APIs of different branches
        cannot be confused when scanning a long list;
      - coloured HTTP method, status code and audit verdict.
    The BG_* / FG_* constants are the light-theme legend colours used by badges and buttons.
    """
    BG_INFO = Color(255, 247, 195)
    BG_OK = Color(228, 248, 232)
    BG_WARN = Color(255, 230, 195)
    BG_ERR = Color(255, 222, 222)
    BG_REDIR = Color(225, 239, 255)
    BG_EVEN = Color(255, 255, 255)
    BG_ODD = Color(248, 249, 252)

    FG_DEFAULT = Color(25, 25, 25)
    FG_INFO = Color(155, 85, 0)
    FG_OK = Color(0, 125, 40)
    FG_WARN = Color(190, 65, 0)
    FG_ERR = Color(190, 15, 15)
    FG_REDIR = Color(10, 80, 180)

    def __init__(self, model, status_col=None, audit_col=None, method_col=None, bold_cols=()):
        DefaultTableCellRenderer.__init__(self)
        self._model = model
        self._status_col = status_col
        self._audit_col = audit_col
        self._method_col = method_col
        self._bold_cols = set(bold_cols)
        if audit_col is not None:
            self._bold_cols.add(audit_col)
        if method_col is not None:
            self._bold_cols.add(method_col)
        self._plain_font = None
        self._bold_font = None

    def getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column):
        comp = DefaultTableCellRenderer.getTableCellRendererComponent(
            self, table, value, isSelected, False, row, column)
        model = self._model
        model_row = table.convertRowIndexToModel(row)
        model_col = table.convertColumnIndexToModel(column)
        pal = RowPalette.of(table.getBackground(), table.getForeground())

        font = table.getFont()
        if font != self._plain_font:
            self._plain_font = font
            self._bold_font = font.deriveFont(Font.BOLD)
        accent_key = model.accent_key_at(model_row)
        bold = model_col in self._bold_cols or (accent_key == "ORIG" and model_col <= 1)
        comp.setFont(self._bold_font if bold else font)
        comp.setBorder(pal.stripe_border(accent_key) if column == 0 else pal.pad_border)
        if isSelected:
            return comp

        lvl = model.audit_level_at(model_row)
        comp.setBackground(pal.background(lvl, row))
        fg = pal.fg
        if model_col == self._audit_col:
            fg = pal.audit_fg.get(lvl, fg)
        elif model_col == self._method_col:
            fg = pal.method_fg.get(u_text(value).upper(), fg)
        elif model_col == self._status_col and value is not None:
            try:
                fg = pal.status_fg(int("%s" % value))
            except Exception:
                pass
        elif accent_key == "ORIG" and model_col <= 1:
            fg = pal.orig_fg
        comp.setForeground(fg)
        return comp


class _ActionCellRenderer(AuditTableRenderer):
    """'copy' cell: a copy glyph; 'link' cell: the Excel STT drawn as a link."""

    def __init__(self, model, mode, tooltip_fn=None):
        AuditTableRenderer.__init__(self, model)
        self._mode = mode
        self._tooltip_fn = tooltip_fn

    def getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column):
        comp = AuditTableRenderer.getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column)
        pal = RowPalette.of(table.getBackground(), table.getForeground())
        if self._mode == "copy":
            comp.setIcon(_CopyIcon.of(comp.getForeground() if isSelected else pal.muted))
            comp.setText(u"")
            comp.setHorizontalAlignment(JLabel.CENTER)
        else:
            comp.setIcon(None)
            comp.setHorizontalAlignment(JLabel.LEFT)
            if value and not isSelected:
                comp.setForeground(pal.orig_fg)
            comp.setFont(comp.getFont().deriveFont(Font.BOLD))
        tip = None
        if self._tooltip_fn is not None:
            try:
                tip = self._tooltip_fn(table.convertRowIndexToModel(row))
            except (Exception, Throwable):
                tip = None
        comp.setToolTipText(tip)
        return comp


class _TableCellClick(MouseAdapter):
    """Single left click on one of `cols` (model indexes) -> fn(model_row, model_col); hand cursor over them."""

    def __init__(self, table, cols, fn):
        self._table = table
        self._cols = set(cols)
        self._fn = fn

    def _cell(self, event):
        t = self._table
        vr = t.rowAtPoint(event.getPoint())
        vc = t.columnAtPoint(event.getPoint())
        if vr < 0 or vc < 0:
            return None
        mc = t.convertColumnIndexToModel(vc)
        if mc not in self._cols:
            return None
        return t.convertRowIndexToModel(vr), mc

    def mouseClicked(self, event):
        if event.getClickCount() != 1 or not SwingUtilities.isLeftMouseButton(event):
            return
        cell = self._cell(event)
        if cell is not None:
            self._fn(cell[0], cell[1])

    def mouseMoved(self, event):
        cell = self._cell(event)
        self._table.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR if cell else Cursor.DEFAULT_CURSOR))


class _TreeChipClick(MouseAdapter):
    """Copy glyph / '[Excel #STT]' badge on an API row of a tree: click to copy / open the Excel row."""

    def __init__(self, tree, ext):
        self._tree = tree
        self._ext = ext

    def mouseClicked(self, event):
        if event.getClickCount() != 1 or not SwingUtilities.isLeftMouseButton(event):
            return
        zone = self._ext.tree_chip_at(self._tree, event.getX(), event.getY())
        if zone is not None:
            self._ext.on_chip(zone[0], zone[1])

    def mouseMoved(self, event):
        zone = self._ext.tree_chip_at(self._tree, event.getX(), event.getY())
        self._tree.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR if zone else Cursor.DEFAULT_CURSOR))


class HitTableModel(AbstractTableModel):
    """Every time the selected Excel row was met while crawling (newest first)."""
    COLS = ["Lần", "Thời gian", "Kết quả", "API #", "Method", "Path thực tế", "Host", "Vị trí đang đứng",
            "Lưu vào nhánh", "Nguồn", "Ghi chú"]
    LEVELS = {HIT_NEW: AUDIT_OK, HIT_DUP: AUDIT_REDIRECT, HIT_FILTERED: AUDIT_INFO}

    def __init__(self):
        self._events = []

    def set_events(self, events):
        self._events = list(reversed(events or []))
        self.fireTableDataChanged()

    def gid_at(self, r):
        return self._events[r].get("gid") if 0 <= r < len(self._events) else None

    def audit_level_at(self, r):
        return self.LEVELS.get(self._events[r].get("result"), AUDIT_NONE) if 0 <= r < len(self._events) else AUDIT_NONE

    def accent_key_at(self, r):
        return None

    def getRowCount(self):
        return len(self._events)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getValueAt(self, r, c):
        ev = self._events[r]
        return [ev.get("n"), ev.get("time"), HIT_LABELS.get(ev.get("result"), ev.get("result")),
                format_api_label(ev["gid"]) if ev.get("gid") else u"", ev.get("method"), ev.get("path"),
                ev.get("host"), ev.get("branch"), ev.get("filed"), ev.get("source"), ev.get("note") or u""][c]


def style_data_table(table):
    """Common look of the data tables: taller rows, hairline row separators, no vertical grid."""
    table.setRowHeight(24)
    table.setShowGrid(False)
    table.setShowHorizontalLines(True)
    table.setIntercellSpacing(Dimension(0, 1))
    table.setFillsViewportHeight(True)
    try:
        table.setGridColor(RowPalette.of(table.getBackground(), table.getForeground()).grid)
        header = table.getTableHeader()
        header.setFont(header.getFont().deriveFont(Font.BOLD))
    except (Exception, Throwable):
        pass


class HeaderRuleTableModel(AbstractTableModel):
    COLS = ["Header / Cookie Key", "Value (use [REMOVE] to strip)", "Mode"]

    def __init__(self, rules, on_change=None):
        self.rules = [dict(r) for r in rules]
        self._on_change = on_change

    def _changed(self):
        if self._on_change is not None:
            self._on_change()

    def set_rules(self, rules):
        self.rules = [dict(r) for r in rules]
        self.fireTableDataChanged()
        self._changed()

    def getRowCount(self):
        return len(self.rules)

    def getColumnCount(self):
        return 3

    def getColumnName(self, c):
        return self.COLS[c]

    def isCellEditable(self, r, c):
        return True

    def getValueAt(self, r, c):
        rule = self.rules[r]
        return [rule.get("name", ""), rule.get("value", ""), rule.get("mode", MODE_REPLACE)][c]

    def setValueAt(self, value, r, c):
        v = "" if value is None else "%s" % value
        self.rules[r][["name", "value", "mode"][c]] = v
        if c == 1 and v.strip().upper() == REMOVE_TOKEN:
            cur_mode = self.rules[r].get("mode", MODE_REPLACE)
            self.rules[r]["mode"] = (MODE_COOKIE_REMOVE if cur_mode in (MODE_COOKIE_SET, MODE_COOKIE_REMOVE)
                                     else MODE_REMOVE)
        self.fireTableRowsUpdated(r, r)
        self._changed()

    def add_rule(self, rule):
        self.rules.append(dict(rule))
        n = len(self.rules) - 1
        self.fireTableRowsInserted(n, n)
        self._changed()

    def remove_rows(self, rows):
        for i in sorted(set(rows), reverse=True):
            if 0 <= i < len(self.rules):
                del self.rules[i]
        self.fireTableDataChanged()
        self._changed()

    def move_rule(self, idx, delta):
        j = idx + delta
        if 0 <= idx < len(self.rules) and 0 <= j < len(self.rules):
            self.rules[idx], self.rules[j] = self.rules[j], self.rules[idx]
            self.fireTableDataChanged()
            self._changed()
            return j
        return idx


# =============================================================================
# Swing listeners / controllers
# =============================================================================


class _SelectionListener(ListSelectionListener):
    def __init__(self, fn):
        self._fn = fn

    def valueChanged(self, event):
        if not event.getValueIsAdjusting():
            self._fn()


class _TreeListener(TreeSelectionListener):
    def __init__(self, fn):
        self._fn = fn

    def valueChanged(self, event):
        self._fn()


class _LazyTreeLoader(TreeWillExpandListener):
    """Fills an API node with its role rows the first time the user expands it."""

    def __init__(self, fn):
        self._fn = fn

    def treeWillExpand(self, event):
        self._fn(event.getPath().getLastPathComponent())

    def treeWillCollapse(self, event):
        pass


class _Action(ActionListener):
    """Explicit ActionListener implementation (avoids Jython lambda coercion issues)."""

    def __init__(self, fn, *args):
        self._fn = fn
        self._args = args

    def actionPerformed(self, event):
        if self._args:
            self._fn(*self._args)
        else:
            self._fn(event)


class _ViewportWidthPanel(JPanel, Scrollable):
    """Panel that always takes the scroll pane's width (so wrapped text wraps), scrolling vertically."""

    def getPreferredScrollableViewportSize(self):
        return self.getPreferredSize()

    def getScrollableUnitIncrement(self, rect, orientation, direction):
        return 16

    def getScrollableBlockIncrement(self, rect, orientation, direction):
        return 96

    def getScrollableTracksViewportWidth(self):
        return True

    def getScrollableTracksViewportHeight(self):
        return False


class _KeyAction(AbstractAction):
    def __init__(self, fn):
        AbstractAction.__init__(self)
        self._fn = fn

    def actionPerformed(self, event):
        self._fn()


class _WindowClosing(WindowAdapter):
    def __init__(self, fn):
        self._fn = fn

    def windowClosing(self, event):
        self._fn()


class _FocusLost(FocusAdapter):
    def __init__(self, fn):
        self._fn = fn

    def focusLost(self, event):
        self._fn()


class _Change(ChangeListener):
    """Explicit ChangeListener implementation for JSpinner."""

    def __init__(self, fn):
        self._fn = fn

    def stateChanged(self, event):
        self._fn(event)


def _py_str_return(text):
    """
    Return `str` in both Python 2 (Jython 2.7, where `__str__`/`__repr__` MUST return
    UTF-8 encoded `bytes`/`str` to avoid `UnicodeEncodeError: 'ascii' codec`) and
    Python 3 (where `__str__`/`__repr__` must return `unicode`/`str`).
    """
    u = u_text(text)
    if str is _BYTES_TYPE and isinstance(u, _UNICODE_TYPE):
        return u.encode("utf-8")
    return u


class HierarchyTreeNode(DefaultMutableTreeNode):
    """
    Subclass of DefaultMutableTreeNode whose Java userObject is ALWAYS a plain
    Unicode string (preventing Jython from ever displaying '<_TreeNodeItem object at 0x...>'),
    while storing .kind, .payload, .label, and .audit_level directly on the node.
    """

    def __init__(self, kind, payload, label, audit_level=AUDIT_NONE, key=None, depth=0):
        clean_label = u_text(label)
        DefaultMutableTreeNode.__init__(self, clean_label)
        self.kind = kind
        self.payload = payload
        self.label = clean_label
        self.audit_level = audit_level
        self.key = key          # stable identity across rebuilds (selection / expansion restore)
        # folder level (1 = top), drives the level colour; not "depth"/"level": those are
        # read-only bean properties of DefaultMutableTreeNode under Jython
        self.folder_level = depth
        self.loaded = True      # False while a lazy node only holds its placeholder child

    def toString(self):
        return getattr(self, "label", "")

    def __unicode__(self):
        return getattr(self, "label", "")

    def __str__(self):
        return _py_str_return(getattr(self, "label", ""))

    def __repr__(self):
        return _py_str_return(getattr(self, "label", ""))


class _TreeNodeItem(object):
    """Legacy wrapper kept for compatibility; returns readable label in all string/repr contexts."""

    def __init__(self, kind, payload, label, audit_level=AUDIT_NONE):
        self.kind = kind
        self.payload = payload
        self.label = u_text(label)
        self.audit_level = audit_level

    def __str__(self):
        return _py_str_return(self.label)

    def __unicode__(self):
        return self.label

    def __repr__(self):
        return _py_str_return(self.label)

    def toString(self):
        return self.label


class _DotIcon(Icon):
    """Small filled circle / rounded square used as the tree-row marker."""
    _cache = {}

    @classmethod
    def of(cls, color, square=False):
        key = (color.getRGB(), square)
        icon = cls._cache.get(key)
        if icon is None:
            icon = cls(color, square)
            cls._cache[key] = icon
        return icon

    def __init__(self, color, square=False):
        self._color = color
        self._square = square

    def getIconWidth(self):
        return 12

    def getIconHeight(self):
        return 10

    def paintIcon(self, c, g, x, y):
        g2 = g.create()
        try:
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON)
            g2.setColor(self._color)
            if self._square:
                g2.fillRoundRect(x + 1, y, 10, 10, 4, 4)
            else:
                g2.fillOval(x + 1, y, 10, 10)
        finally:
            g2.dispose()


class _CopyIcon(Icon):
    """Small 'two sheets' copy glyph, drawn (no emoji font needed)."""
    _cache = {}

    @classmethod
    def of(cls, color):
        icon = cls._cache.get(color.getRGB())
        if icon is None:
            icon = cls(color)
            cls._cache[color.getRGB()] = icon
        return icon

    def __init__(self, color):
        self._color = color

    def getIconWidth(self):
        return 14

    def getIconHeight(self):
        return 14

    def paintIcon(self, c, g, x, y):
        g2 = g.create()
        try:
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON)
            g2.setColor(self._color)
            g2.drawRoundRect(x + 1, y + 1, 8, 9, 3, 3)
            bg = c.getBackground() if c is not None else None
            g2.setColor(bg or Color(255, 255, 255))
            g2.fillRoundRect(x + 4, y + 4, 8, 9, 3, 3)
            g2.setColor(self._color)
            g2.drawRoundRect(x + 4, y + 4, 8, 9, 3, 3)
            g2.drawLine(x + 6, y + 7, x + 10, y + 7)
            g2.drawLine(x + 6, y + 10, x + 10, y + 10)
        finally:
            g2.dispose()


class _GroupIcon(Icon):
    """API row marker: audit dot + a copy glyph (click it to copy 'STT. path')."""
    _cache = {}
    COPY_X = 14

    @classmethod
    def of(cls, dot, glyph):
        key = (id(dot), id(glyph))
        icon = cls._cache.get(key)
        if icon is None:
            icon = cls(dot, glyph)
            cls._cache[key] = icon
        return icon

    def __init__(self, dot, glyph):
        self._dot = dot
        self._glyph = glyph

    def getIconWidth(self):
        return self.COPY_X + 16

    def getIconHeight(self):
        return 14

    def paintIcon(self, c, g, x, y):
        self._dot.paintIcon(c, g, x, y + 2)
        self._glyph.paintIcon(c, g, x + self.COPY_X + 1, y)


class HierarchyTreeRenderer(JLabel, TreeCellRenderer):
    """
    Tree rows drawn as rounded "chips":
      * folders: border + light fill in the colour of their LEVEL (level 1 blue, level 2 teal,
        level 3 purple, ...), so siblings share a colour and parent/child never do; a dot at
        the right end shows the branch's audit verdict;
      * API / role rows: audit tint (yellow INFO, green OK, orange WARN, red ERROR) and an
        audit-coloured marker; the original request is drawn in blue.
    Colours come from RowPalette, i.e. from the tree's own colours (light and dark themes).
    """
    ARC = 10
    STRONG = ("ROOT", "FOLDER", "GROUP", "LOGBRANCH", "LOGAPI", "LOGSYS")
    report = None          # set by the extension: logs the first rendering error to Burp's Errors tab
    _reported = False

    def __init__(self):
        JLabel.__init__(self)
        self.setOpaque(False)
        self.setIconTextGap(5)
        self._fill = None
        self._edge = None
        self._dot = None
        self._fonts = (None, None)
        self._pad = BorderFactory.createEmptyBorder(2, 6, 2, 9)
        self._pad_dot = BorderFactory.createEmptyBorder(2, 6, 2, 22)
        self.setBorder(self._pad)

    def getTreeCellRendererComponent(self, tree, value, selected, expanded, leaf, row, hasFocus):
        try:
            self._configure(tree, value, selected)
        except (Exception, Throwable):
            self._fill = self._edge = self._dot = None
            try:
                self.setText(u_text(getattr(value, "label", None) or value))
            except (Exception, Throwable):
                pass
            cls = HierarchyTreeRenderer
            if not cls._reported and cls.report is not None:
                cls._reported = True
                try:
                    cls.report("Tree renderer error (rows fall back to plain text):\n%s"
                               % u_text(traceback.format_exc()))
                except (Exception, Throwable):
                    pass
        return self

    def _configure(self, tree, value, selected):
        kind = getattr(value, "kind", None)
        label = getattr(value, "label", None)
        lvl = getattr(value, "audit_level", AUDIT_NONE)
        depth = getattr(value, "folder_level", 0)
        if label is None and isinstance(value, DefaultMutableTreeNode):
            uobj = value.getUserObject()
            label = u_text(uobj) if uobj is not None else ""
        self.setText(u_text(label or ""))
        self._fill = self._edge = self._dot = None
        if tree is None:
            return
        # Some themes report no tree colours: fall back to the look-and-feel's, then plain white/black.
        bg = (tree.getBackground() or UIManager.getColor("Tree.background")
              or UIManager.getColor("Panel.background") or Color(255, 255, 255))
        fg = (UIManager.getColor("Tree.textForeground") or tree.getForeground()
              or UIManager.getColor("Label.foreground") or Color(20, 20, 20))
        pal = RowPalette.of(bg, fg)
        font = tree.getFont() or UIManager.getFont("Tree.font")
        if font is not None:
            if self._fonts[0] != font:
                self._fonts = (font, font.deriveFont(Font.BOLD))
            self.setFont(self._fonts[1] if kind in self.STRONG else font)

        fill = edge = dot = icon = None
        text = fg
        if kind in ("FOLDER", "LOGBRANCH"):
            fill, edge, text, hue = pal.level(depth)
            icon = _DotIcon.of(hue, square=True)
            if lvl in pal.dots:
                dot = pal.dot(lvl)
        elif kind in ("ROOT", "LOGSYS"):
            fill, edge = pal.zebra[1], pal.grid
            icon = _DotIcon.of(pal.dot_none, square=True)
        elif kind in ("GROUP", "LOGAPI"):
            fill = pal.row_bg.get(lvl, pal.zebra)[0] if lvl in pal.row_bg else pal.zebra[1]
            icon = _DotIcon.of(pal.dot(lvl))
            if kind == "GROUP":
                icon = _GroupIcon.of(icon, _CopyIcon.of(pal.muted))
        elif kind in ("ORIG", "ROLE", "LOGRES"):
            if lvl in pal.row_bg:
                fill = pal.row_bg[lvl][0]
            if kind == "ORIG":
                text = pal.orig_fg
            icon = _DotIcon.of(pal.orig_accent if kind == "ORIG" else pal.dot(lvl))
        else:
            text = pal.muted
        if selected:
            sel_bg = UIManager.getColor("Tree.selectionBackground") or Color(51, 120, 220)
            sel_fg = UIManager.getColor("Tree.selectionForeground") or Color(255, 255, 255)
            fill, edge, text = sel_bg, _mix(sel_bg, fg, 0.3), sel_fg
        self._fill, self._edge, self._dot = fill, edge, dot
        self.setForeground(text)
        self.setIcon(icon)
        self.setBorder(self._pad_dot if dot is not None else self._pad)

    def paintComponent(self, g):
        if self._fill is not None or self._edge is not None or self._dot is not None:
            g2 = g.create()
            try:
                g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON)
                w = self.getWidth()
                h = self.getHeight()
                if self._fill is not None:
                    g2.setColor(self._fill)
                    g2.fillRoundRect(0, 1, w - 1, h - 2, self.ARC, self.ARC)
                if self._edge is not None:
                    g2.setColor(self._edge)
                    g2.drawRoundRect(0, 1, w - 1, h - 3, self.ARC, self.ARC)
                if self._dot is not None:
                    g2.setColor(self._dot)
                    g2.fillOval(w - 16, (h - 9) // 2, 9, 9)
            finally:
                g2.dispose()
        self.super__paintComponent(g)

    def getPreferredSize(self):
        # Text is measured at 1x with integer metrics but drawn scaled (HiDPI 125-200 %) or with
        # fractional metrics, which can be a few % wider: reserve that slack so labels never clip.
        size = JLabel.getPreferredSize(self)
        text = self.getText()
        if text:
            size.width += 4 + self.getFontMetrics(self.getFont()).stringWidth(text) // 20
        return size


class _DoubleClick(MouseAdapter):
    def __init__(self, fn):
        self._fn = fn

    def mouseClicked(self, event):
        if event.getClickCount() == 2 and SwingUtilities.isLeftMouseButton(event):
            self._fn()


class _TreePopupListener(MouseAdapter):
    """Right-click context menu handler for JTree."""

    def __init__(self, tree, popup_fn):
        self._tree = tree
        self._popup_fn = popup_fn

    def _trigger(self, event):
        if event.isPopupTrigger() or SwingUtilities.isRightMouseButton(event):
            row = self._tree.getClosestRowForLocation(event.getX(), event.getY())
            if row >= 0:
                self._tree.setSelectionRow(row)
            self._popup_fn(event)

    def mousePressed(self, event):
        self._trigger(event)

    def mouseReleased(self, event):
        self._trigger(event)


class _TablePopupListener(MouseAdapter):
    """Right-click context menu handler for JTable (auto-selects row under cursor)."""

    def __init__(self, table, popup_fn):
        self._table = table
        self._popup_fn = popup_fn

    def _trigger(self, event):
        if event.isPopupTrigger() or SwingUtilities.isRightMouseButton(event):
            row = self._table.rowAtPoint(event.getPoint())
            if row >= 0:
                selected = self._table.getSelectedRows()
                if selected is None or row not in list(selected):
                    self._table.setRowSelectionInterval(row, row)
            self._popup_fn(event)

    def mousePressed(self, event):
        self._trigger(event)

    def mouseReleased(self, event):
        self._trigger(event)


class _SubFolderTableModel(AbstractTableModel):
    COLS = ["Cấp #", "Tên Thư mục / Cấp con (Click đúp để sửa trực tiếp)"]

    def __init__(self, segments):
        self.segments = [u_text(s) for s in segments]

    def getRowCount(self):
        return len(self.segments)

    def getColumnCount(self):
        return 2

    def getColumnName(self, c):
        return self.COLS[c]

    def isCellEditable(self, r, c):
        return c == 1

    def getValueAt(self, r, c):
        if c == 0:
            return "Cấp %d" % (r + 1)
        return self.segments[r]

    def setValueAt(self, val, r, c):
        if c == 1 and 0 <= r < len(self.segments):
            s = u_text(val).strip()
            if s:
                self.segments[r] = s
                self.fireTableRowsUpdated(r, r)


class SubFolderManagerDialog(object):
    """
    Interactive N-level Sub-folder Manager Dialog allowing the user to freely
    add, insert, rename, delete, or reorder an arbitrary number of sub-folder levels
    (1 level, 2 levels, 5 levels, 10 levels...).
    """

    def __init__(self, parent, current_path):
        self._result = None
        owner = SwingUtilities.getWindowAncestor(parent) if parent is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle("Quản lý các cấp Sub-folder (Thêm / Xóa / Sửa / Đổi thứ tự không giới hạn số cấp)")
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))

        self.model = _SubFolderTableModel(split_hierarchy_path(current_path))
        self.table = JTable(self.model)
        self.table.putClientProperty("terminateEditOnFocusLost", Boolean.TRUE)
        self.table.setRowHeight(24)
        self.table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.table.getColumnModel().getColumn(0).setPreferredWidth(70)
        self.table.getColumnModel().getColumn(1).setPreferredWidth(420)

        self.preview_label = JLabel("")
        self.preview_label.setFont(Font("Dialog", Font.BOLD, 12))
        self._update_preview()

        top_info = JPanel(BorderLayout(4, 4))
        top_info.setBorder(BorderFactory.createEmptyBorder(6, 8, 2, 8))
        top_info.add(JLabel("Bạn có thể tạo bao nhiêu cấp sub-folder tùy ý (1 cấp, 2 cấp, 5 cấp, 10 cấp...). "
                            "Click đúp vào tên cấp để sửa trực tiếp:"), BorderLayout.NORTH)
        top_info.add(self.preview_label, BorderLayout.SOUTH)
        self.dialog.add(top_info, BorderLayout.NORTH)

        center = JPanel(BorderLayout(4, 4))
        center.setBorder(BorderFactory.createEmptyBorder(4, 8, 4, 8))
        center.add(JScrollPane(self.table), BorderLayout.CENTER)

        side = JPanel(GridLayout(6, 1, 4, 4))
        side.add(JButton("+ Thêm cấp vào cuối", actionPerformed=self._on_append))
        side.add(JButton("+ Chèn cấp sau dòng chọn", actionPerformed=self._on_insert_after))
        side.add(JButton("✏ Sửa dòng đang chọn...", actionPerformed=self._on_rename))
        side.add(JButton("⬆ Đẩy lên trên", actionPerformed=lambda e: self._on_move(-1)))
        side.add(JButton("⬇ Đẩy xuống dưới", actionPerformed=lambda e: self._on_move(1)))
        side.add(JButton("🗑 Xóa cấp đang chọn", actionPerformed=self._on_delete))
        center.add(side, BorderLayout.EAST)
        self.dialog.add(center, BorderLayout.CENTER)

        btns = JPanel(FlowLayout(FlowLayout.RIGHT))
        btns.add(JButton("Lưu & Áp dụng Path", actionPerformed=self._on_save))
        btns.add(JButton("Hủy", actionPerformed=self._on_cancel))
        self.dialog.add(btns, BorderLayout.SOUTH)

        self.dialog.setSize(Dimension(680, 360))
        self.dialog.setLocationRelativeTo(owner)
        if self.model.getRowCount() > 0:
            self.table.setRowSelectionInterval(self.model.getRowCount() - 1, self.model.getRowCount() - 1)

    def _stop_edit(self):
        if self.table.isEditing():
            ed = self.table.getCellEditor()
            if ed is not None:
                ed.stopCellEditing()

    def _update_preview(self):
        path_str = normalize_hierarchy_path(self.model.segments)
        self.preview_label.setText("Đường dẫn (%d cấp):  %s" % (len(self.model.segments), path_str))

    def _on_append(self, event):
        self._stop_edit()
        name = JOptionPane.showInputDialog(
            self.dialog,
            "Nhập tên Sub-folder mới (có thể nhập nhiều cấp cách nhau bởi '>'):",
            "Subfolder_%d" % (len(self.model.segments) + 1))
        if name and u_text(name).strip():
            for p in split_hierarchy_path(name):
                self.model.segments.append(p)
            self.model.fireTableDataChanged()
            last = len(self.model.segments) - 1
            if last >= 0:
                self.table.setRowSelectionInterval(last, last)
            self._update_preview()

    def _on_insert_after(self, event):
        self._stop_edit()
        r = self.table.getSelectedRow()
        if r < 0:
            r = len(self.model.segments) - 1
        name = JOptionPane.showInputDialog(
            self.dialog, "Nhập tên Sub-folder chèn sau Cấp %d:" % (r + 1),
            "Subfolder_%d" % (r + 2))
        if name and u_text(name).strip():
            inserted = split_hierarchy_path(name)
            pos = max(0, min(len(self.model.segments), r + 1))
            self.model.segments = self.model.segments[:pos] + inserted + self.model.segments[pos:]
            self.model.fireTableDataChanged()
            self.table.setRowSelectionInterval(pos, pos)
            self._update_preview()

    def _on_rename(self, event):
        self._stop_edit()
        r = self.table.getSelectedRow()
        if r < 0 or r >= len(self.model.segments):
            return
        name = JOptionPane.showInputDialog(
            self.dialog, "Sửa tên cho Cấp %d:" % (r + 1), self.model.segments[r])
        if name and u_text(name).strip():
            self.model.segments[r] = u_text(name).strip()
            self.model.fireTableRowsUpdated(r, r)
            self._update_preview()

    def _on_move(self, delta):
        self._stop_edit()
        r = self.table.getSelectedRow()
        j = r + delta
        if 0 <= r < len(self.model.segments) and 0 <= j < len(self.model.segments):
            self.model.segments[r], self.model.segments[j] = self.model.segments[j], self.model.segments[r]
            self.model.fireTableDataChanged()
            self.table.setRowSelectionInterval(j, j)
            self._update_preview()

    def _on_delete(self, event):
        self._stop_edit()
        r = self.table.getSelectedRow()
        if r < 0 or r >= len(self.model.segments):
            return
        if len(self.model.segments) <= 1:
            JOptionPane.showMessageDialog(self.dialog, "Path cần ít nhất 1 cấp gốc.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        del self.model.segments[r]
        self.model.fireTableDataChanged()
        sel = min(r, len(self.model.segments) - 1)
        if sel >= 0:
            self.table.setRowSelectionInterval(sel, sel)
        self._update_preview()

    def _on_save(self, event):
        self._stop_edit()
        self._result = normalize_hierarchy_path(self.model.segments)
        self.dialog.dispose()

    def _on_cancel(self, event):
        self._result = None
        self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)
        return self._result


class _EditorController(IMessageEditorController):
    """Feeds the request/response viewers with the selected role result."""

    def __init__(self, ext):
        self._ext = ext

    def getHttpService(self):
        g, _ = self._ext.current_selection()
        return g.service if g is not None else None

    def getRequest(self):
        _, r = self._ext.current_selection()
        return r.request if r is not None else None

    def getResponse(self):
        _, r = self._ext.current_selection()
        return r.response if r is not None else None


class _TreeViewerController(IMessageEditorController):
    """Feeds the viewers under the 'Cây Sub-folder' tree with the entry selected in that tree."""

    def __init__(self, ext):
        self._ext = ext

    def _entry(self):
        return getattr(self._ext, "_tree_entry", None) or (None, None)

    def getHttpService(self):
        g, _ = self._entry()
        return g.service if g is not None else None

    def getRequest(self):
        _, r = self._entry()
        return r.request if r is not None else None

    def getResponse(self):
        _, r = self._entry()
        return r.response if r is not None else None


def tree_entry_for(kind, payload):
    """(group, result) shown under the tree: an API node shows its API gốc, a role node that role."""
    if kind == "GROUP" and payload is not None:
        return payload, getattr(payload, "orig_result", None)
    if kind in ("ORIG", "ROLE") and payload is not None:
        return payload[0], payload[1]
    return None, None


# =============================================================================
# Role editor panel & dialog (supports Header, Cookie Key, and JWT/Bearer rules)
# =============================================================================


FLAGGED_LEVELS = (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR)
_STT_TOKEN_RE = re.compile(r"\{stt\}[\s.\-:)\]]*")


def format_copy_line(template, stt, path, method="", url="", api="", endpoint=""):
    """
    'STT. path' line for one API, e.g. template '{stt}. {path}' -> '200. / > contact > button "send"'.
    Without an STT the '{stt}.' part (and the separator after it) disappears.
    """
    t = u_text(template or "{stt}. {path}")
    if stt is None or u_text(stt).strip() == "":
        t = _STT_TOKEN_RE.sub(u"", t)
    values = {"stt": u_text(stt if stt is not None else ""), "path": u_text(path), "method": u_text(method),
              "url": u_text(url), "api": u_text(api), "endpoint": u_text(endpoint)}
    out = t
    for key, value in values.items():
        out = out.replace(u"{%s}" % key, value)
    return out.strip()


def effective_role_states(all_roles, branch_path, branch_rules, overrides=None):
    """
    {role_name: enabled} for an API in `branch_path`: the role's global Enabled flag, overridden by
    branch rules (a deeper branch wins over its parents), overridden by the API's own rules.
    """
    state = dict([(r["name"], bool(r.get("enabled"))) for r in all_roles])
    rules = [r for r in (branch_rules or []) if hierarchy_matches_prefix(branch_path, r.get("prefix", ""))]
    rules.sort(key=lambda r: len(split_hierarchy_path(r.get("prefix", ""))))
    for rule in rules:
        for name, on in rule.get("roles", {}).items():
            if name in state:
                state[name] = bool(on)
    for name, on in (overrides or {}).items():
        if name in state:
            state[name] = bool(on)
    return state


def effective_roles(all_roles, branch_path, branch_rules, overrides=None):
    """Role dicts (with their global position in '_index') enabled for one API."""
    state = effective_role_states(all_roles, branch_path, branch_rules, overrides)
    out = []
    for i, r in enumerate(all_roles):
        if state.get(r["name"]):
            role = dict(r)
            role["_index"] = i
            out.append(role)
    return out


def role_names_in(groups):
    """[(role_name, number_of_APIs_having_it)] in role order, across the given API groups."""
    order = []
    counts = {}
    for g in groups:
        for r in g.results:
            if r.role_name not in counts:
                counts[r.role_name] = 0
                order.append((r.role_index, len(order), r.role_name))
            counts[r.role_name] += 1
    order.sort()
    return [(name, counts[name]) for _, _, name in order]


def select_push_targets(group, include_original, role_names, only_flagged=False):
    """Entries of one API to push / send: optionally the original, then the chosen roles."""
    out = [group.orig_result] if include_original else []
    for r in group.results:
        if r.role_name not in role_names:
            continue
        if only_flagged and (getattr(r, "_audit_level", None) or evaluate_role_result(group, r)[0]) not in FLAGGED_LEVELS:
            continue
        out.append(r)
    return out


def branch_prefix_counts(groups):
    """[(branch_path, number_of_APIs_inside)] for every branch level that holds captured APIs."""
    counts = {}
    for g in groups:
        parts = split_hierarchy_path(g.feature_name)
        for i in range(1, len(parts) + 1):
            key = normalize_hierarchy_path(parts[:i])
            counts[key] = counts.get(key, 0) + 1
    return sorted(counts.items(), key=lambda kv: [p.lower() for p in split_hierarchy_path(kv[0])])


def role_scope_preview(all_roles, groups, branch_rules, role_names, enable, scope, targets):
    """
    (APIs whose role set would change, role rows added, role rows removed) if the rule were applied -
    shown in the dialog before anything is changed.
    """
    role_names = set(role_names)
    targets = list(targets or [])
    rules = [dict(r, roles=dict(r["roles"])) for r in branch_rules or []]
    roles = [dict(r) for r in all_roles]
    if scope == "global":
        for r in roles:
            if r["name"] in role_names:
                r["enabled"] = bool(enable)
        affected = list(groups)
    elif scope == "branch":
        for prefix in targets:
            clean = normalize_hierarchy_path(prefix)
            rule = None
            for r in rules:
                if r["prefix"].lower() == clean.lower():
                    rule = r
            if rule is None:
                rule = {"prefix": clean, "roles": {}}
                rules.append(rule)
            for name in role_names:
                rule["roles"][name] = bool(enable)
        affected = [g for g in groups if any([hierarchy_matches_prefix(g.feature_name, t) for t in targets])]
    else:
        affected = targets
    changed = added = removed = 0
    for g in affected:
        overrides = dict(getattr(g, "role_overrides", {}) or {})
        if scope == "api":
            for name in role_names:
                overrides[name] = bool(enable)
        before = set([r.role_key or r.role_name for r in g.results])
        after = set([r["name"] for r in effective_roles(roles, g.feature_name, rules, overrides)])
        if before != after:
            changed += 1
            added += len(after - before)
            removed += len(before - after)
    return changed, added, removed


class _DocChange(DocumentListener):
    def __init__(self, fn):
        self._fn = fn

    def insertUpdate(self, e):
        self._fn()

    def removeUpdate(self, e):
        self._fn()

    def changedUpdate(self, e):
        self._fn()


class _CheckList(JPanel):
    """Filterable list of check boxes; the checked state survives filtering."""

    def __init__(self, items, checked, on_change, hint="Lọc..."):
        JPanel.__init__(self, BorderLayout(2, 2))
        self._items = list(items)            # [(key, label)]
        self._checked = set(checked)
        self._on_change = on_change
        top = JPanel(BorderLayout(4, 2))
        row = JPanel(BorderLayout(4, 0))
        row.add(JLabel(" Lọc:"), BorderLayout.WEST)
        self.filter = JTextField()
        self.filter.setToolTipText(hint)
        self.filter.getDocument().addDocumentListener(_DocChange(self._rebuild))
        row.add(self.filter, BorderLayout.CENTER)
        top.add(row, BorderLayout.NORTH)
        quick = JPanel(FlowLayout(FlowLayout.LEFT, 2, 0))
        quick.add(JButton("Chọn các mục đang hiện", actionPerformed=lambda e: self._set_visible(True)))
        quick.add(JButton("Bỏ chọn hết", actionPerformed=lambda e: self._clear()))
        top.add(quick, BorderLayout.SOUTH)
        self.add(top, BorderLayout.NORTH)
        self._box = JPanel()
        self._box.setLayout(BoxLayout(self._box, BoxLayout.Y_AXIS))
        scroll = JScrollPane(self._box)
        scroll.getVerticalScrollBar().setUnitIncrement(16)
        self.add(scroll, BorderLayout.CENTER)
        self._visible = []
        self._rebuild()

    def _rebuild(self):
        text = u_text(self.filter.getText()).strip().lower()
        self._box.removeAll()
        self._visible = []
        shown = 0
        for key, label in self._items:
            if text and text not in u_text(label).lower():
                continue
            shown += 1
            if shown > 600:
                more = JLabel("   ... còn nữa - gõ thêm vào ô lọc để thu hẹp")
                self._box.add(more)
                break
            box = JCheckBox(label, key in self._checked)
            box.addActionListener(_Action(lambda e, k=key, b=box: self._toggle(k, b)))
            self._box.add(box)
            self._visible.append(key)
        if not self._items:
            self._box.add(JLabel("   (chưa có mục nào)"))
        self._box.revalidate()
        self._box.repaint()

    def _toggle(self, key, box):
        if box.isSelected():
            self._checked.add(key)
        else:
            self._checked.discard(key)
        self._on_change()

    def _set_visible(self, on):
        for key in self._visible:
            if on:
                self._checked.add(key)
            else:
                self._checked.discard(key)
        self._rebuild()
        self._on_change()

    def _clear(self):
        self._checked = set()
        self._rebuild()
        self._on_change()

    def checked(self):
        return [k for k, _ in self._items if k in self._checked]


class RoleScopeDialog(object):
    """
    'Bật / Tắt Role theo phạm vi': choose Tắt / Bật, which roles, and where - every API (the
    roles' own Enabled flag), selected branches (sub-branches included, also for APIs captured later)
    or selected APIs only. Lists the branch exceptions already set and previews the change.
    Role requests stay virtual: they are only built when viewed / sent / pushed.
    """

    SCOPES = (("global", "🌐 Toàn bộ (cờ Enabled của role - mọi API)"),
              ("branch", "🌿 Chỉ các nhánh chọn bên dưới (gồm nhánh con, cả API bắt sau này)"),
              ("api", "📌 Chỉ các API gốc chọn bên dưới"))

    def __init__(self, ext, preset):
        self.ext = ext
        self._result = None
        self._groups = ext.group_model.all_groups() if ext.group_model is not None else []
        owner = SwingUtilities.getWindowAncestor(ext.main_panel) if ext.main_panel is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle("Bật / Tắt Role theo phạm vi")
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))
        bg, fg = _ui_colors()
        self._pal = RowPalette.of(bg, fg)

        head = JPanel()
        head.setLayout(BoxLayout(head, BoxLayout.Y_AXIS))
        head.setBorder(BorderFactory.createEmptyBorder(8, 10, 2, 10))
        acts = JPanel(FlowLayout(FlowLayout.LEFT, 6, 0))
        acts.add(JLabel("Thao tác:"))
        enable = bool(preset.get("enable", False))
        self.rb_off = JRadioButton("⬜ TẮT role", not enable)
        self.rb_on = JRadioButton("✅ BẬT role", enable)
        g1 = ButtonGroup()
        for rb in (self.rb_off, self.rb_on):
            g1.add(rb)
            rb.addActionListener(_Action(lambda e: self._update()))
            acts.add(rb)
        acts.setAlignmentX(0.0)
        head.add(acts)
        scopes = JPanel(FlowLayout(FlowLayout.LEFT, 6, 0))
        scopes.add(JLabel("Phạm vi:"))
        self.scope_buttons = []
        g2 = ButtonGroup()
        for key, label in self.SCOPES:
            rb = JRadioButton(label, key == preset.get("scope", "global"))
            g2.add(rb)
            rb.addActionListener(_Action(lambda e: self._on_scope()))
            scopes.add(rb)
            self.scope_buttons.append((key, rb))
        scopes.setAlignmentX(0.0)
        head.add(scopes)
        self.dialog.add(head, BorderLayout.NORTH)

        roles = ext.roles.all()
        chosen = preset.get("roles")
        role_items = [(r["name"], "%s   %s" % (r["name"], "(đang bật)" if r.get("enabled") else "(đang tắt)"))
                      for r in roles]
        self.role_list = _CheckList(role_items, chosen if chosen is not None else [r["name"] for r in roles],
                                    self._update, "Lọc role theo tên")
        self.role_list.setBorder(BorderFactory.createTitledBorder("1. Role áp dụng"))
        self.role_list.setPreferredSize(Dimension(250, 300))

        branch_items = [(prefix, "%s   (%d API)" % (prefix, n)) for prefix, n in branch_prefix_counts(self._groups)]
        known = set([k for k, _ in branch_items])
        for r in ext.role_branch_rules:
            if r["prefix"] not in known:
                branch_items.append((r["prefix"], "%s   (chưa có API)" % r["prefix"]))
        self.branch_list = _CheckList(branch_items, preset.get("branches", []), self._update,
                                      "Lọc nhánh, vd: contact")
        api_items = [(g.gid, "#%d  %s %s   ·   %s" % (g.gid, g.method, strip_query(g.path), g.feature_name))
                     for g in sorted(self._groups, key=lambda x: x.gid)]
        self.api_list = _CheckList(api_items, preset.get("apis", []), self._update, "Lọc API theo #, method, path, nhánh")
        self.target_tabs = JTabbedPane()
        self.target_tabs.addTab("Nhánh", self.branch_list)
        self.target_tabs.addTab("API gốc", self.api_list)
        self.target_tabs.addTab("Ngoại lệ đã đặt", self._build_rules_panel())
        self.target_tabs.setBorder(BorderFactory.createTitledBorder("2. Nhánh / API (khi phạm vi không phải Toàn bộ)"))
        split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, self.role_list, self.target_tabs)
        split.setResizeWeight(0.3)
        self.dialog.add(split, BorderLayout.CENTER)

        bottom = JPanel(BorderLayout(4, 4))
        bottom.setBorder(BorderFactory.createEmptyBorder(4, 10, 8, 10))
        self.cb_existing = JCheckBox("Cập nhật luôn các API đã bắt (dòng role của role đang bật giữ nguyên kết quả "
                                     "đã nhận). Bỏ chọn = chỉ áp dụng cho API bắt sau này.",
                                     bool(preset.get("apply_existing", True)))
        self.cb_existing.addActionListener(_Action(lambda e: self._update()))
        bottom.add(self.cb_existing, BorderLayout.NORTH)
        self.lbl_summary = JLabel(" ")
        self.lbl_summary.setFont(self.lbl_summary.getFont().deriveFont(Font.BOLD))
        bottom.add(self.lbl_summary, BorderLayout.CENTER)
        btns = JPanel(FlowLayout(FlowLayout.RIGHT, 6, 0))
        self.btn_ok = JButton("Áp dụng", actionPerformed=self._on_ok)
        self.btn_ok.setFont(self.btn_ok.getFont().deriveFont(Font.BOLD))
        btns.add(self.btn_ok)
        btns.add(JButton("Đóng", actionPerformed=lambda e: self.dialog.dispose()))
        bottom.add(btns, BorderLayout.EAST)
        self.dialog.add(bottom, BorderLayout.SOUTH)
        self.dialog.setSize(Dimension(1040, 620))
        self.dialog.setLocationRelativeTo(owner)
        self._on_scope()

    def _build_rules_panel(self):
        panel = JPanel(BorderLayout(4, 4))
        self._rules_box = JPanel()
        self._rules_box.setLayout(BoxLayout(self._rules_box, BoxLayout.Y_AXIS))
        scroll = JScrollPane(self._rules_box)
        scroll.getVerticalScrollBar().setUnitIncrement(16)
        panel.add(scroll, BorderLayout.CENTER)
        hint = JLabel(" Thứ tự ưu tiên: cờ Enabled toàn bộ  →  nhánh (nhánh sâu hơn thắng)  →  từng API.")
        hint.setForeground(self._pal.muted)
        panel.add(hint, BorderLayout.SOUTH)
        self._fill_rules()
        return panel

    def _fill_rules(self):
        box = self._rules_box
        box.removeAll()
        ext = self.ext
        rules = sorted(ext.role_branch_rules, key=lambda r: r["prefix"].lower())
        api_over = [g for g in self._groups if getattr(g, "role_overrides", None)]
        if not rules and not api_over:
            box.add(JLabel("   Chưa có ngoại lệ - mọi API dùng cờ Enabled của từng role."))
        for r in rules:
            row = JPanel(FlowLayout(FlowLayout.LEFT, 4, 0))
            offs = sorted([n for n, on in r["roles"].items() if not on])
            ons = sorted([n for n, on in r["roles"].items() if on])
            row.add(JButton("✖", actionPerformed=lambda e, p=r["prefix"]: self._remove_rule(p)))
            row.add(JLabel("🌿 %s   %s%s" % (r["prefix"], ("TẮT: " + ", ".join(offs)) if offs else "",
                                             ("   BẬT: " + ", ".join(ons)) if ons else "")))
            row.setAlignmentX(0.0)
            box.add(row)
        for g in api_over:
            row = JPanel(FlowLayout(FlowLayout.LEFT, 4, 0))
            offs = sorted([n for n, on in g.role_overrides.items() if not on])
            ons = sorted([n for n, on in g.role_overrides.items() if on])
            row.add(JButton("✖", actionPerformed=lambda e, grp=g: self._remove_override(grp)))
            row.add(JLabel("📌 #%d %s %s   %s%s" % (g.gid, g.method, strip_query(g.path),
                                                  ("TẮT: " + ", ".join(offs)) if offs else "",
                                                  ("   BẬT: " + ", ".join(ons)) if ons else "")))
            row.setAlignmentX(0.0)
            box.add(row)
        box.revalidate()
        box.repaint()

    def _remove_rule(self, prefix):
        self.ext.remove_branch_rule(prefix, self.cb_existing.isSelected())
        self._fill_rules()
        self._update()

    def _remove_override(self, group):
        group.role_overrides = {}
        if self.cb_existing.isSelected():
            self.ext.sync_group_roles(group)
        self._fill_rules()
        self._update()

    def scope(self):
        for key, rb in self.scope_buttons:
            if rb.isSelected():
                return key
        return "global"

    def _on_scope(self):
        sc = self.scope()
        self.target_tabs.setEnabled(True)
        if sc == "branch":
            self.target_tabs.setSelectedIndex(0)
        elif sc == "api":
            self.target_tabs.setSelectedIndex(1)
        self._update()

    def choice(self):
        sc = self.scope()
        if sc == "branch":
            targets = self.branch_list.checked()
        elif sc == "api":
            wanted = set(self.api_list.checked())
            targets = [g for g in self._groups if g.gid in wanted]
        else:
            targets = None
        return {"enable": self.rb_on.isSelected(), "roles": self.role_list.checked(), "scope": sc,
                "targets": targets, "apply_existing": self.cb_existing.isSelected() or sc == "api"}

    def _update(self):
        c = self.choice()
        verb = "BẬT" if c["enable"] else "TẮT"
        if not c["roles"]:
            msg, ok = "Chọn ít nhất 1 role.", False
        elif c["scope"] != "global" and not c["targets"]:
            msg, ok = "Chọn ít nhất 1 %s ở khung bên phải." % ("nhánh" if c["scope"] == "branch" else "API"), False
        else:
            ok = True
            where = {"global": "mọi API", "branch": "%d nhánh" % len(c["targets"] or []),
                     "api": "%d API" % len(c["targets"] or [])}[c["scope"]]
            msg = "%s %d role cho %s" % (verb, len(c["roles"]), where)
            if c["apply_existing"]:
                changed, added, removed = role_scope_preview(
                    self.ext.roles.all(), self._groups, self.ext.role_branch_rules, c["roles"], c["enable"],
                    c["scope"], c["targets"])
                msg += "  ·  %d API đã bắt thay đổi (+%d / -%d dòng role)" % (changed, added, removed)
            else:
                msg += "  ·  chỉ áp dụng cho API bắt sau này"
        self.lbl_summary.setText(msg)
        self.btn_ok.setEnabled(ok)
        self.cb_existing.setEnabled(c["scope"] != "api")

    def _on_ok(self, e):
        self._result = self.choice()
        self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)
        return self._result


class PushTargetsDialog(object):
    """
    'Đẩy / Gửi có chọn Role': for one API, several APIs or a whole branch, choose the action
    (push to Burp Repeater / send), the API gốc and any subset of roles, an optional
    'only failing / diverging roles' filter and the Repeater tab naming. Shows how many tabs /
    requests that makes before running, and remembers the last choice.
    """

    def __init__(self, parent, groups, scope_label, memory, action):
        self._groups = list(groups)
        self._result = None
        owner = SwingUtilities.getWindowAncestor(parent) if parent is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle("Đẩy / Gửi có chọn Role - %s" % scope_label)
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))
        bg, fg = _ui_colors()
        pal = RowPalette.of(bg, fg)

        head = JPanel(BorderLayout(4, 4))
        head.setBorder(BorderFactory.createEmptyBorder(8, 10, 2, 10))
        branches = len(set([g.feature_name for g in self._groups]))
        info = JLabel("%s  ·  %d API  ·  %d nhánh" % (scope_label, len(self._groups), branches))
        info.setFont(info.getFont().deriveFont(Font.BOLD))
        head.add(info, BorderLayout.NORTH)
        actions = JPanel(FlowLayout(FlowLayout.LEFT, 6, 0))
        self.rb_push = JRadioButton("📤 Đẩy sang Burp Repeater", action != "send")
        self.rb_send = JRadioButton("▶ Gửi request (hàng đợi chống 429)", action == "send")
        grp = ButtonGroup()
        grp.add(self.rb_push)
        grp.add(self.rb_send)
        for rb in (self.rb_push, self.rb_send):
            rb.addActionListener(_Action(lambda e: self._update()))
            actions.add(rb)
        head.add(actions, BorderLayout.SOUTH)
        self.dialog.add(head, BorderLayout.NORTH)

        listing = JPanel()
        listing.setLayout(BoxLayout(listing, BoxLayout.Y_AXIS))
        listing.setBorder(BorderFactory.createEmptyBorder(4, 8, 4, 8))
        self.cb_orig = JCheckBox("📌 API GỐC (Acc Crawl) - request đã bắt, áp profile API gốc nếu bật",
                                 bool(memory.get("orig", False)))
        self.cb_orig.setFont(self.cb_orig.getFont().deriveFont(Font.BOLD))
        self.cb_orig.setForeground(pal.orig_fg)
        self.cb_orig.addActionListener(_Action(lambda e: self._update()))
        listing.add(self.cb_orig)
        listing.add(Box.createVerticalStrut(4))
        self.role_boxes = []
        unchecked = set(memory.get("unchecked", []))
        names = role_names_in(self._groups)
        if not names:
            none = JLabel("   (Các API này không có role nào - chỉ có thể đẩy / gửi API gốc)")
            none.setForeground(pal.muted)
            listing.add(none)
        for name, count in names:
            box = JCheckBox("%s      (có ở %d/%d API)" % (name, count, len(self._groups)), name not in unchecked)
            box.addActionListener(_Action(lambda e: self._update()))
            self.role_boxes.append((name, box))
            listing.add(box)
        scroll = JScrollPane(listing)
        scroll.setBorder(BorderFactory.createTitledBorder("Đối tượng (API gốc và / hoặc các Role)"))
        scroll.getVerticalScrollBar().setUnitIncrement(16)

        quick = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        for label, fn in (("Tất cả", self._all), ("Chỉ API gốc", self._only_orig), ("Chỉ các Role", self._only_roles),
                          ("Bỏ chọn hết", self._none), ("Đảo chọn", self._invert)):
            quick.add(JButton(label, actionPerformed=fn))
        options = JPanel()
        options.setLayout(BoxLayout(options, BoxLayout.Y_AXIS))
        options.setBorder(BorderFactory.createEmptyBorder(2, 8, 2, 8))
        self.cb_flagged = JCheckBox("Chỉ lấy role đang Lỗi / Lệch / Nghi bypass (Vàng / Cam / Đỏ) ở từng API",
                                    bool(memory.get("only_flagged", False)))
        self.cb_flagged.addActionListener(_Action(lambda e: self._update()))
        self.rb_compact = JRadioButton("Tên tab gọn: G01•01_Admin (+ copy tên Group vào clipboard)",
                                       memory.get("compact", True))
        self.rb_full = JRadioButton("Tên tab đầy đủ: [G01:METHOD /path] 01_Admin", not memory.get("compact", True))
        naming = ButtonGroup()
        naming.add(self.rb_compact)
        naming.add(self.rb_full)
        for c in (self.cb_flagged, self.rb_compact, self.rb_full):
            c.setAlignmentX(0.0)
            options.add(c)
        center = JPanel(BorderLayout(4, 4))
        center.add(quick, BorderLayout.NORTH)
        center.add(scroll, BorderLayout.CENTER)
        center.add(options, BorderLayout.SOUTH)
        self.dialog.add(center, BorderLayout.CENTER)

        bottom = JPanel(BorderLayout())
        bottom.setBorder(BorderFactory.createEmptyBorder(4, 10, 8, 10))
        self.lbl_summary = JLabel(" ")
        self.lbl_summary.setFont(self.lbl_summary.getFont().deriveFont(Font.BOLD))
        bottom.add(self.lbl_summary, BorderLayout.CENTER)
        btns = JPanel(FlowLayout(FlowLayout.RIGHT, 6, 0))
        self.btn_ok = JButton("Thực hiện", actionPerformed=self._on_ok)
        self.btn_ok.setFont(self.btn_ok.getFont().deriveFont(Font.BOLD))
        btns.add(self.btn_ok)
        btns.add(JButton("Hủy", actionPerformed=lambda e: self.dialog.dispose()))
        bottom.add(btns, BorderLayout.EAST)
        self.dialog.add(bottom, BorderLayout.SOUTH)
        self.dialog.setSize(Dimension(720, 560))
        self.dialog.setLocationRelativeTo(owner)
        self._update()

    def _set_all(self, orig, roles):
        self.cb_orig.setSelected(orig)
        for _, box in self.role_boxes:
            box.setSelected(roles)
        self._update()

    def _all(self, e):
        self._set_all(True, True)

    def _only_orig(self, e):
        self._set_all(True, False)

    def _only_roles(self, e):
        self._set_all(False, True)

    def _none(self, e):
        self._set_all(False, False)

    def _invert(self, e):
        self.cb_orig.setSelected(not self.cb_orig.isSelected())
        for _, box in self.role_boxes:
            box.setSelected(not box.isSelected())
        self._update()

    def choice(self):
        names = set([n for n, box in self.role_boxes if box.isSelected()])
        return {
            "action": "send" if self.rb_send.isSelected() else "push",
            "orig": self.cb_orig.isSelected(),
            "roles": names,
            "unchecked": [n for n, box in self.role_boxes if not box.isSelected()],
            "only_flagged": self.cb_flagged.isSelected(),
            "compact": self.rb_compact.isSelected(),
        }

    def _update(self):
        c = self.choice()
        total = 0
        apis = 0
        for g in self._groups:
            n = len(select_push_targets(g, c["orig"], c["roles"], c["only_flagged"]))
            total += n
            apis += 1 if n else 0
        verb = "Sẽ gửi %d request" if c["action"] == "send" else "Sẽ tạo %d tab Repeater"
        self.lbl_summary.setText((verb % total) + " cho %d / %d API" % (apis, len(self._groups)))
        self.btn_ok.setEnabled(total > 0)
        self.rb_compact.setEnabled(c["action"] == "push")
        self.rb_full.setEnabled(c["action"] == "push")

    def _on_ok(self, e):
        self._result = self.choice()
        self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)
        return self._result


MODE_HINTS = [
    (MODE_REPLACE, "ghi đè hoặc thêm header"),
    (MODE_ADD, "thêm 1 dòng header mới"),
    (MODE_REMOVE, "xóa header"),
    (MODE_COOKIE_SET, "đặt / sửa 1 biến trong Cookie"),
    (MODE_COOKIE_REMOVE, "xóa 1 biến khỏi Cookie"),
    (REMOVE_TOKEN, "ghi vào ô Value = xóa"),
]


def _font_resized(font, style, delta):
    """font with `style`, `delta` points bigger/smaller (relative, so Burp's font size setting is kept)."""
    try:
        return font.deriveFont(style, float(font.getSize2D()) + delta)
    except (Exception, Throwable):
        return font.deriveFont(style)


def _ui_colors():
    bg = UIManager.getColor("Panel.background") or Color(242, 242, 242)
    fg = UIManager.getColor("Label.foreground") or Color(30, 30, 30)
    return bg, fg


def make_chip(text, fill, fg, edge):
    """Small opaque pill-shaped label (plain text: Burp disables HTML in extension labels)."""
    chip = JLabel(" %s " % text)
    chip.setOpaque(True)
    chip.setBackground(fill)
    chip.setForeground(fg)
    chip.setFont(chip.getFont().deriveFont(Font.BOLD))
    chip.setBorder(BorderFactory.createCompoundBorder(
        BorderFactory.createLineBorder(edge), BorderFactory.createEmptyBorder(1, 4, 1, 4)))
    return chip


def build_mode_legend():
    """Legend of the rule modes, laid out as 3 x 2 chips + descriptions."""
    bg, fg = _ui_colors()
    pal = RowPalette.of(bg, fg)
    panel = JPanel(BorderLayout(4, 4))
    panel.setBorder(BorderFactory.createEmptyBorder(6, 2, 4, 2))
    title = JLabel("Các chế độ (cột Mode):")
    title.setFont(title.getFont().deriveFont(Font.BOLD))
    panel.add(title, BorderLayout.NORTH)
    grid = JPanel(GridLayout(0, 3, 12, 4))
    for mode, hint in MODE_HINTS:
        fill, text, edge = pal.modes.get(mode, (pal.zebra[1], fg, pal.grid))
        cell = JPanel(FlowLayout(FlowLayout.LEFT, 5, 0))
        cell.add(make_chip(mode, fill, text, edge))
        desc = JLabel(hint)
        desc.setForeground(pal.muted)
        cell.add(desc)
        grid.add(cell)
    panel.add(grid, BorderLayout.CENTER)
    return panel


class ModeCellRenderer(DefaultTableCellRenderer):
    """Mode column of the rule table: bold text in the mode's colour."""

    def getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column):
        comp = DefaultTableCellRenderer.getTableCellRendererComponent(
            self, table, value, isSelected, hasFocus, row, column)
        comp.setFont(table.getFont().deriveFont(Font.BOLD))
        if not isSelected:
            pal = RowPalette.of(table.getBackground(), table.getForeground())
            colours = pal.modes.get(u_text(value).upper())
            comp.setBackground(colours[0] if colours else table.getBackground())
            comp.setForeground(colours[1] if colours else table.getForeground())
        return comp


class RoleEditorPanel(JPanel):
    """
    Reusable editor panel for a single role profile. Used both inline on the
    Roles tab and inside the modal RoleEditorDialog.
    """

    def __init__(self, role, inline_save_fn=None):
        JPanel.__init__(self, BorderLayout(6, 6))
        self._inline_save_fn = inline_save_fn
        self.setBorder(BorderFactory.createEmptyBorder(6, 6, 6, 6))

        top = JPanel(GridBagLayout())
        gc = GridBagConstraints()
        gc.insets = Insets(3, 3, 3, 3)
        gc.anchor = GridBagConstraints.WEST
        gc.gridx = 0
        gc.gridy = 0
        top.add(JLabel("Role Name:"), gc)
        gc.gridx = 1
        gc.fill = GridBagConstraints.HORIZONTAL
        gc.weightx = 1.0
        self.name_field = JTextField(role.get("name", ""), 26)
        top.add(self.name_field, gc)
        gc.gridx = 2
        gc.weightx = 0.0
        gc.fill = GridBagConstraints.NONE
        self.enabled_box = JCheckBox("Enabled", bool(role.get("enabled", True)))
        top.add(self.enabled_box, gc)
        if inline_save_fn is not None:
            gc.gridx = 3
            self.save_btn = JButton("Save Profile Changes", actionPerformed=self._on_inline_save)
            top.add(self.save_btn, gc)
            gc.gridx = 4
            self.dirty_label = JLabel(" ")
            self.dirty_label.setForeground(Color(0, 130, 0))
            top.add(self.dirty_label, gc)
        else:
            self.dirty_label = None
        self.add(top, BorderLayout.NORTH)

        self.model = HeaderRuleTableModel(role.get("headers", []), on_change=self._refresh_jwt_preview)
        self.table = JTable(self.model)
        self.table.putClientProperty("terminateEditOnFocusLost", Boolean.TRUE)
        cm = self.table.getColumnModel()
        cm.getColumn(2).setCellEditor(DefaultCellEditor(JComboBox(HEADER_MODES)))
        cm.getColumn(2).setCellRenderer(ModeCellRenderer())
        self.table.setRowHeight(24)
        cm.getColumn(0).setPreferredWidth(180)
        cm.getColumn(1).setPreferredWidth(420)
        cm.getColumn(2).setPreferredWidth(130)

        self.jwt_area = JTextArea(5, 50)
        self.jwt_area.setEditable(False)
        self.jwt_area.setFont(Font("Monospaced", Font.PLAIN, 11))
        jwt_panel = JPanel(BorderLayout())
        jwt_panel.add(JLabel(" JWT / Token Inspector (auto-decodes any eyJ... token in this profile):"),
                      BorderLayout.NORTH)
        jwt_panel.add(JScrollPane(self.jwt_area), BorderLayout.CENTER)

        split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.table), jwt_panel)
        split.setResizeWeight(0.68)

        center = JPanel(BorderLayout(4, 4))
        center.add(split, BorderLayout.CENTER)
        center.add(build_mode_legend(), BorderLayout.SOUTH)
        self.add(center, BorderLayout.CENTER)

        toolbar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        toolbar.add(JButton("+ Header", actionPerformed=self._on_add_header))
        toolbar.add(JButton("+ Strip Header ([REMOVE])", actionPerformed=self._on_strip_header))
        toolbar.add(JButton("+ Set JWT / Bearer...", actionPerformed=self._on_set_jwt))
        toolbar.add(JButton("+ Set Cookie/Session Key...", actionPerformed=self._on_set_cookie))
        toolbar.add(JButton("+ Strip Cookie Key...", actionPerformed=self._on_strip_cookie))
        toolbar.add(JButton("Paste Headers...", actionPerformed=self._on_bulk_headers))
        toolbar.add(JButton("Paste Cookies...", actionPerformed=self._on_bulk_cookies))
        toolbar.add(JButton("Rule Up", actionPerformed=lambda e: self._on_move_rule(-1)))
        toolbar.add(JButton("Rule Down", actionPerformed=lambda e: self._on_move_rule(1)))
        toolbar.add(JButton("Remove Rule(s)", actionPerformed=self._on_remove))
        self.add(toolbar, BorderLayout.SOUTH)
        self._refresh_jwt_preview()

    def set_original_mode(self, original):
        """Editing the API gốc profile: fixed name, the checkbox means 'apply to the original'."""
        self.name_field.setEditable(not original)
        self.enabled_box.setText("Áp dụng profile này cho API gốc" if original else "Enabled")

    def load_role(self, role):
        self.stop_editing()
        if role is None:
            self.name_field.setText("")
            self.enabled_box.setSelected(True)
            self.model.set_rules([])
            if self.dirty_label is not None:
                self.dirty_label.setText(" ")
            return
        self.name_field.setText(role.get("name", ""))
        self.enabled_box.setSelected(bool(role.get("enabled", True)))
        self.model.set_rules(role.get("headers", []))
        if self.dirty_label is not None:
            self.dirty_label.setText(" ")

    def stop_editing(self):
        if self.table.isEditing():
            self.table.getCellEditor().stopCellEditing()

    def _refresh_jwt_preview(self):
        vals = "\n".join([r.get("value", "") for r in self.model.rules])
        self.jwt_area.setText(decode_jwt_preview(vals))
        self.jwt_area.setCaretPosition(0)

    def build_validated_role(self):
        self.stop_editing()
        name = self.name_field.getText().strip()
        if not name:
            JOptionPane.showMessageDialog(self, "Role name is required.", EXT_NAME,
                                          JOptionPane.WARNING_MESSAGE)
            return None
        bad = [r.get("name", "") for r in self.model.rules if not sanitize_header_name(r.get("name"))]
        if bad:
            JOptionPane.showMessageDialog(
                self, "Invalid header/cookie name(s): %s\n(no spaces, colons or line breaks)"
                % ", ".join(["'%s'" % b for b in bad]), EXT_NAME, JOptionPane.WARNING_MESSAGE)
            return None
        return normalize_role({"name": name, "enabled": self.enabled_box.isSelected(),
                               "headers": self.model.rules})

    def _on_inline_save(self, event):
        if self._inline_save_fn is not None:
            role = self.build_validated_role()
            if role is not None:
                self._inline_save_fn(role)
                if self.dirty_label is not None:
                    self.dirty_label.setText("Saved!")

    def _select_last_row(self, edit_col=None):
        r = self.model.getRowCount() - 1
        if r >= 0:
            self.table.setRowSelectionInterval(r, r)
            if edit_col is not None:
                self.table.editCellAt(r, edit_col)

    def _on_add_header(self, event):
        self.stop_editing()
        self.model.add_rule({"name": "X-Role", "value": "", "mode": MODE_REPLACE})
        self._select_last_row(0)

    def _on_strip_header(self, event):
        self.stop_editing()
        hdr = JOptionPane.showInputDialog(self, "Header name to strip (e.g. Authorization, Cookie, X-Tenant-ID):",
                                          "Authorization")
        if hdr is not None and sanitize_header_name(hdr):
            self.model.add_rule({"name": sanitize_header_name(hdr), "value": REMOVE_TOKEN, "mode": MODE_REMOVE})
            self._select_last_row()

    def _on_set_jwt(self, event):
        self.stop_editing()
        p = JPanel(GridBagLayout())
        gc = GridBagConstraints()
        gc.insets = Insets(3, 3, 3, 3)
        gc.anchor = GridBagConstraints.WEST
        gc.fill = GridBagConstraints.HORIZONTAL
        hdr_field = JTextField("Authorization", 25)
        pfx_field = JTextField("Bearer", 12)
        tok_area = JTextArea(5, 45)
        tok_area.setLineWrap(True)
        gc.gridx, gc.gridy = 0, 0
        p.add(JLabel("Header Name:"), gc)
        gc.gridx = 1
        p.add(hdr_field, gc)
        gc.gridx, gc.gridy = 0, 1
        p.add(JLabel("Prefix (leave empty for raw token):"), gc)
        gc.gridx = 1
        p.add(pfx_field, gc)
        gc.gridx, gc.gridy = 0, 2
        gc.gridwidth = 2
        p.add(JLabel("JWT / Token value (or [REMOVE]):"), gc)
        gc.gridy = 3
        p.add(JScrollPane(tok_area), gc)
        res = JOptionPane.showConfirmDialog(self, p, "Set JWT / Bearer Token for Role",
                                            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)
        if res != JOptionPane.OK_OPTION:
            return
        hname = sanitize_header_name(hdr_field.getText()) or "Authorization"
        raw_tok = tok_area.getText().strip()
        val = format_jwt_bearer(raw_tok, pfx_field.getText())
        mode = MODE_REMOVE if val == REMOVE_TOKEN else MODE_REPLACE
        for i, r in enumerate(self.model.rules):
            if r.get("name", "").lower() == hname.lower() and r.get("mode") in (MODE_REPLACE, MODE_REMOVE):
                self.model.rules[i] = {"name": hname, "value": val, "mode": mode}
                self.model.fireTableDataChanged()
                self._refresh_jwt_preview()
                return
        self.model.add_rule({"name": hname, "value": val, "mode": mode})

    def _on_set_cookie(self, event):
        self.stop_editing()
        p = JPanel(GridBagLayout())
        gc = GridBagConstraints()
        gc.insets = Insets(3, 3, 3, 3)
        gc.anchor = GridBagConstraints.WEST
        gc.fill = GridBagConstraints.HORIZONTAL
        k_field = JTextField("JSESSIONID", 25)
        v_field = JTextField("", 35)
        gc.gridx, gc.gridy = 0, 0
        p.add(JLabel("Cookie / Session Key (e.g. JSESSIONID, session, token):"), gc)
        gc.gridx = 1
        p.add(k_field, gc)
        gc.gridx, gc.gridy = 0, 1
        p.add(JLabel("Cookie Value:"), gc)
        gc.gridx = 1
        p.add(v_field, gc)
        res = JOptionPane.showConfirmDialog(
            self, p, "Set Individual Cookie / Session Parameter (preserves other cookies)",
            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)
        if res == JOptionPane.OK_OPTION:
            cname = sanitize_header_name(k_field.getText())
            if cname:
                self.model.add_rule({"name": cname, "value": sanitize_header_value(v_field.getText()),
                                     "mode": MODE_COOKIE_SET})
                self._select_last_row()

    def _on_strip_cookie(self, event):
        self.stop_editing()
        cname = JOptionPane.showInputDialog(
            self, "Cookie key to strip from Cookie header (other cookies stay intact):", "JSESSIONID")
        if cname is not None and sanitize_header_name(cname):
            self.model.add_rule({"name": sanitize_header_name(cname), "value": REMOVE_TOKEN,
                                 "mode": MODE_COOKIE_REMOVE})
            self._select_last_row()

    def _on_move_rule(self, delta):
        self.stop_editing()
        r = self.table.getSelectedRow()
        if r >= 0:
            nr = self.model.move_rule(r, delta)
            self.table.setRowSelectionInterval(nr, nr)

    def _on_remove(self, event):
        self.stop_editing()
        self.model.remove_rows(list(self.table.getSelectedRows()))

    def _on_bulk_headers(self, event):
        self.stop_editing()
        area = JTextArea(12, 60)
        res = JOptionPane.showConfirmDialog(self, JScrollPane(area),
                                            "Paste HTTP headers, one 'Name: value' per line",
                                            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)
        if res == JOptionPane.OK_OPTION:
            for rule in parse_bulk_headers(area.getText()):
                self.model.add_rule(rule)

    def _on_bulk_cookies(self, event):
        self.stop_editing()
        area = JTextArea(8, 60)
        res = JOptionPane.showConfirmDialog(
            self, JScrollPane(area),
            "Paste 'Cookie: a=1; b=2' or 'a=1; b=2' (splits into individual COOKIE_SET rules)",
            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)
        if res == JOptionPane.OK_OPTION:
            for rule in parse_bulk_cookies(area.getText()):
                self.model.add_rule(rule)


class RoleEditorDialog(object):
    """Modal editor for one role. Call show() on the EDT; returns a role dict or None."""

    def __init__(self, parent, role, title):
        self._result = None
        owner = SwingUtilities.getWindowAncestor(parent) if parent is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle(title)
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))

        self.editor = RoleEditorPanel(role, inline_save_fn=None)
        self.dialog.add(self.editor, BorderLayout.CENTER)

        btns = JPanel(FlowLayout(FlowLayout.RIGHT))
        btns.add(JButton("Save", actionPerformed=self._on_save))
        btns.add(JButton("Cancel", actionPerformed=self._on_cancel))
        self.dialog.add(btns, BorderLayout.SOUTH)

        self.dialog.setSize(Dimension(940, 520))
        self.dialog.setLocationRelativeTo(owner)

    def _on_save(self, event):
        role = self.editor.build_validated_role()
        if role is not None:
            self._result = role
            self.dialog.dispose()

    def _on_cancel(self, event):
        self._result = None
        self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)
        return self._result


# =============================================================================
# Main extension
# =============================================================================


class BurpExtender(IBurpExtender, ITab, IHttpListener, IContextMenuFactory, IExtensionStateListener):

    # ------------------------------------------------------------------ setup
    def registerExtenderCallbacks(self, callbacks):
        self.callbacks = callbacks
        self.helpers = callbacks.getHelpers()
        callbacks.setExtensionName(EXT_NAME)

        self.roles = RoleStore()
        self._cfg_lock = threading.RLock()
        self._state_lock = threading.RLock()
        self._next_gid = 1
        self._next_fid = 2
        self._active_fid = 1
        self._features = [FeatureGroup(1, DEFAULT_HIERARCHY_PATH)]
        self._seen_keys = set()
        self._skipped_count = 0
        self._last_skip_reason = ""
        self._unloaded = False
        self._api_regex = None
        self._static_exts = set()
        self._ui_dirty = False
        self._last_ui_flush = 0.0
        self._active_sends = 0
        self.log_area = None
        self.main_panel = None
        self.status_label = None
        self.feature_model = None
        self.group_model = None
        self.result_model = None
        self.left_hierarchy_tree = None
        self.left_hierarchy_tree_model = None
        self.history_tree = None
        self.history_tree_model = None
        self.history_summary_area = None
        self.inline_role_editor = None
        self.group_path_editor_combo = None
        self._updating_feature_bar = False
        self.feature_table = None
        self.group_table = None
        self.result_table = None

        # Pending UI work, written by any thread and drained by the Swing timer (_ui_tick).
        self._ui_lock = threading.Lock()
        self._p_new = []
        self._p_dirty = {}
        self._p_done_res = set()
        self._p_structure = False
        self._p_status = False
        self._p_log = []
        self._ui_timer = None
        self._in_tick = False
        self._stats = None
        self._stale_stats = True
        self._stale_left = True
        self._stale_history = True
        self._tree_states = {"left": self._new_tree_state(), "history": self._new_tree_state(),
                             "log": self._new_tree_state(), "full": self._new_tree_state()}
        self._stale_log = True
        self._stale_full = True
        self._menu_tree = None
        self._scope_source = "table"
        self._push_memory = None
        self._tree_window = None
        self._main_window = None
        self.suite_root = None
        self._tree_entry = None
        self._log_lock = threading.Lock()
        self._log_system = deque(maxlen=LOG_SYSTEM_MAX)
        self._log_by_gid = {}
        self._send_ui_state = None
        self._restoring_tree = False
        self._restoring_feature_sel = False
        self._chips_path = None
        self._path_combo_state = None
        self._persist_failures = 0

        self._inline_target = ("role", 0)
        self.config = merge_config(self._load_json_setting(SETTINGS_KEY_CONFIG, {}))
        self.original_profile = self._load_original_profile()
        self.role_branch_rules = self._load_role_scopes()
        self.targets = None
        self._stale_coverage = True
        self.target_hits = TargetHitLog()
        self._hits_saved_at = 0.0
        self._seen_gid = {}
        try:
            raw_targets = callbacks.loadExtensionSetting(SETTINGS_KEY_TARGETS)
            if raw_targets:
                self.targets = TargetList.from_json(raw_targets)
                self.target_hits.load_json(callbacks.loadExtensionSetting(SETTINGS_KEY_TARGET_HITS),
                                           targets_signature(self.targets))
        except Exception as e:
            callbacks.printError("Could not load the stored Excel API list: %s" % u_text(e))
        regex_err = self._recompile_filters(self.config)
        try:
            stored_roles = self._load_json_setting(SETTINGS_KEY_ROLES, None)
            if isinstance(stored_roles, list) and len(stored_roles) > 0:
                self.roles.set_all([normalize_role(r, i) for i, r in enumerate(stored_roles)])
            else:
                self.roles.set_all(default_role_templates())
        except Exception as e:
            callbacks.printError("Could not load stored roles: %s" % u_text(e))

        self.capture_executor = Executors.newSingleThreadExecutor()
        self.send_executor = Executors.newFixedThreadPool(self.config["threads"])
        self.send_scheduler = Executors.newSingleThreadScheduledExecutor()
        self.dispatcher = SendDispatcher(self._run_job, self.send_executor, self.send_scheduler,
                                         self.get_config, self.log)

        callbacks.registerExtensionStateListener(self)
        # The UI is built and the tab registered before this method returns, so
        # getUiComponent() can never be asked for a panel that does not exist yet.
        self._init_ui()

        if regex_err:
            self.log("Stored API regex is invalid: %s" % u_text(regex_err))

    @staticmethod
    def _new_tree_state():
        return {"collapsed": set(), "expanded": set(), "next_ok": 0.0, "nodes": {}}

    def _build_error_fallback_panel(self, err_msg):
        panel = JPanel(BorderLayout())
        area = JTextArea(u_text(err_msg))
        area.setEditable(False)
        panel.add(JScrollPane(area), BorderLayout.CENTER)
        return panel

    def _init_ui(self):
        if self._unloaded:
            return
        ui_panel = None
        try:
            self._build_ui()
            ui_panel = self.main_panel
        except Throwable as t:
            msg = "Error building UI (Java): %s\n%s" % (u_text(t), u_text(traceback.format_exc()))
            self._print_error(msg)
            ui_panel = self._build_error_fallback_panel(msg)
        except Exception:
            msg = "Error building UI:\n%s" % u_text(traceback.format_exc())
            self._print_error(msg)
            ui_panel = self._build_error_fallback_panel(msg)
        if ui_panel is None:
            ui_panel = self._build_error_fallback_panel("Error building UI: main_panel was None.")
        self.main_panel = ui_panel

        try:
            self.callbacks.addSuiteTab(self)
            self.callbacks.printOutput("%s: tab '%s' registered." % (EXT_NAME, EXT_NAME))
        except Throwable as t:
            self._print_error("Error calling addSuiteTab (Java): %s\n%s" % (
                u_text(t), u_text(traceback.format_exc())))
        except Exception:
            self._print_error("Error calling addSuiteTab:\n%s" % u_text(traceback.format_exc()))

        try:
            self.callbacks.registerHttpListener(self)
            self.callbacks.registerContextMenuFactory(self)
        except Throwable as t:
            self._print_error("Error registering listeners (Java): %s\n%s" % (
                u_text(t), u_text(traceback.format_exc())))
        except Exception:
            self._print_error("Error registering listeners:\n%s" % u_text(traceback.format_exc()))

        self.log("%s %s loaded - %d role(s) configured." % (EXT_NAME, EXT_VERSION, self.roles.count()))
        HierarchyTreeRenderer.report = self._print_error
        self._ensure_tree_renderers()
        self._start_ui_timer()
        self._refresh_feature_views()
        self.update_status()

    def _print_error(self, msg):
        try:
            self.callbacks.printError(msg)
        except (Throwable, Exception):
            pass

    def _start_ui_timer(self):
        try:
            if self._ui_timer is not None:
                self._ui_timer.stop()
            timer = Timer(UI_TICK_MS, _Action(self._ui_tick))
            timer.setCoalesce(True)
            timer.start()
            self._ui_timer = timer
        except (Throwable, Exception):
            self._print_error("Could not start UI timer:\n%s" % u_text(traceback.format_exc()))

    def extensionUnloaded(self):
        self._unloaded = True
        try:
            self._save_hits(True)
        except (Throwable, Exception):
            pass
        for win in (self._tree_window, self._main_window):
            try:
                if win is not None:
                    win.dispose()
            except (Throwable, Exception):
                pass
        try:
            if self._ui_timer is not None:
                self._ui_timer.stop()
        except (Throwable, Exception):
            pass
        try:
            self.capture_executor.shutdownNow()
            self.send_executor.shutdownNow()
            self.send_scheduler.shutdownNow()
            self.capture_executor.awaitTermination(2, TimeUnit.SECONDS)
            self.send_executor.awaitTermination(2, TimeUnit.SECONDS)
        except Throwable:
            pass
        self.callbacks.printOutput("%s unloaded." % EXT_NAME)

    # ------------------------------------------------------------------ ITab
    def getTabCaption(self):
        return EXT_NAME

    def getUiComponent(self):
        # A fixed holder: the extension can move out into its own window and back without Burp noticing.
        if self.suite_root is None:
            self.suite_root = JPanel(BorderLayout())
            if self.main_panel is not None:
                self.suite_root.add(self.main_panel, BorderLayout.CENTER)
        return self.suite_root

    def _on_toggle_detach(self, event=None):
        if self._main_window is not None:
            self._attach_main()
        else:
            self._detach_main()

    def _detach_main(self):
        if self.main_panel is None or self._main_window is not None:
            return
        root = self.getUiComponent()
        frame = JFrame("%s %s" % (EXT_NAME, EXT_VERSION))
        frame.setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE)
        frame.addWindowListener(_WindowClosing(lambda: self._attach_main()))
        root.remove(self.main_panel)
        holder = JPanel(FlowLayout(FlowLayout.CENTER, 8, 60))
        holder.add(JLabel("%s đang mở ở cửa sổ riêng." % EXT_NAME))
        holder.add(JButton("Đưa cửa sổ lên trước", actionPerformed=lambda e: (frame.setState(JFrame.NORMAL),
                                                                               frame.toFront())))
        holder.add(JButton("Gắn lại vào tab", actionPerformed=lambda e: self._attach_main()))
        root.add(holder, BorderLayout.CENTER)
        root.revalidate()
        root.repaint()
        frame.getContentPane().add(self.main_panel)
        size = root.getSize()
        frame.setSize(Dimension(max(1100, size.width), max(760, size.height)))
        frame.setLocationRelativeTo(None)
        self._main_window = frame
        self.btn_detach.setText("🗗 Gắn lại vào tab Burp")
        frame.setVisible(True)
        self._ensure_tree_renderers()

    def _attach_main(self):
        frame = self._main_window
        if frame is None:
            return
        self._main_window = None
        frame.getContentPane().removeAll()
        frame.dispose()
        root = self.getUiComponent()
        root.removeAll()
        root.add(self.main_panel, BorderLayout.CENTER)
        root.revalidate()
        root.repaint()
        self.btn_detach.setText("🗗 Tách ra cửa sổ riêng")
        self._ensure_tree_renderers()

    # --------------------------------------------------------------- logging
    def log(self, msg, gid=None):
        """
        Thread-safe. `gid` files the line under that API in the Log tab (otherwise under
        'Hệ thống'). Lines are buffered and written (extension Output + Log tab) by the UI tick.
        """
        ts = time.strftime("%H:%M:%S")
        text = u_text(msg)
        entry = (ts, text, gid)
        if self._ui_timer is None:
            self._flush_log([entry])
            return
        with self._ui_lock:
            if len(self._p_log) < 5000:
                self._p_log.append(entry)

    def _flush_log(self, entries):
        try:
            self.callbacks.printOutput("\n".join(["[%s] %s" % (ts, text) for ts, text, _ in entries]))
        except (Throwable, Exception):
            pass
        with self._log_lock:
            for ts, text, gid in entries:
                if gid is None:
                    self._log_system.append((ts, text))
                else:
                    lines = self._log_by_gid.setdefault(gid, [])
                    lines.append((ts, text))
                    if len(lines) > LOG_PER_API_MAX:
                        del lines[:len(lines) - LOG_PER_API_MAX]
        self._stale_log = True

    # ------------------------------------------------------------ UI refresh
    def _mark(self, structure=False, status=False):
        with self._ui_lock:
            if structure:
                self._p_structure = True
            if status:
                self._p_status = True

    def _ui_pending(self):
        with self._ui_lock:
            return bool(self._p_new or self._p_dirty or self._p_structure or self._p_status or self._p_log)

    def _ui_tick(self, event=None):
        """
        The ONLY place that pushes captured/replayed data into Swing. The timer calls it
        every UI_TICK_MS; user actions on the EDT call it directly (event=None) so their
        effect is immediate and not throttled.
        """
        if self._unloaded or self._in_tick:
            return
        self._in_tick = True
        try:
            self._ui_tick_body(force=(event is None))
        except Throwable as t:
            self._print_error("UI refresh error (Java): %s\n%s" % (u_text(t), u_text(traceback.format_exc())))
        except Exception:
            self._print_error("UI refresh error:\n%s" % u_text(traceback.format_exc()))
        finally:
            self._in_tick = False

    def _ui_tick_body(self, force):
        with self._ui_lock:
            new_groups, self._p_new = self._p_new, []
            dirty, self._p_dirty = self._p_dirty, {}
            done_res, self._p_done_res = self._p_done_res, set()
            structure, self._p_structure = self._p_structure, False
            status, self._p_status = self._p_status, False
            lines, self._p_log = self._p_log, []
        if lines:
            self._flush_log(lines)
        self._save_hits()
        if self.group_model is None or self.group_table is None:
            return
        total = self.target_hits.total()
        if total != getattr(self, "_hits_seen_total", 0):
            self._hits_seen_total = total
            self.group_table.repaint()
        self._ensure_tree_renderers()
        if new_groups:
            self.group_model.add_many(new_groups)
            if self.group_table.getSelectedRow() < 0 and self.group_table.getRowCount() > 0:
                self.group_table.setRowSelectionInterval(0, 0)
            structure = True
        if dirty:
            self._apply_dirty_groups(dirty, done_res)
            structure = True
        if structure:
            self._stale_stats = True
            self._stale_left = True
            self._stale_history = True
            self._stale_log = True
            self._stale_coverage = True
            self._stale_full = True
        self._refresh_send_controls()
        self._refresh_stale_views(force)
        if dirty:
            self._refresh_tree_entry()
        if status or structure:
            self._do_update_status()

    def _ensure_tree_renderers(self):
        """
        Burp's customizeUiComponent (and theme switches) can replace a JTree's cell renderer with
        Burp's own, which drops the level colours. Put ours back whenever that happens.
        """
        for name in ("left_hierarchy_tree", "history_tree", "log_tree", "full_tree"):
            tree = getattr(self, name, None)
            if tree is None:
                continue
            try:
                if not isinstance(tree.getCellRenderer(), HierarchyTreeRenderer):
                    tree.setCellRenderer(HierarchyTreeRenderer())
                    tree.setRowHeight(26)
            except (Exception, Throwable):
                pass

    def _apply_dirty_groups(self, dirty, done_res):
        cur = self.result_model.group()
        view_rebuilt = False
        for g in dirty.values():
            if not self.group_model.refresh_group(g):
                view_rebuilt = True
        if view_rebuilt and cur is not None and self.group_table.getSelectedRow() < 0:
            self._select_group_in_table(cur)
        if cur is not None and id(cur) in dirty and self.result_model.group() is cur:
            self.result_model.rows_updated()
            self._refresh_grouped_repeater_bar()
            _, sel = self.current_selection()
            if sel is not None and id(sel) in done_res:
                self._show_result(sel)

    def _refresh_stale_views(self, force):
        if self._stale_stats or self._stats is None:
            self._stale_stats = False
            self._stats = HierarchyStats(self.features_list(), self.group_model.all_groups())
            self._reload_feature_table(self._stats)
        stats = self._stats
        self._sync_path_combos(stats.paths)
        tree = self.left_hierarchy_tree
        if self._stale_left and tree is not None and tree.isShowing():
            label = "Tất cả Group & API (%d Nhánh | %d API)" % (len(stats.features), stats.total)
            if self._rebuild_tree("left", tree, self.left_hierarchy_tree_model, label, stats, force):
                self._stale_left = False
        tree = self.history_tree
        if self._stale_history and tree is not None and tree.isShowing():
            label = "Tổng cộng: %d Nhánh Chức năng | %d API đã đi qua" % (len(stats.features), stats.total)
            if self._rebuild_tree("history", tree, self.history_tree_model, label, stats, force):
                self._stale_history = False
                self._refresh_history_summary_only()
        tree = getattr(self, "full_tree", None)
        if self._stale_full and tree is not None and tree.isShowing():
            label = "Tất cả Group & API (%d Nhánh | %d API)" % (len(stats.features), stats.total)
            if self._rebuild_tree("full", tree, self.full_tree_model, label, stats, force):
                self._stale_full = False
                self._update_full_tree_header()
        table = getattr(self, "coverage_table", None)
        if self._stale_coverage and table is not None and table.isShowing():
            self._stale_coverage = False
            self._reload_coverage()
        tree = getattr(self, "log_tree", None)
        if self._stale_log and tree is not None and tree.isShowing():
            if self._rebuild_tree("log", tree, self.log_tree_model, "Nhật ký", stats, force,
                                  builder=self._build_log_nodes):
                self._stale_log = False

    def _reload_feature_table(self, stats):
        if self.feature_model is None or self.feature_table is None:
            return
        sel = self.feature_table.getSelectedRow()
        self._restoring_feature_sel = True
        try:
            same_size = self.feature_model.reload(build_feature_rows(stats, self.active_feature_id()))
            if not same_size:
                n = self.feature_model.getRowCount()
                if 0 <= sel < n:
                    self.feature_table.setRowSelectionInterval(sel, sel)
                elif n > 0:
                    self.feature_table.setRowSelectionInterval(0, 0)
        finally:
            self._restoring_feature_sel = False
        if not same_size:
            self._on_feature_filter_selected()

    def _sync_path_combos(self, paths):
        combo = getattr(self, "cb_existing_paths", None)
        editor_combo = getattr(self, "group_path_editor_combo", None)
        if combo is None or editor_combo is None:
            return
        cur_act = self.active_feature().name
        state = (tuple(paths), cur_act)
        if state == self._path_combo_state or self.group_table.isEditing():
            return
        self._path_combo_state = state
        editor_combo.removeAllItems()
        for p in paths:
            editor_combo.addItem(p)
        self._updating_path_combos = True
        try:
            combo.removeAllItems()
            for p in paths:
                combo.addItem(p)
            combo.setSelectedItem(cur_act)
        finally:
            self._updating_path_combos = False

    # -------------------------------------------------------------- features
    def features_list(self):
        with self._state_lock:
            return list(self._features)

    def active_feature_id(self):
        with self._state_lock:
            return self._active_fid

    def active_feature(self):
        with self._state_lock:
            for f in self._features:
                if f.fid == self._active_fid:
                    return f
            return self._features[-1]

    def get_feature(self, fid):
        if fid is None:
            return None
        with self._state_lock:
            for f in self._features:
                if f.fid == fid:
                    return f
        return None

    def start_new_feature(self, name=None):
        with self._state_lock:
            fid = self._next_fid
            self._next_fid += 1
            raw = u_text(name or "").strip()
            clean = normalize_hierarchy_path(raw) if ">" in raw else (raw or ("Chức năng %d" % fid))
            feat = FeatureGroup(fid, clean)
            self._features.append(feat)
            self._active_fid = fid
        self.log("Chuyển sang %s - các API tiếp theo sẽ được gom vào chức năng này."
                 % format_feature_label(feat.fid, feat.name))
        self._refresh_feature_views()
        self.update_status()
        return feat

    def find_or_create_feature_by_path(self, path_text, make_active=False):
        raw = u_text(path_text or "").strip()
        clean = normalize_hierarchy_path(raw) if ">" in raw else (raw or DEFAULT_HIERARCHY_PATH)
        with self._state_lock:
            for f in self._features:
                if f.name.lower() == clean.lower():
                    if make_active:
                        self._active_fid = f.fid
                    return f
            fid = self._next_fid
            self._next_fid += 1
            feat = FeatureGroup(fid, clean)
            self._features.append(feat)
            if make_active:
                self._active_fid = fid
        return feat

    def assign_group_to_path(self, group, new_path):
        """Assign an individual API group to a specific Group Path (e.g. Toppage > menu > button)."""
        if group is None:
            return
        feat = self.find_or_create_feature_by_path(new_path, make_active=False)
        self.move_groups_to_feature([group], feat.fid)

    def rename_hierarchy_prefix(self, old_prefix, new_prefix):
        """
        Rename a folder prefix (e.g. 'Toppage > menu' -> 'Toppage > navigation') across all
        features and captured API groups, preserving all deeper sub-folders under it!
        """
        old_clean = normalize_hierarchy_path(old_prefix)
        new_clean = normalize_hierarchy_path(new_prefix)
        if not old_clean or not new_clean:
            return
        with self._state_lock:
            for f in self._features:
                if hierarchy_matches_prefix(f.name, old_clean):
                    f.name = replace_hierarchy_prefix(f.name, old_clean, new_clean)

        def sync():
            if self.group_model is not None:
                for g in self.group_model.all_groups():
                    if hierarchy_matches_prefix(g.feature_name, old_clean):
                        g.feature_name = replace_hierarchy_prefix(g.feature_name, old_clean, new_clean)
                self.group_model.fireTableDataChanged()
            self._refresh_feature_views()
            self.update_status()
        ui_call(sync)
        self.log("Đổi tên nhánh '%s' -> '%s' (cập nhật toàn bộ sub-folder con)." % (old_clean, new_clean))

    def delete_hierarchy_prefix(self, prefix_path, delete_apis=False):
        """
        Delete a sub-folder branch from the hierarchy.
        If delete_apis=True, also deletes all APIs inside that branch;
        otherwise moves its APIs up to the parent folder (or 'Toppage').
        """
        clean_prefix = normalize_hierarchy_path(prefix_path)
        parent_path = pop_hierarchy_segment(clean_prefix) if len(split_hierarchy_path(clean_prefix)) > 1 else "Toppage"
        if parent_path.lower() == clean_prefix.lower():
            parent_path = "Toppage"
        with self._state_lock:
            kept = [f for f in self._features if not hierarchy_matches_prefix(f.name, clean_prefix)]
            if not kept:
                kept = [FeatureGroup(1, parent_path)]
                self._next_fid = max(self._next_fid, 2)
            self._features = kept
            if not any(f.fid == self._active_fid for f in self._features):
                self._active_fid = self._features[-1].fid
        fallback_feat = self.find_or_create_feature_by_path(parent_path, make_active=False)

        def sync():
            if self.group_model is not None:
                matched = [g for g in self.group_model.all_groups()
                           if hierarchy_matches_prefix(g.feature_name, clean_prefix)]
                if delete_apis and matched:
                    self.group_model.remove_groups(matched)
                    self.forget_dedup(matched)
                elif matched:
                    self.move_groups_to_feature(matched, fallback_feat.fid)
            self._refresh_feature_views()
            self.update_status()
        ui_call(sync)
        self.log("Đã xóa nhánh '%s'." % clean_prefix)

    def rename_feature(self, fid, new_name):
        raw = u_text(new_name or "").strip()
        clean = normalize_hierarchy_path(raw) if ">" in raw else (raw or ("Chức năng %d" % fid))
        with self._state_lock:
            feat = None
            for f in self._features:
                if f.fid == fid:
                    f.name = clean
                    feat = f
                    break
        if feat is None:
            return

        def sync():
            if self.group_model is not None:
                for g in self.group_model.all_groups():
                    if g.fid == fid:
                        g.feature_name = clean
                self.group_model.fireTableDataChanged()
            self._refresh_feature_views()
            self.update_status()
        ui_call(sync)
        self.log("Đổi tên chức năng #%d -> %s" % (fid, format_feature_label(fid, clean)))

    def set_active_feature(self, fid):
        with self._state_lock:
            for f in self._features:
                if f.fid == fid:
                    self._active_fid = fid
                    break
        self._refresh_feature_views()
        self.update_status()

    def move_groups_to_feature(self, groups, fid):
        feat = self.get_feature(fid)
        if feat is None or not groups:
            return
        cfg = self.get_config()
        for g in groups:
            g.fid = feat.fid
            g.feature_name = feat.name
            g.sync_original_meta(cfg["short_path_len"], cfg["include_feature_in_tab"])
            for r in g.results:
                r.tab_name = repeater_tab_name(g.gid, g.method, g.path, r.role_name,
                                               cfg["short_path_len"], g.fid, cfg["include_feature_in_tab"])
        if self.group_model is not None:
            self.group_model._rebuild_view()
            self.group_model.fireTableDataChanged()
        self._refresh_feature_views()
        self.update_status()

    def groups_for_hierarchy_prefix(self, prefix_path, groups_override=None):
        """
        Return all captured API groups whose hierarchy path starts with prefix_path.
        Example: prefix_path='Toppage' returns all APIs in 'Toppage', 'Toppage > menu',
        'Toppage > menu > button "Search"', etc.
        """
        if groups_override is not None:
            source_groups = list(groups_override)
        elif self.group_model is not None:
            source_groups = self.group_model.all_groups()
        else:
            source_groups = []
        if not prefix_path:
            return source_groups
        return [g for g in source_groups if hierarchy_matches_prefix(g.feature_name, prefix_path)]

    def replay_hierarchy_prefix(self, prefix_path, groups_override=None, include_original=False):
        """
        Manually send all APIs inside a hierarchical group prefix (e.g. 'Toppage' or 'Toppage > menu').
        Returns the list of API groups that were queued for sending.
        """
        matched = self.groups_for_hierarchy_prefix(prefix_path, groups_override=groups_override)
        for g in matched:
            targets = self.default_targets(g, include_original)
            self.replay(g, targets)
        if matched:
            self.log("Manual Send Hierarchy '%s': queued %d API group(s)." % (u_text(prefix_path), len(matched)))
        return matched

    def send_hierarchy_prefix_to_repeater(self, prefix_path, groups_override=None, include_original=False,
                                          compact=False, copy_group_name=False):
        """Send all APIs inside a hierarchical group prefix to Burp Repeater."""
        matched = self.groups_for_hierarchy_prefix(prefix_path, groups_override=groups_override)
        for g in matched:
            targets = self.default_targets(g, include_original)
            self.send_to_repeater(g, targets, compact=compact, copy_group_name=copy_group_name)
        return matched

    # -------------------------------------------------------------- settings
    def _load_json_setting(self, key, default):
        raw = self.callbacks.loadExtensionSetting(key)
        if not raw:
            return default
        try:
            return json.loads(raw)
        except Exception:
            return default

    def _load_original_profile(self):
        stored = self._load_json_setting(SETTINGS_KEY_ORIGINAL, None)
        prof = {"name": ORIGINAL_PROFILE_NAME, "enabled": False, "headers": []}
        if isinstance(stored, dict):
            try:
                prof = normalize_role(stored, 0)
            except Exception:
                pass
        prof["name"] = ORIGINAL_PROFILE_NAME
        return prof

    def _load_role_scopes(self):
        stored = self._load_json_setting(SETTINGS_KEY_ROLE_SCOPES, [])
        rules = []
        for r in stored if isinstance(stored, list) else []:
            if isinstance(r, dict) and r.get("prefix"):
                roles = dict([(u_text(k), bool(v)) for k, v in (r.get("roles") or {}).items()])
                if roles:
                    rules.append({"prefix": normalize_hierarchy_path(r["prefix"]), "roles": roles})
        return rules

    def save_role_scopes(self):
        self.callbacks.saveExtensionSetting(SETTINGS_KEY_ROLE_SCOPES, json.dumps(self.role_branch_rules))

    # ---- roles per scope (all / branches / single APIs)
    def sync_group_roles(self, group):
        """
        Bring an API's role rows in line with its effective roles: drop the roles switched off, add
        the ones switched on. Results already received by the remaining roles are kept.
        """
        cfg = self.get_config()
        wanted = effective_roles(self.roles.all(), group.feature_name, self.role_branch_rules,
                                 group.role_overrides)
        names = [r["name"] for r in wanted]
        keep = [r for r in group.results if (r.role_key or r.role_name) in names]
        have = set([r.role_key or r.role_name for r in keep])
        missing = [r for r in wanted if r["name"] not in have]
        if not missing and len(keep) == len(group.results):
            return False
        group.results = sorted(keep + self._make_role_results(group, missing, cfg), key=lambda r: r.role_index)
        group.recalc_audit()
        self._notify_results(group, None, finished_send=True)
        return True

    def apply_role_scope(self, role_names, enable, scope, targets=None, apply_existing=True):
        """
        Switch `role_names` on / off for scope 'global' (the roles themselves), 'branch' (targets =
        branch paths, sub-branches included, also for APIs captured later) or 'api' (targets = API
        groups). Returns how many captured APIs changed.
        """
        role_names = list(role_names)
        all_groups = self.group_model.all_groups() if self.group_model is not None else []
        affected = []
        if scope == "global":
            roles = self.roles.all()
            for i, r in enumerate(roles):
                if r["name"] in role_names:
                    self.roles.set_enabled(i, enable)
            self.save_roles()
            affected = all_groups if apply_existing else []
        elif scope == "branch":
            for prefix in targets or []:
                clean = normalize_hierarchy_path(prefix)
                rule = None
                for r in self.role_branch_rules:
                    if r["prefix"].lower() == clean.lower():
                        rule = r
                if rule is None:
                    rule = {"prefix": clean, "roles": {}}
                    self.role_branch_rules.append(rule)
                for name in role_names:
                    rule["roles"][name] = bool(enable)
                if apply_existing:
                    affected.extend([g for g in all_groups if hierarchy_matches_prefix(g.feature_name, clean)])
            self.save_role_scopes()
        else:
            for g in targets or []:
                for name in role_names:
                    g.role_overrides[name] = bool(enable)
            affected = list(targets or [])
        changed = 0
        seen = set()
        for g in affected:
            if id(g) not in seen:
                seen.add(id(g))
                changed += 1 if self.sync_group_roles(g) else 0
        what = {"global": "toàn bộ", "branch": "nhánh: " + ", ".join([u_text(t) for t in targets or []]),
                "api": "%d API" % len(targets or [])}[scope]
        self.log("%s %d role (%s) cho %s; %d API đã bắt được cập nhật." % (
            "BẬT" if enable else "TẮT", len(role_names), ", ".join(role_names), what, changed))
        if getattr(self, "role_model", None) is not None:
            ui_call(self.role_model.reload)
        self._mark(structure=True, status=True)
        return changed

    def open_role_scope_dialog(self, enable=False, scope="global", branches=None, apis=None, roles=None):
        preset = {"enable": enable, "scope": scope, "branches": branches or [],
                  "apis": [g.gid for g in apis or []], "roles": roles,
                  "apply_existing": getattr(self, "_scope_apply_existing", True)}
        choice = RoleScopeDialog(self, preset).show()
        if choice is None:
            return None
        if choice["scope"] != "api":
            self._scope_apply_existing = choice["apply_existing"]
        changed = self.apply_role_scope(choice["roles"], choice["enable"], choice["scope"], choice["targets"],
                                        choice["apply_existing"])
        if self.role_table is not None:
            self._roles_changed(self.role_table.getSelectedRow())
        self._flash_status("%s %d role · %d API cập nhật" % ("Bật" if choice["enable"] else "Tắt",
                                                            len(choice["roles"]), changed))
        return choice

    def _open_scope_for_selection(self, enable=False):
        groups, _ = self._groups_in_scope()
        kind, payload = self._selected_left_tree_payload() if self._scope_source == "tree" else (None, None)
        if kind == "FOLDER" and payload:
            return self.open_role_scope_dialog(enable, "branch", branches=[payload])
        if groups:
            return self.open_role_scope_dialog(enable, "api", apis=groups)
        return self.open_role_scope_dialog(enable)

    def remove_branch_rule(self, prefix, apply_existing=True):
        clean = normalize_hierarchy_path(prefix).lower()
        self.role_branch_rules = [r for r in self.role_branch_rules if r["prefix"].lower() != clean]
        self.save_role_scopes()
        changed = 0
        if apply_existing and self.group_model is not None:
            for g in self.group_model.all_groups():
                if hierarchy_matches_prefix(g.feature_name, prefix):
                    changed += 1 if self.sync_group_roles(g) else 0
        self.log("Đã xóa quy tắc role của nhánh '%s'; %d API cập nhật." % (prefix, changed))
        return changed

    def save_original_profile(self, profile):
        prof = normalize_role(profile, 0)
        prof["name"] = ORIGINAL_PROFILE_NAME
        self.original_profile = prof
        self.callbacks.saveExtensionSetting(SETTINGS_KEY_ORIGINAL, json.dumps(prof))
        self._refresh_original_profile_bar()

    def save_roles(self):
        self.callbacks.saveExtensionSetting(SETTINGS_KEY_ROLES, json.dumps(self.roles.all()))

    def get_config(self):
        with self._cfg_lock:
            return dict(self.config)

    def _recompile_filters(self, cfg):
        compiled, err = compile_api_regex(cfg.get("api_regex", ""))
        exts = parse_static_extensions(cfg.get("static_ext", ""))
        with self._cfg_lock:
            self._api_regex = compiled
            self._static_exts = exts
        return err

    def apply_config(self, new_cfg):
        new_cfg = merge_config(new_cfg)
        err = self._recompile_filters(new_cfg)
        with self._cfg_lock:
            old_threads = self.config["threads"]
            was_sending = self.config.get("auto_send", False)
            old_match = tuple([self.config.get(k) for k in TARGET_MATCH_KEYS])
            self.config = new_cfg
        if self.targets and old_match != tuple([new_cfg.get(k) for k in TARGET_MATCH_KEYS]):
            self._retag_groups()
        if was_sending and not new_cfg.get("auto_send", False):
            self.cancel_pending_sends("Đã DỪNG gửi")
        n = new_cfg["threads"]
        if n != old_threads:
            pool = self.send_executor
            if n > pool.getMaximumPoolSize():
                pool.setMaximumPoolSize(n)
                pool.setCorePoolSize(n)
            else:
                pool.setCorePoolSize(n)
                pool.setMaximumPoolSize(n)
        self.callbacks.saveExtensionSetting(SETTINGS_KEY_CONFIG, json.dumps(new_cfg))
        if not getattr(self, "_collecting_settings", False):
            # Changed from code (send toggle, Excel mode, ...): make the form show the real config,
            # otherwise the next form edit would write the stale widget values back.
            ui_call(lambda: self._sync_settings_ui(new_cfg))
        self.update_status()
        return err

    # ---------------------------------------------------------- IHttpListener
    def processHttpMessage(self, toolFlag, messageIsRequest, messageInfo):
        # Fast lock-free exit on non-Proxy or request phase or when capture is disabled
        if self._unloaded or messageIsRequest or toolFlag != self.callbacks.TOOL_PROXY:
            return
        cfg = self.config
        if not cfg.get("capture_enabled"):
            return
        try:
            req = messageInfo.getRequest()
            if req is None:
                return
            # Fast zero-allocation pre-check on the first line before copying byte[] arrays!
            fast_method, fast_path = fast_extract_method_and_path(req)
            if fast_method and fast_path:
                if cfg.get("ignore_options_head") and fast_method in ("OPTIONS", "HEAD"):
                    with self._state_lock:
                        self._skipped_count += 1
                        self._last_skip_reason = "method %s ignored" % fast_method
                    return
                if cfg.get("ignore_static") and is_static_path(fast_path, self._static_exts):
                    with self._state_lock:
                        self._skipped_count += 1
                        self._last_skip_reason = "static extension"
                    return
                targets = self.targets
                if cfg.get("target_only") and targets:
                    # The Excel list replaces the path regex: only documented APIs are copied.
                    if self._target_match(fast_method, fast_path, messageInfo.getHttpService().getHost(), cfg) is None:
                        with self._state_lock:
                            self._skipped_count += 1
                            self._last_skip_reason = "không có trong danh sách Excel"
                        return
                else:
                    rx = self._api_regex
                    if cfg.get("api_regex_enabled") and rx is not None and not rx.search(strip_query(fast_path)):
                        with self._state_lock:
                            self._skipped_count += 1
                            self._last_skip_reason = "API path regex mismatch"
                        return
            service = messageInfo.getHttpService()
            resp = messageInfo.getResponse()
            req_copy = Arrays.copyOf(req, len(req))
            resp_copy = Arrays.copyOf(resp, len(resp)) if resp is not None else None
            target_fid = self.active_feature_id()
            self.capture_executor.execute(_Task(
                lambda: self._process_capture(service, req_copy, resp_copy, "Proxy", True, target_fid),
                self.log))
        except Throwable as t:
            self.log("Proxy capture error: %s" % t)

    # ---------------------------------------------------- IContextMenuFactory
    def createMenuItems(self, invocation):
        messages = invocation.getSelectedMessages()
        if messages is None or len(messages) == 0:
            return None
        snapshot = []
        for m in messages:
            req = m.getRequest()
            if req is None:
                continue
            resp = m.getResponse()
            snapshot.append((m.getHttpService(), Arrays.copyOf(req, len(req)),
                             Arrays.copyOf(resp, len(resp)) if resp is not None else None))
        if not snapshot:
            return None

        cur_feat = self.active_feature()
        cur_label = format_feature_label(cur_feat.fid, cur_feat.name)

        def make_handler(apply_filters, prompt_new_feature=False):
            def handler(event):
                target_fid = cur_feat.fid
                if prompt_new_feature:
                    name = JOptionPane.showInputDialog(
                        self.main_panel,
                        "Nhập Đường dẫn Group phân cấp (VD: Toppage > menu > button \"Search\"):",
                        cur_feat.name)
                    if name is None:
                        return
                    feat = self.start_new_feature(name)
                    target_fid = feat.fid
                for svc, rq, rs in snapshot:
                    self.capture_executor.execute(_Task(
                        (lambda s=svc, a=rq, b=rs, tf=target_fid:
                         self._process_capture(s, a, b, "Manual", apply_filters, tf)),
                        self.log))
                self.log("Manual trigger: %d message(s) queued -> Feature #%d (%s)." %
                         (len(snapshot), target_fid,
                          "capture filters applied" if apply_filters else "filters bypassed"))
            return handler

        items = ArrayList()
        items.add(JMenuItem("%s: Clone to '%s' (%d message(s))" % (EXT_NAME, cur_label, len(snapshot)),
                            actionPerformed=make_handler(False, False)))
        items.add(JMenuItem("%s: Clone to NEW Group Path (Toppage > menu > button...) (%d message(s))"
                            % (EXT_NAME, len(snapshot)),
                            actionPerformed=make_handler(False, True)))
        items.add(JMenuItem("%s: Clone to '%s' (apply capture filters + dedup)" % (EXT_NAME, cur_label),
                            actionPerformed=make_handler(True, False)))
        return items

    # -------------------------------------------------------------- filtering
    def _filter_reason(self, cfg, url, method, path, target=None):
        """None if the request passes every filter, otherwise the reason it was skipped."""
        target_mode = bool(cfg.get("target_only") and self.targets)
        if cfg["ignore_options_head"] and method in ("OPTIONS", "HEAD"):
            return "method %s ignored" % method
        if cfg["in_scope_only"] and not self.callbacks.isInScope(url):
            return "out of scope"
        with self._cfg_lock:
            exts = self._static_exts
            rx = self._api_regex
        if cfg["ignore_static"] and is_static_path(path, exts):
            return "static extension"
        if target_mode:
            if target is None:
                return "không có trong danh sách Excel"
        elif cfg["api_regex_enabled"] and rx is not None and not rx.search(strip_query(path)):
            return "API path regex mismatch"
        return None

    # ------------------------------------------------ capture -> group build
    def _process_capture(self, service, req, resp, source, apply_filters, target_fid=None):
        """Runs on the single capture thread (deterministic API # / group IDs + dedup)."""
        if self._unloaded:
            return
        cfg = self.get_config()
        info = self.helpers.analyzeRequest(service, req)
        url = info.getUrl()
        method = ("%s" % (info.getMethod() or "GET")).upper()
        path = url.getFile() or "/"
        feat = self.get_feature(target_fid) or self.active_feature()
        standing = feat.name
        targets = self.targets
        target = self._target_match(method, path, service.getHost(), cfg) if targets else None
        if target is not None and target.position and cfg.get("target_use_position", True):
            feat = self.find_or_create_feature_by_path(target.position)

        def hit(result, gid=None, note=u""):
            if target is not None:
                self.target_hits.record(target, {
                    "time": time.strftime("%d/%m %H:%M:%S"), "result": result, "gid": gid, "method": method,
                    "path": u_text(path)[:400], "host": service.getHost(), "branch": standing,
                    "filed": feat.name, "source": source, "note": note})
                self._stale_coverage = True
                self._mark(status=True)

        key = None
        if apply_filters:
            reason = self._filter_reason(cfg, url, method, path, target)
            if reason:
                with self._state_lock:
                    self._skipped_count += 1
                    self._last_skip_reason = reason
                hit(HIT_FILTERED, note=reason)
                if source == "Manual":
                    self.log("Skipped %s %s (%s)" % (method, url, reason))
                self.update_status()
                return
            if cfg["dedup"]:
                base_key = dedup_key(method, service.getProtocol(), service.getHost(), service.getPort(),
                                     path, cfg["dedup_normalize_ids"])
                key = ("F%d|%s" % (feat.fid, base_key)) if cfg.get("dedup_per_feature") else base_key
                with self._state_lock:
                    seen = key in self._seen_keys
                    if seen:
                        self._skipped_count += 1
                        self._last_skip_reason = "dedup"
                    else:
                        self._seen_keys.add(key)
                    earlier = self._seen_gid.get(key)
                if seen:
                    hit(HIT_DUP, earlier)
                    if source == "Manual":
                        self.log("Skipped %s %s (duplicate endpoint)" % (method, url))
                    self.update_status()
                    return

        # Roles are optional: with none enabled the API is still captured, stored and shown
        # ("1 API gốc + 0 role") and every send / Repeater action falls back to the original.
        roles = effective_roles(self.roles.all(), feat.name, self.role_branch_rules)

        with self._state_lock:
            gid = self._next_gid
            self._next_gid += 1

        group = ApiGroup(gid, service, method, path, "%s" % url, req, resp, source,
                         feat.fid, feat.name)
        group.message_builder = self._build_message
        group.target = target
        if key is not None:
            group.dedup_key = key
            with self._state_lock:
                self._seen_gid[key] = gid
        hit(HIT_NEW, gid)
        if resp is not None:
            try:
                rinfo = self.helpers.analyzeResponse(resp)
                group.orig_status = rinfo.getStatusCode()
                group.orig_length = len(resp) - rinfo.getBodyOffset()
            except Throwable:
                pass
        group.sync_original_meta(cfg["short_path_len"], cfg.get("include_feature_in_tab", False))
        group.results = self._clone_for_roles(group, info, roles, cfg)
        self._apply_original_profile(group)
        group.recalc_audit()
        group.attach_store(self._persist(service, req, resp))

        with self._ui_lock:
            self._p_new.append(group)
        note = ""
        if not group.results:
            note += " (không có role nào bật - chỉ lưu API gốc)"
        if group.orig_result.rules:
            note += " (API gốc áp profile: %d rule)" % len(group.orig_result.rules)
        if target is not None:
            note += " (khớp dòng STT %s trong file Excel)" % target.stt
        self.log("Bắt từ %s: %s %s -> 1 API gốc + %d role%s" %
                 (source, method, url, len(group.results), note), gid=gid)
        if cfg["auto_repeater"]:
            self._dispatch_repeater(group, self.default_targets(group))
        if cfg["auto_send"]:
            targets = list(group.results)
            if cfg.get("auto_send_original"):
                targets.insert(0, group.orig_result)
            if targets:
                self.replay(group, targets)

    def default_targets(self, group, include_original=False):
        """What a plain Send / Push acts on: every role, or the original when the API has no role."""
        if not group.results:
            return [group.orig_result]
        if include_original:
            return [group.orig_result] + list(group.results)
        return list(group.results)

    def _apply_original_profile(self, group):
        """Snapshot the original profile's rules onto the API gốc (like role rules at capture time)."""
        prof = self.original_profile
        rules = [dict(h) for h in prof.get("headers", [])] if prof.get("enabled") else []
        orig = group.orig_result
        orig.rules = rules or None
        orig.role_name = ORIGINAL_LABEL + (("  + profile (%d rule)" % len(rules)) if rules else "")

    def _clone_for_roles(self, group, info, roles, cfg):
        """
        One VIRTUAL request per enabled role: only the role's rule snapshot is stored.
        The bytes are built by ApiGroup.build_request() when the role is viewed, sent or
        pushed to Repeater (method/URL/params/body always come from the original).
        """
        group.base_headers = [u_text(h) for h in info.getHeaders()]
        group.body_offset = info.getBodyOffset()
        return self._make_role_results(group, roles, cfg)

    def _make_role_results(self, group, roles, cfg):
        results = []
        for pos, role in enumerate(roles):
            idx = role.get("_index", pos)   # position in the full role list: stable numbering
            display = display_role_name(role["name"], idx, cfg["number_roles_in_tab"])
            res = RoleResult(display, idx, None, is_stripped_auth=is_stripped_auth_role(role),
                             group=group, rules=role["headers"])
            res.role_key = role["name"]
            res.tab_name = repeater_tab_name(group.gid, group.method, group.path, display,
                                             cfg["short_path_len"], group.fid,
                                             cfg.get("include_feature_in_tab", False))
            evaluate_role_result(group, res)
            results.append(res)
        return results

    def _build_message(self, headers, orig_request, body_offset):
        jlist = ArrayList()
        for h in headers:
            jlist.add(h)
        body = Arrays.copyOfRange(orig_request, body_offset, len(orig_request))
        return self.helpers.buildHttpMessage(jlist, body)

    def _persist(self, service, request, response):
        """
        Move a message into Burp's temp file. Returns the persisted handle, or None when
        disk storage is off / unavailable (the caller then keeps the bytes in memory).
        """
        if self._persist_failures >= 3 or not self.config.get("store_on_disk", True):
            return None
        try:
            store = self.callbacks.saveBuffersToTempFiles(_BytesMessage(service, request, response))
            self._persist_failures = 0
            return store
        except (Throwable, Exception):
            self._persist_failures += 1
            if self._persist_failures == 3:
                self.log("Burp temp-file storage unavailable - keeping messages in memory.")
            return None

    def rebuild_group(self, group):
        """Re-clone a group's original request with the *current* enabled roles."""
        def work():
            roles = effective_roles(self.roles.all(), group.feature_name, self.role_branch_rules,
                                    group.role_overrides)
            cfg = self.get_config()
            info = self.helpers.analyzeRequest(group.service, group.orig_request)
            new_results = self._clone_for_roles(group, info, roles, cfg)

            def apply():
                group.results = new_results
                self._apply_original_profile(group)
                group.sync_original_meta(cfg["short_path_len"], cfg.get("include_feature_in_tab", False))
                group.recalc_audit()
                self.group_model.refresh_group(group)
                if self.result_model.group() is group:
                    self.result_model.set_group(group)
                    self._select_first_result()
                    self._refresh_grouped_repeater_bar()
                self._refresh_feature_views()
            ui_call(apply)
            self.log("Dựng lại với 1 API gốc + %d role hiện tại." % len(new_results), gid=group.gid)
        self.capture_executor.execute(_Task(work, self.log))

    # -------------------------------------------------------------- Repeater
    def _copy_to_clipboard(self, text):
        try:
            cb = Toolkit.getDefaultToolkit().getSystemClipboard()
            if cb is not None:
                cb.setContents(StringSelection(u_text(text)), None)
        except Throwable:
            pass
        except Exception:
            pass

    def send_to_repeater(self, group, results, compact=False, copy_group_name=False):
        """Public entry (EDT-safe): dispatch off the EDT, preserving order."""
        results = list(results)
        self.capture_executor.execute(
            _Task(lambda: self._dispatch_repeater(group, results, compact=compact,
                                                  copy_group_name=copy_group_name), self.log))

    def _dispatch_repeater(self, group, results, compact=False, copy_group_name=False):
        cfg = self.get_config()
        inc_feat = cfg.get("include_feature_in_tab", False)
        for res in results:
            try:
                if compact:
                    short_role = u_text(res.role_name)
                    if getattr(res, "is_original", False):
                        short_role = "00_GOC"
                    tname = compact_repeater_tab_name(group.gid, short_role, group.fid, inc_feat)
                else:
                    tname = res.tab_name
                self.callbacks.sendToRepeater(group.host, group.port, group.use_https(),
                                              res.request, tname)
            except Throwable as t:
                self.log("Đẩy Repeater lỗi (%s): %s" % (res.tab_name, t), gid=group.gid)
        if copy_group_name:
            grp_title = "%s %s %s" % (format_group_id(group.gid), group.method,
                                      short_path(group.path, 28))
            self._copy_to_clipboard(grp_title)
            self.log("Đã đẩy %d tab gọn sang Burp Repeater (copy tên Group '%s')." % (len(results), grp_title),
                     gid=group.gid)
        else:
            self.log("Đã đẩy %d request sang Burp Repeater." % len(results), gid=group.gid)

    # ------------------------------------------------------ background replay
    def replay(self, group, results):
        """Queue requests on the SendDispatcher (paced per host); never blocks the caller."""
        busy = (STATE_QUEUED, STATE_SENDING, STATE_RETRY)
        results = [r for r in results if r.state not in busy]
        if not results:
            return
        with self._state_lock:
            self._active_sends += len(results)
        for res in results:
            res.state = STATE_QUEUED
            res.error = ""
            evaluate_role_result(group, res)
        group.recalc_audit()
        self._notify_results(group, None, finished_send=False)
        self.dispatcher.submit([_SendJob(group, res) for res in results])

    def cancel_pending_sends(self, reason="Đã hủy"):
        """Take every not-yet-sent request off the queue; already-sent results are kept."""
        dropped = self.dispatcher.cancel_all()
        if not dropped:
            return 0
        groups = {}
        for job in dropped:
            res = job.res
            res.state = STATE_DONE if res.status is not None else STATE_NOT_SENT
            res.error = ""
            groups[id(job.group)] = job.group
        with self._state_lock:
            self._active_sends = max(0, self._active_sends - len(dropped))
            all_settled = (self._active_sends == 0)
        for g in groups.values():
            g.recalc_audit()
            self._notify_results(g, None, finished_send=all_settled)
        self.log("%s: %d request trong hàng đợi không được gửi." % (reason, len(dropped)))
        return len(dropped)

    def _run_job(self, job):
        group, res = job.group, job.res
        if self._unloaded:
            return
        res.state = STATE_SENDING
        evaluate_role_result(group, res)
        self._notify_results(group, None)
        started = time.time()
        retry_after = None
        try:
            request = res.request  # a virtual role request is built here, used once, then dropped
            if request is None:
                raise ValueError("request could not be built")
            started = time.time()
            rr = self.callbacks.makeHttpRequest(group.service, request)
            resp = rr.getResponse() if rr is not None else None
            res.elapsed_ms = int((time.time() - started) * 1000)
            res.sent_count += 1
            if resp is None or len(resp) == 0:
                res.response = None
                res.status = None
                res.length = None
                res.state = STATE_ERROR
                res.error = "No response (timeout / connection failure)"
            else:
                rinfo = self.helpers.analyzeResponse(resp)
                store = self._persist(group.service, request, resp)
                if store is not None:
                    res.set_response_store(store)
                else:
                    res.response = resp
                res.status = rinfo.getStatusCode()
                res.length = len(resp) - rinfo.getBodyOffset()
                res.state = STATE_DONE
                res.error = ""
                if res.status in RETRYABLE_STATUS:
                    try:
                        retry_after = parse_retry_after(rinfo.getHeaders())
                    except (Throwable, Exception):
                        retry_after = None  # fall back to exponential back-off
                if getattr(res, "is_original", False):
                    group.has_orig_response = True
                    group.orig_status = res.status
                    group.orig_length = res.length
        except Throwable as t:
            res.elapsed_ms = int((time.time() - started) * 1000)
            res.state = STATE_ERROR
            res.error = "%s" % t
        except Exception as e:
            res.elapsed_ms = int((time.time() - started) * 1000)
            res.state = STATE_ERROR
            res.error = "%s" % e
        status = res.status if res.state == STATE_DONE else None
        if self.dispatcher.will_retry(job, status):
            res.state = STATE_RETRY
            res.error = "HTTP %d - server giới hạn tốc độ, sẽ tự gửi lại (lần %d/%d)" % (
                status, job.retries + 1, self.get_config().get("max_retries", 0))
        finished = self.dispatcher.done(job, status, retry_after)
        # Pre-calculate audit on the worker thread so the Swing EDT does 0 heavy work
        group.recalc_audit()
        all_settled = False
        if finished:
            with self._state_lock:
                self._active_sends = max(0, self._active_sends - 1)
                all_settled = (self._active_sends == 0)
        self._notify_results(group, res if finished else None, finished_send=all_settled)

    def _notify_results(self, group, res, finished_send=False):
        """Record that a group changed; the UI tick repaints it (any thread, never blocks)."""
        with self._ui_lock:
            self._p_dirty[id(group)] = group
            if res is not None and res.state in (STATE_DONE, STATE_ERROR):
                self._p_done_res.add(id(res))
            if finished_send:
                self._p_structure = True
            self._p_status = True

    @staticmethod
    def _make_color_badge(text, bg_color, fg_color):
        lbl = JLabel(" " + text + " ")
        lbl.setOpaque(True)
        lbl.setBackground(bg_color)
        lbl.setForeground(fg_color)
        lbl.setFont(Font("Dialog", Font.BOLD, 11))
        lbl.setBorder(BorderFactory.createLineBorder(Color(190, 190, 190)))
        return lbl

    # ===================================================================== UI
    def _build_ui(self):
        self.main_panel = JPanel(BorderLayout())
        cfg = self.get_config()
        self._repeater_group_Expanded = True

        # ---- Modern Minimalist Single-Strip Header Bar (Capture + Breadcrumb Chips + Dropdown Menus + Status)
        top_container = JPanel(BorderLayout(4, 2))
        top_container.setBorder(BorderFactory.createEmptyBorder(3, 6, 3, 6))

        # Keep checkbox instances initialized so _collect_settings & _on_restore_defaults stay 100% compatible
        self.cb_capture = JCheckBox("● Capture Proxy", cfg["capture_enabled"],
                                    actionPerformed=self._on_settings_changed)
        self.cb_capture.setFont(Font("Dialog", Font.BOLD, 12))
        self.cb_auto_send = JCheckBox("Cho phép Tự động Gửi ngầm (Mặc định: TẮT)", cfg["auto_send"],
                                      actionPerformed=self._on_settings_changed)
        self.cb_auto_repeater = JCheckBox("Tự động đẩy Repeater (Mặc định: TẮT)", cfg["auto_repeater"],
                                          actionPerformed=self._on_settings_changed)
        self.cb_top_scope = JCheckBox("In-Scope Only", cfg["in_scope_only"],
                                      actionPerformed=self._on_top_filter_toggled)
        self.cb_top_regex = JCheckBox("API Path Regex", cfg["api_regex_enabled"],
                                      actionPerformed=self._on_top_filter_toggled)
        self.cb_existing_paths = JComboBox([self.active_feature().name])
        self.cb_existing_paths.addActionListener(_Action(self._on_existing_path_picked))

        left_header = JPanel(FlowLayout(FlowLayout.LEFT, 4, 1))
        self.btn_capture_opts = JButton("⚙ Chế độ & Lọc ▾",
                                        actionPerformed=lambda e: self._show_capture_options_menu(self.btn_capture_opts))
        self.btn_capture_opts.setMargin(Insets(2, 7, 2, 7))

        self.lbl_active_feature = JLabel("Path [#1]:")
        self.lbl_active_feature.setFont(Font("Dialog", Font.BOLD, 11))
        self.subfolder_chips_panel = JPanel(FlowLayout(FlowLayout.LEFT, 2, 0))
        self.tf_feature_name = JTextField(self.active_feature().name, 18)
        self.tf_feature_name.addActionListener(_Action(self._on_apply_active_feature_name))
        self.tf_feature_name.setToolTipText(
            "Nhập đường dẫn N cấp ngăn cách bởi '>' rồi nhấn Enter (VD: Toppage > menu > button)")

        self.btn_path_menu = JButton("📁 Path / Nhánh ▾",
                                     actionPerformed=lambda e: self._show_path_actions_menu(self.btn_path_menu))
        self.btn_path_menu.setMargin(Insets(2, 8, 2, 8))
        self.btn_path_menu.setFont(Font("Dialog", Font.BOLD, 11))

        self.lbl_feature_counter = JLabel("(0 API)")
        left_header.add(self.cb_capture)
        self.btn_send_mode = JButton(" ", actionPerformed=self._on_toggle_send_mode)
        self.btn_send_mode.setFont(Font("Dialog", Font.BOLD, 12))
        self.btn_send_mode.setMargin(Insets(2, 8, 2, 8))
        self.btn_queue = JButton("Hàng đợi: 0", actionPerformed=self._on_cancel_queue)
        self.btn_queue.setMargin(Insets(2, 6, 2, 6))
        left_header.add(self.btn_send_mode)
        left_header.add(self.btn_queue)
        left_header.add(self.btn_capture_opts)
        left_header.add(JLabel(" | "))
        left_header.add(self.lbl_active_feature)
        left_header.add(self.subfolder_chips_panel)
        left_header.add(self.tf_feature_name)
        left_header.add(self.btn_path_menu)
        left_header.add(self.lbl_feature_counter)

        # Second header row: never competes for width with the controls above (no overlap).
        right_header = JPanel(FlowLayout(FlowLayout.LEFT, 4, 0))
        self.status_label = JLabel("")
        self.status_label.setFont(Font("Dialog", Font.PLAIN, 11))
        right_header.add(self.status_label)
        right_header.add(self._make_color_badge("Vàng: Lỗi/Lệch",
                                                AuditTableRenderer.BG_INFO, AuditTableRenderer.FG_INFO))
        right_header.add(self._make_color_badge("Cam: Bypass",
                                                AuditTableRenderer.BG_WARN, AuditTableRenderer.FG_WARN))
        right_header.add(self._make_color_badge("Xanh: 2xx",
                                                AuditTableRenderer.BG_OK, AuditTableRenderer.FG_OK))

        self._rebuild_subfolder_chips(self.active_feature().name)
        top_container.add(left_header, BorderLayout.NORTH)
        top_container.add(right_header, BorderLayout.SOUTH)
        self.main_panel.add(top_container, BorderLayout.NORTH)
        self.btn_detach = JButton("🗗 Tách ra cửa sổ riêng", actionPerformed=self._on_toggle_detach)
        self.btn_detach.setMargin(Insets(1, 6, 1, 6))
        self.btn_detach.setToolTipText("Mở cả extension trong một cửa sổ riêng (vd: màn hình thứ 2); "
                                       "đóng cửa sổ để gắn lại vào tab của Burp")
        right_header.add(self.btn_detach)

        self.tabs = JTabbedPane()
        self.tabs.addTab("API Groups & Repeater", self._build_groups_tab())
        self.tabs.addTab("Lịch sử & Báo cáo", self._build_history_tab())
        self.tabs.addTab("Roles (Profiles)", self._build_roles_tab())
        self.tabs.addTab("Cấu hình & Bộ lọc", self._build_settings_tab(cfg))
        self.tabs.addTab("Log", self._build_log_tab())
        self.tabs.addTab("Độ phủ Excel", self._build_coverage_tab())
        self.tabs.addTab("🌳 Cây Sub-folder", self._build_tree_tab())
        # A tree that was hidden while APIs arrived is rebuilt the moment its tab is opened.
        self.tabs.addChangeListener(_Change(lambda e: self._ui_tick(None)))
        self.main_panel.add(self.tabs, BorderLayout.CENTER)
        try:
            self.callbacks.customizeUiComponent(self.main_panel)
            self._ensure_tree_renderers()
        except (Throwable, Exception):
            try:
                self.callbacks.printError("Warning: customizeUiComponent failed:\n%s" % u_text(traceback.format_exc()))
            except (Throwable, Exception):
                pass

    # ---- API Groups tab (Minimalist 1-row toolbar + Dropdowns + Right-click menus + Full screen space)
    def _build_groups_tab(self):
        panel = JPanel(BorderLayout())

        # Keep hidden combo for repeater mode state compatibility, controlled via "📤 Repeater ▾" dropdown
        self.cb_repeater_mode = JComboBox([
            "Repeater Gọn: G01•01_Admin (+Copy tên Group)",
            "Repeater: Chỉ đẩy Role Lỗi/Lệch (Vàng/Cam)",
            "Repeater Đầy đủ: [G01:METHOD /path] 01_Admin"
        ])
        self.btn_replay_sel = JButton("▶ Gửi lại Role đang chọn", actionPerformed=self._on_replay_selected)
        self.btn_send_group = JButton("📤 Đẩy API -> Burp Repeater", actionPerformed=self._on_send_group)
        self.btn_send_role = JButton("📤 Đẩy Role -> Burp Repeater", actionPerformed=self._on_send_role)

        # Single-row modern minimalist action bar
        action_bar = JPanel(BorderLayout(4, 2))
        action_bar.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))

        left_actions = JPanel(FlowLayout(FlowLayout.LEFT, 4, 1))
        self.btn_replay_all = JButton("▶ Gửi API (N Roles)", actionPerformed=self._on_replay_all)
        self.btn_replay_all.setFont(Font("Dialog", Font.BOLD, 11))
        self.btn_replay_all.setBackground(Color(235, 95, 40))
        self.btn_replay_all.setForeground(Color(255, 255, 255))

        self.btn_replay_branch = JButton("▶▶ Gửi Nhánh",
                                         actionPerformed=self._on_replay_selected_hierarchy_or_feature)

        self.btn_send_dropdown = JButton("▶ Gửi ▾",
                                         actionPerformed=lambda e: self._show_send_dropdown_menu(self.btn_send_dropdown))

        self.btn_repeater_dropdown = JButton("📤 Burp Repeater ▾",
                                             actionPerformed=lambda e: self._show_repeater_dropdown_menu(self.btn_repeater_dropdown))

        self.btn_tools_dropdown = JButton("🛠 Công cụ ▾",
                                          actionPerformed=lambda e: self._show_tools_dropdown_menu(self.btn_tools_dropdown))

        left_actions.add(self.btn_replay_all)
        left_actions.add(self.btn_replay_branch)
        left_actions.add(self.btn_send_dropdown)
        left_actions.add(self.btn_repeater_dropdown)
        left_actions.add(self.btn_tools_dropdown)
        btn_copy = JButton("📋 Copy STT + Path", actionPerformed=self._on_copy_scope)
        btn_copy.setToolTipText("Copy 'STT. path' của API / nhánh đang chọn (Ctrl+Shift+C)")
        left_actions.add(btn_copy)

        right_filters = JPanel(FlowLayout(FlowLayout.RIGHT, 4, 1))
        right_filters.add(JLabel("Xem:"))
        self.cb_group_mode = JComboBox([
            "Theo từng API (Mặc định)",
            "Lọc theo Nhánh đang chọn"
        ])
        self.cb_group_mode.addActionListener(_Action(self._on_group_mode_changed))
        right_filters.add(self.cb_group_mode)
        right_filters.add(JLabel("Màu:"))
        self.cb_audit_filter = JComboBox([label for label, _ in AUDIT_FILTER_OPTIONS])
        self.cb_audit_filter.addActionListener(_Action(self._on_audit_filter_changed))
        right_filters.add(self.cb_audit_filter)

        action_bar.add(left_actions, BorderLayout.WEST)
        action_bar.add(right_filters, BorderLayout.EAST)
        panel.add(action_bar, BorderLayout.NORTH)

        # Left side of top master area: Nested Hierarchy Tree + Context Menu
        left_root = HierarchyTreeNode("ROOT", "", "Tất cả Group & API")
        self.left_hierarchy_tree_model = DefaultTreeModel(left_root)
        self.left_hierarchy_tree = JTree(self.left_hierarchy_tree_model)
        self.left_hierarchy_tree.setRowHeight(26)
        self.left_hierarchy_tree.setLargeModel(True)
        self._install_copy_shortcut(self.left_hierarchy_tree)
        self.left_hierarchy_tree.setCellRenderer(HierarchyTreeRenderer())
        self.left_hierarchy_tree.addTreeWillExpandListener(_LazyTreeLoader(
            lambda node: self._lazy_load_tree_node("left", self.left_hierarchy_tree_model, node)))
        self.left_hierarchy_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.left_hierarchy_tree.addTreeSelectionListener(
            _TreeListener(lambda: self._on_tree_used(self.left_hierarchy_tree)))
        self.left_hierarchy_tree.addMouseListener(
            _TreePopupListener(self.left_hierarchy_tree,
                               lambda e: self._tree_popup_from(self.left_hierarchy_tree, e)))
        chips = _TreeChipClick(self.left_hierarchy_tree, self)
        self.left_hierarchy_tree.addMouseListener(chips)
        self.left_hierarchy_tree.addMouseMotionListener(chips)

        self.feature_model = FeatureTableModel(self)
        self.feature_table = JTable(self.feature_model)
        style_data_table(self.feature_table)
        self.feature_table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.feature_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_feature_filter_selected))
        self.feature_table.addMouseListener(
            _TablePopupListener(self.feature_table, self._show_feature_table_popup))
        feat_renderer = AuditTableRenderer(self.feature_model, status_col=None, audit_col=3)
        for col, width in ((0, 56), (1, 165), (2, 50), (3, 155), (4, 115)):
            column = self.feature_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(feat_renderer)

        left_tabs = JTabbedPane()
        left_tabs.addTab("Cây Sub-folder", JScrollPane(self.left_hierarchy_tree))
        left_tabs.addTab("Bảng Nhánh", JScrollPane(self.feature_table))
        left_tabs.addChangeListener(_Change(lambda e: self._ui_tick(None)))
        self.left_group_tabs = left_tabs

        feat_panel = JPanel(BorderLayout(2, 2))
        feat_panel.setBorder(BorderFactory.createTitledBorder(
            "Cây phân cấp Sub-folder (Chuột phải để Gửi / Thêm / Sửa / Xóa)"))
        feat_panel.add(left_tabs, BorderLayout.CENTER)

        feat_mini_bar = JPanel(FlowLayout(FlowLayout.LEFT, 3, 1))
        btn_add_sub = JButton("+ Sub-folder", actionPerformed=self._on_add_subfolder_to_selected_tree)
        btn_add_sub.setMargin(Insets(1, 6, 1, 6))
        btn_add_branch = JButton("+ Nhánh", actionPerformed=self._on_next_feature)
        btn_add_branch.setMargin(Insets(1, 6, 1, 6))
        btn_show_all = JButton("Xem tất cả", actionPerformed=self._on_show_all_features)
        btn_show_all.setMargin(Insets(1, 6, 1, 6))
        self.btn_branch_more = JButton("Thao tác ▾",
                                       actionPerformed=lambda e: self._show_branch_actions_menu(self.btn_branch_more))
        self.btn_branch_more.setMargin(Insets(1, 6, 1, 6))
        feat_mini_bar.add(btn_add_sub)
        feat_mini_bar.add(btn_add_branch)
        feat_mini_bar.add(btn_show_all)
        feat_mini_bar.add(self.btn_branch_more)
        feat_panel.add(feat_mini_bar, BorderLayout.SOUTH)

        # Right side of top master area: Sequentially numbered API Groups table (Right-click + Editable Group Path)
        self.group_model = GroupTableModel(self)
        self.group_table = JTable(self.group_model)
        self.group_table.putClientProperty("terminateEditOnFocusLost", Boolean.TRUE)
        style_data_table(self.group_table)
        self._install_copy_shortcut(self.group_table)
        self.group_table.setAutoCreateRowSorter(True)
        self.group_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.group_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_group_selected))
        self.group_table.addMouseListener(
            _TablePopupListener(self.group_table, self._show_group_table_popup))
        grp_renderer = AuditTableRenderer(self.group_model, status_col=7, audit_col=3, method_col=4,
                                          bold_cols=(0,))
        for col, width in ((0, 72), (1, 46), (2, 200), (3, 185), (4, 68), (5, 130),
                           (6, 235), (7, 48), (8, 62), (9, 95), (10, 58), (11, 52), (12, 60), (13, 230)):
            column = self.group_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(grp_renderer)
        cm = self.group_table.getColumnModel()
        copy_col = cm.getColumn(GroupTableModel.COPY_COL)
        copy_col.setPreferredWidth(34)
        copy_col.setMaxWidth(40)
        copy_col.setCellRenderer(_ActionCellRenderer(
            self.group_model, "copy", lambda r: u"Bấm để copy: " + self.copy_label_for(self.group_model.group_at(r), False)))
        excel_col = cm.getColumn(GroupTableModel.EXCEL_COL)
        excel_col.setPreferredWidth(100)
        excel_col.setCellRenderer(_ActionCellRenderer(
            self.group_model, "link", lambda r: self._excel_tooltip(self.group_model.group_at(r))))
        # 'Copy' first, 'Excel' right after Method (the other columns keep their model index)
        cm.moveColumn(GroupTableModel.COPY_COL, 0)
        cm.moveColumn(GroupTableModel.EXCEL_COL, 6)
        cell_click = _TableCellClick(self.group_table, (GroupTableModel.COPY_COL, GroupTableModel.EXCEL_COL),
                                     self._on_group_cell_click)
        self.group_table.addMouseListener(cell_click)
        self.group_table.addMouseMotionListener(cell_click)
        self.group_path_editor_combo = JComboBox([DEFAULT_HIERARCHY_PATH])
        self.group_path_editor_combo.setEditable(True)
        self.group_table.getColumnModel().getColumn(2).setCellEditor(
            DefaultCellEditor(self.group_path_editor_combo))

        group_panel = JPanel(BorderLayout())
        group_panel.setBorder(BorderFactory.createTitledBorder(
            "Danh sách API (Click đúp cột 'Group Path' để chọn Nhánh | Chuột phải để Gửi / Đẩy Repeater)"))
        group_panel.add(JScrollPane(self.group_table), BorderLayout.CENTER)

        top_master_split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, feat_panel, group_panel)
        top_master_split.setResizeWeight(0.30)

        # Bottom detail area: 1 API Gốc + N Role results table + Built-in Grouped Repeater + Editable Viewers
        self.result_model = ResultTableModel()
        self.result_table = JTable(self.result_model)
        style_data_table(self.result_table)
        self.result_table.setAutoCreateRowSorter(True)
        self.result_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.result_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_result_selected))
        self.result_table.addMouseListener(_DoubleClick(lambda: self._on_send_role(None)))
        self.result_table.addMouseListener(
            _TablePopupListener(self.result_table, self._show_result_table_popup))
        res_renderer = AuditTableRenderer(self.result_model, status_col=4, audit_col=2)
        for col, width in ((0, 66), (1, 185), (2, 210), (3, 80), (4, 55), (5, 75),
                           (6, 85), (7, 70), (8, 50), (9, 340)):
            column = self.result_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(res_renderer)

        res_panel = JPanel(BorderLayout())
        res_panel.setBorder(BorderFactory.createTitledBorder(
            "So sánh 1 API GỐC (Acc Crawl) & N Roles (Click đúp hoặc Chuột phải để Gửi / Đẩy Repeater)"))
        res_panel.add(JScrollPane(self.result_table), BorderLayout.CENTER)

        # ---- Built-in Collapsible Group Repeater Bar (Minimalist Single-Strip Bar + Editable Request/Response)
        grouped_repeater_container = JPanel(BorderLayout(2, 2))
        grouped_repeater_bar = JPanel(BorderLayout(4, 1))
        grouped_repeater_bar.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))

        left_pill_box = JPanel(FlowLayout(FlowLayout.LEFT, 3, 1))
        self.btn_repeater_group_pill = JButton("📁 Chưa chọn API Group ▾",
                                               actionPerformed=self._on_toggle_or_switch_repeater_group)
        self.btn_repeater_group_pill.setBackground(Color(218, 206, 252))
        self.btn_repeater_group_pill.setForeground(Color(55, 20, 120))
        self.btn_repeater_group_pill.setFont(Font("Dialog", Font.BOLD, 12))
        left_pill_box.add(self.btn_repeater_group_pill)

        self.repeater_role_tabs_panel = JPanel(FlowLayout(FlowLayout.LEFT, 3, 1))
        role_tabs_scroll = JScrollPane(
            self.repeater_role_tabs_panel,
            JScrollPane.VERTICAL_SCROLLBAR_NEVER,
            JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED
        )
        role_tabs_scroll.setBorder(BorderFactory.createEmptyBorder())
        role_tabs_scroll.setPreferredSize(Dimension(420, 32))

        right_send_box = JPanel(FlowLayout(FlowLayout.RIGHT, 3, 1))
        self.btn_inline_send_one = JButton("▶ Send Tab này", actionPerformed=self._on_inline_repeater_send_one)
        self.btn_inline_send_one.setBackground(Color(235, 95, 40))
        self.btn_inline_send_one.setForeground(Color(255, 255, 255))
        self.btn_inline_send_one.setFont(Font("Dialog", Font.BOLD, 11))
        btn_inline_send_group = JButton("▶▶ Send Group", actionPerformed=self._on_replay_all)
        self.btn_inline_more = JButton("⋯ Thêm ▾",
                                       actionPerformed=lambda e: self._show_inline_repeater_more_menu(self.btn_inline_more))
        right_send_box.add(self.btn_inline_send_one)
        right_send_box.add(btn_inline_send_group)
        right_send_box.add(self.btn_inline_more)

        grouped_repeater_bar.add(left_pill_box, BorderLayout.WEST)
        grouped_repeater_bar.add(role_tabs_scroll, BorderLayout.CENTER)
        grouped_repeater_bar.add(right_send_box, BorderLayout.EAST)

        controller = _EditorController(self)
        self.req_viewer = self.callbacks.createMessageEditor(controller, True)
        self.resp_viewer = self.callbacks.createMessageEditor(controller, False)
        self.lbl_req_header = JLabel(" Request (Sửa trực tiếp & bấm '▶ Send Tab này')")
        self.lbl_req_header.setFont(Font("Dialog", Font.BOLD, 11))
        self.lbl_resp_header = JLabel(" Response")
        self.lbl_resp_header.setFont(Font("Dialog", Font.BOLD, 11))
        req_panel = JPanel(BorderLayout())
        req_panel.add(self.lbl_req_header, BorderLayout.NORTH)
        req_panel.add(self.req_viewer.getComponent(), BorderLayout.CENTER)
        resp_panel = JPanel(BorderLayout())
        resp_panel.add(self.lbl_resp_header, BorderLayout.NORTH)
        resp_panel.add(self.resp_viewer.getComponent(), BorderLayout.CENTER)
        viewers = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, req_panel, resp_panel)
        viewers.setResizeWeight(0.5)

        grouped_repeater_container.add(grouped_repeater_bar, BorderLayout.NORTH)
        grouped_repeater_container.add(viewers, BorderLayout.CENTER)

        detail_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, res_panel, grouped_repeater_container)
        detail_split.setResizeWeight(0.30)
        master_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, top_master_split, detail_split)
        master_split.setResizeWeight(0.36)
        panel.add(master_split, BorderLayout.CENTER)
        return panel

    # ---- "Cây Sub-folder" tab: the branch tree alone, full size, can pop out into its own window
    def _build_tree_tab(self):
        self.full_tree_model = DefaultTreeModel(HierarchyTreeNode("ROOT", "", "Tất cả Group & API", key=("ROOT",)))
        self.full_tree = JTree(self.full_tree_model)
        self.full_tree.setRowHeight(26)
        self.full_tree.setLargeModel(True)
        self._install_copy_shortcut(self.full_tree)
        self.full_tree.setCellRenderer(HierarchyTreeRenderer())
        self.full_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.full_tree.addTreeSelectionListener(_TreeListener(lambda: self._on_full_tree_selected()))
        self.full_tree.addTreeWillExpandListener(_LazyTreeLoader(
            lambda node: self._lazy_load_tree_node("full", self.full_tree_model, node)))
        self.full_tree.addMouseListener(_TreePopupListener(self.full_tree, lambda e: self._tree_popup_from(self.full_tree, e)))
        chips = _TreeChipClick(self.full_tree, self)
        self.full_tree.addMouseListener(chips)
        self.full_tree.addMouseMotionListener(chips)

        bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        self.btn_tree_window = JButton("🗗 Mở cửa sổ riêng", actionPerformed=self._on_toggle_tree_window)
        self.btn_tree_window.setFont(self.btn_tree_window.getFont().deriveFont(Font.BOLD))
        bar.add(self.btn_tree_window)
        push = JButton("🎯 Đẩy / Gửi có chọn Role...",
                       actionPerformed=lambda e: self._tree_action(self.full_tree, lambda: self._open_push_dialog("push")))
        bar.add(push)
        copy_btn = JButton("📋 Copy", actionPerformed=lambda e: self._on_copy_from(self.full_tree))
        copy_btn.setToolTipText("Copy 'STT. path' của API / nhánh đang chọn (Ctrl+Shift+C)")
        bar.add(copy_btn)
        self.btn_full_tree_more = JButton("Thao tác ▾", actionPerformed=lambda e: self._show_full_tree_menu())
        bar.add(self.btn_full_tree_more)
        # Few, short buttons: the bar must still fit when the tree is popped out into a narrow window.
        expand = JButton("+", actionPerformed=lambda e: self._expand_folders(self.full_tree, True))
        expand.setToolTipText("Mở tất cả các nhánh")
        collapse = JButton("−", actionPerformed=lambda e: self._expand_folders(self.full_tree, False))
        collapse.setToolTipText("Thu gọn tất cả")
        bar.add(expand)
        bar.add(collapse)
        self.lbl_full_tree = JLabel(" ")
        bg, fg = _ui_colors()
        self.lbl_full_tree.setForeground(_mix(fg, bg, 0.42))
        self.lbl_full_tree.setBorder(BorderFactory.createEmptyBorder(0, 8, 2, 8))
        head = JPanel(BorderLayout())
        head.add(bar, BorderLayout.NORTH)
        head.add(self.lbl_full_tree, BorderLayout.SOUTH)
        # The tree + its toolbar move as one piece between the tab and the separate window.
        self.full_tree_content = JPanel(BorderLayout())
        self.full_tree_content.add(head, BorderLayout.NORTH)
        # Like Proxy > HTTP history: the tree on top, the selected request / response below.
        controller = _TreeViewerController(self)
        self._tree_entry = None
        self._tree_entry_shown = None
        self.tree_req_viewer = self.callbacks.createMessageEditor(controller, False)
        self.tree_resp_viewer = self.callbacks.createMessageEditor(controller, False)
        self.lbl_tree_req = JLabel(" Request - chọn 1 API / role trong cây")
        self.lbl_tree_resp = JLabel(" Response")
        for lbl in (self.lbl_tree_req, self.lbl_tree_resp):
            lbl.setFont(lbl.getFont().deriveFont(Font.BOLD))
        req_panel = JPanel(BorderLayout())
        req_panel.add(self.lbl_tree_req, BorderLayout.NORTH)
        req_panel.add(self.tree_req_viewer.getComponent(), BorderLayout.CENTER)
        resp_panel = JPanel(BorderLayout())
        resp_panel.add(self.lbl_tree_resp, BorderLayout.NORTH)
        resp_panel.add(self.tree_resp_viewer.getComponent(), BorderLayout.CENTER)
        self.tree_viewer_split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, req_panel, resp_panel)
        self.tree_viewer_split.setResizeWeight(0.5)
        self.tree_viewer_split.setPreferredSize(Dimension(600, 340))
        self.tree_main_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.full_tree),
                                          self.tree_viewer_split)
        self.tree_main_split.setResizeWeight(0.5)
        self.tree_main_split.setOneTouchExpandable(True)
        self.full_tree_content.add(self.tree_main_split, BorderLayout.CENTER)

        self.full_tree_placeholder = JPanel(FlowLayout(FlowLayout.CENTER, 8, 40))
        self.full_tree_placeholder.add(JLabel("Cây Sub-folder đang mở ở cửa sổ riêng."))
        self.full_tree_placeholder.add(JButton("Gắn lại vào tab", actionPerformed=lambda e: self._close_tree_window()))
        self.full_tree_tab = JPanel(BorderLayout())
        self.full_tree_tab.add(self.full_tree_content, BorderLayout.CENTER)
        return self.full_tree_tab

    def _on_full_tree_selected(self):
        self._on_tree_used(self.full_tree)
        path = self.full_tree.getSelectionPath()
        kind, payload = self._extract_node_kind_payload(path.getLastPathComponent() if path is not None else None)
        g, res = tree_entry_for(kind, payload)
        if res is not None:
            self._show_tree_entry(g, res)

    def _show_tree_entry(self, g, res):
        """Show one entry below the tree (read-only, like Proxy history; Burp's own menu still works)."""
        self._tree_entry = (g, res) if res is not None else None
        empty = self.helpers.stringToBytes("")
        if res is None:
            self.lbl_tree_req.setText(" Request - chọn 1 API / role trong cây")
            self.lbl_tree_resp.setText(" Response")
            self.tree_req_viewer.setMessage(empty, True)
            self.tree_resp_viewer.setMessage(empty, False)
            self._tree_entry_shown = None
            return
        request = res.request
        response = res.response
        self.lbl_tree_req.setText(" Request [%s | %s]  %s %s" % (format_group_id(g.gid), res.role_name, g.method,
                                                                  strip_query(g.path)))
        st = res.status if res.status is not None else res.state
        ln = res.length if res.length is not None else "-"
        self.lbl_tree_resp.setText(" Response [%s | Status: %s | Length: %s]" % (res.role_name, st, ln))
        self.tree_req_viewer.setMessage(request if request is not None else empty, True)
        self.tree_resp_viewer.setMessage(response if response is not None else empty, False)
        self._tree_entry_shown = (id(res), id(response), res.state)

    def _refresh_tree_entry(self):
        """A response that arrives for the entry under the tree is shown without re-selecting it."""
        entry = getattr(self, "_tree_entry", None)
        if not entry or getattr(self, "tree_req_viewer", None) is None:
            return
        g, res = entry
        if (id(res), id(res.response), res.state) != self._tree_entry_shown:
            self._show_tree_entry(g, res)

    def _show_full_tree_menu(self):
        tree = self.full_tree
        menu = JPopupMenu()
        for label, fn in [
            ("▶ Gửi mục đang chọn (nhánh / API / role)", lambda: self._on_replay_selected_hierarchy_or_feature(None)),
            ("📤 Đẩy mục đang chọn -> Burp Repeater", lambda: self._on_send_selected_hierarchy_repeater(None)),
            ("🎯 Gửi có chọn Role...", lambda: self._open_push_dialog("send")),
            ("📋 Copy STT + Path (Ctrl+Shift+C)", lambda: self._on_copy_scope()),
            ("📋 Copy path nhánh", lambda: self._on_copy_branch_path()),
            ("🎛 Bật / Tắt Role cho mục đang chọn...", lambda: self._open_scope_for_selection(False)),
            (None, None),
            ("🎯 Đặt làm nhánh đang bắt (Active Path)", lambda: self._on_set_selected_feature_active(None)),
            ("➕ Thêm Sub-folder con...", lambda: self._on_add_subfolder_to_selected_tree(None)),
            ("✏ Đổi tên nhánh...", lambda: self._on_rename_selected_feature(None)),
            ("🗑 Xóa nhánh...", lambda: self._on_delete_selected_tree_branch(None)),
        ]:
            if label is None:
                menu.addSeparator()
                continue
            item = JMenuItem(label)
            item.addActionListener(_Action(lambda e, f=fn: self._tree_action(tree, f)))
            menu.add(item)
        btn = self.btn_full_tree_more
        menu.show(btn, 0, btn.getHeight())

    def _update_full_tree_header(self):
        label = getattr(self, "lbl_full_tree", None)
        if label is None:
            return
        stats = self._stats
        total = stats.total if stats is not None else 0
        label.setText("Nhánh đang bắt: %s   ·   %d nhánh, %d API   ·   Chuột phải để Gửi / Đẩy / Thêm / Sửa / Xóa; "
                      "chọn 1 API để xem ở tab API Groups" % (self.active_feature().name, len(self.features_list()), total))

    def _tree_action(self, tree, fn):
        """Run a tree action against this tree's selection (not the other tree's)."""
        self._menu_tree = tree
        self._scope_source = "tree"
        fn()

    def _expand_folders(self, tree, expand):
        state = self._tree_states["full"]
        rows = range(tree.getRowCount() - 1, -1, -1) if not expand else None
        if expand:
            i = 0
            while i < tree.getRowCount():
                node = tree.getPathForRow(i).getLastPathComponent()
                if getattr(node, "kind", None) in ("ROOT", "FOLDER"):
                    tree.expandRow(i)
                i += 1
            state["collapsed"] = set()
        else:
            for i in rows:
                if i > 0:
                    tree.collapseRow(i)
            state["expanded"] = set()

    def _on_toggle_tree_window(self, event):
        if self._tree_window is not None:
            self._close_tree_window()
        else:
            self._open_tree_window()

    def _open_tree_window(self):
        frame = JFrame("theMythOfCrawl - Cây Sub-folder")
        frame.setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE)
        frame.addWindowListener(_WindowClosing(lambda: self._close_tree_window()))
        self.full_tree_tab.remove(self.full_tree_content)
        self.full_tree_tab.add(self.full_tree_placeholder, BorderLayout.CENTER)
        self.full_tree_tab.revalidate()
        self.full_tree_tab.repaint()
        window_bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        pin = JCheckBox("📌 Luôn nằm trên các cửa sổ khác")
        pin.addActionListener(_Action(lambda e: frame.setAlwaysOnTop(pin.isSelected())))
        window_bar.add(pin)
        root = JPanel(BorderLayout())
        root.add(window_bar, BorderLayout.NORTH)
        root.add(self.full_tree_content, BorderLayout.CENTER)
        frame.getContentPane().add(root)
        try:
            self.callbacks.customizeUiComponent(root)
        except (Throwable, Exception):
            pass
        self._ensure_tree_renderers()
        frame.setSize(Dimension(980, 900))
        frame.setLocationRelativeTo(self.main_panel)
        frame.setVisible(True)
        self._tree_window = frame
        self.btn_tree_window.setText("🗗 Gắn lại vào tab")
        self._stale_full = True
        self._ui_tick(None)

    def _close_tree_window(self):
        frame = self._tree_window
        if frame is None:
            return
        self._tree_window = None
        frame.getContentPane().removeAll()
        frame.dispose()
        self.full_tree_tab.remove(self.full_tree_placeholder)
        self.full_tree_tab.add(self.full_tree_content, BorderLayout.CENTER)
        self.full_tree_tab.revalidate()
        self.full_tree_tab.repaint()
        self.btn_tree_window.setText("🗗 Mở cửa sổ riêng")
        self._stale_full = True
        self._ui_tick(None)

    # ---- "Độ phủ Excel" tab: which documented APIs were captured
    def _build_coverage_tab(self):
        panel = JPanel(BorderLayout(4, 4))
        bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        btn_load = JButton("Nạp file Excel (.xlsx)...", actionPerformed=self._on_load_targets)
        btn_load.setFont(btn_load.getFont().deriveFont(Font.BOLD))
        btn_load.setBackground(Color(219, 39, 119))
        btn_load.setForeground(Color(255, 255, 255))
        bar.add(btn_load)
        self.btn_target_clear = JButton("Bỏ danh sách", actionPerformed=self._on_clear_targets)
        bar.add(self.btn_target_clear)
        btn_export = JButton("Xuất Excel độ phủ (.xlsx)...", actionPerformed=self._on_export_excel)
        bar.add(btn_export)
        bar.add(JButton("Gửi các API đã bắt trong danh sách", actionPerformed=self._on_send_target_groups))
        self.cb_target_only_mirror = JCheckBox("Chỉ bắt API có trong danh sách",
                                               self.config.get("target_only", False))
        self.cb_target_only_mirror.addActionListener(_Action(self._on_target_only_mirror))
        bar.add(self.cb_target_only_mirror)
        bar.add(JButton("Đặt lại bộ đếm lượt gặp", actionPerformed=self._on_reset_hits))
        bar.add(JLabel("   Xem:"))
        self.cb_coverage_filter = JComboBox(CoverageTableModel.FILTERS)
        self.cb_coverage_filter.addActionListener(_Action(lambda e: self._reload_coverage()))
        bar.add(self.cb_coverage_filter)

        self.lbl_coverage = JLabel(" ")
        self.lbl_coverage.setFont(_font_resized(self.lbl_coverage.getFont(), Font.BOLD, 1))
        self.lbl_coverage.setBorder(BorderFactory.createEmptyBorder(2, 8, 4, 8))
        top = JPanel(BorderLayout())
        top.add(bar, BorderLayout.NORTH)
        top.add(self.lbl_coverage, BorderLayout.SOUTH)
        panel.add(top, BorderLayout.NORTH)

        self.coverage_model = CoverageTableModel()
        self.coverage_table = JTable(self.coverage_model)
        style_data_table(self.coverage_table)
        self.coverage_table.setAutoCreateRowSorter(True)
        self.coverage_table.addMouseListener(_DoubleClick(self._on_coverage_jump))
        renderer = AuditTableRenderer(self.coverage_model, audit_col=8, method_col=1, bold_cols=(0, 4))
        for col, width in ((0, 64), (1, 80), (2, 300), (3, 220), (4, 150), (5, 110), (6, 260), (7, 220), (8, 240),
                           (9, 230), (10, 380), (11, 170), (12, 300)):
            column = self.coverage_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(renderer)
        cm = self.coverage_table.getColumnModel()
        cm.moveColumn(CoverageTableModel.HITS_COL, 5)
        cm.moveColumn(CoverageTableModel.PLACES_COL, 6)
        self.coverage_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_coverage_selected))

        # Below: every time the selected row was met (audit of real paths and positions)
        self.hit_model = HitTableModel()
        self.hit_table = JTable(self.hit_model)
        style_data_table(self.hit_table)
        self.hit_table.addMouseListener(_DoubleClick(self._on_hit_jump))
        hit_renderer = AuditTableRenderer(self.hit_model, audit_col=2, method_col=4, bold_cols=(0,))
        for col, width in ((0, 45), (1, 120), (2, 130), (3, 70), (4, 70), (5, 320), (6, 160), (7, 260),
                           (8, 260), (9, 70), (10, 200)):
            column = self.hit_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(hit_renderer)
        self.lbl_hits = JLabel(" Chọn 1 dòng Excel để xem các lần đã gặp (path thực tế, vị trí, kết quả).")
        self.lbl_hits.setFont(self.lbl_hits.getFont().deriveFont(Font.BOLD))
        self.lbl_hits.setBorder(BorderFactory.createEmptyBorder(3, 6, 3, 6))
        hits_panel = JPanel(BorderLayout())
        hits_panel.add(self.lbl_hits, BorderLayout.NORTH)
        hits_panel.add(JScrollPane(self.hit_table), BorderLayout.CENTER)
        split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.coverage_table), hits_panel)
        split.setResizeWeight(0.62)
        split.setOneTouchExpandable(True)
        panel.add(split, BorderLayout.CENTER)
        self.coverage_panel = panel
        self._refresh_target_controls()
        return panel

    def _reload_coverage(self):
        model = getattr(self, "coverage_model", None)
        if model is None:
            return
        keep = self._selected_coverage_entry()
        groups = self.group_model.all_groups() if self.group_model is not None else []
        model.reload(self.targets, groups, self.cb_coverage_filter.getSelectedIndex(), self.target_hits)
        if keep is not None:
            self._select_coverage_entry(keep, scroll=False)
        else:
            self._on_coverage_selected()
        self._refresh_target_controls(groups)

    def _selected_coverage_entry(self):
        table = getattr(self, "coverage_table", None)
        if table is None:
            return None
        vr = table.getSelectedRow()
        return self.coverage_model.entry_at(table.convertRowIndexToModel(vr)) if vr >= 0 else None

    def _select_coverage_entry(self, entry, scroll=True):
        table = self.coverage_table
        r = self.coverage_model.row_of_entry(entry)
        if r < 0:
            return False
        vr = table.convertRowIndexToView(r)
        if vr < 0:
            return False
        table.setRowSelectionInterval(vr, vr)
        if scroll:
            table.scrollRectToVisible(table.getCellRect(vr, 0, True))
        return True

    def _on_coverage_selected(self):
        label = getattr(self, "lbl_hits", None)
        if label is None:
            return
        e = self._selected_coverage_entry()
        if e is None:
            self.hit_model.set_events([])
            label.setText(" Chọn 1 dòng Excel để xem các lần đã gặp (path thực tế, vị trí, kết quả).")
            return
        events = self.target_hits.events(e)
        self.hit_model.set_events(events)
        places = self.target_hits.positions(e)
        label.setText(u" Dòng STT %s · %s %s · gặp %s%s%s" % (
            u_text(e.stt), e.method_label(), e.path, hit_cell(self.target_hits, e) or u"0",
            (u" · ở %d vị trí: %s" % (len(places), u"; ".join(places[:4]))) if places else u"",
            u"   (click đúp 1 dòng bên dưới để mở API)" if events else u""))

    def _on_hit_jump(self):
        vr = self.hit_table.getSelectedRow()
        if vr < 0:
            return
        gid = self.hit_model.gid_at(self.hit_table.convertRowIndexToModel(vr))
        g = self._group_by_gid(gid)
        if g is None:
            self._flash_status(u"API #%s không còn (đã xóa)" % gid if gid else u"Lượt gặp này không tạo API")
            return
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self.tabs.setSelectedIndex(0)
        self._select_group_in_table(g)

    def _group_by_gid(self, gid):
        if gid is None or self.group_model is None:
            return None
        for g in self.group_model.all_groups():
            if g.gid == gid:
                return g
        return None

    def jump_to_target(self, entry):
        """Open the 'Độ phủ Excel' tab on this row of the file (and its hit audit below)."""
        if entry is None or getattr(self, "coverage_panel", None) is None:
            return
        self.tabs.setSelectedComponent(self.coverage_panel)
        self._reload_coverage()
        if self.coverage_model.row_of_entry(entry) < 0 and self.cb_coverage_filter.getSelectedIndex() != 0:
            self.cb_coverage_filter.setSelectedIndex(0)
            self._reload_coverage()
        if self._select_coverage_entry(entry):
            self.coverage_table.requestFocusInWindow()
            self._flash_status(u"Excel: dòng STT %s · %s %s" % (u_text(entry.stt), entry.method_label(), entry.path))

    def _excel_tooltip(self, g):
        e = getattr(g, "target", None) if g is not None else None
        if e is None:
            return u"API không có trong file Excel" if self.targets else None
        n, new, dup, filtered = self.target_hits.stats(e)
        return u"Bấm để mở dòng STT %s trong tab Độ phủ Excel (%s %s) · đã gặp %d lần" % (
            u_text(e.stt), e.method_label(), e.path, n)

    def _on_group_cell_click(self, model_row, model_col):
        g = self.group_model.group_at(model_row)
        if g is None:
            return
        self.on_chip("copy" if model_col == GroupTableModel.COPY_COL else "excel", g)

    def on_chip(self, kind, g):
        if kind == "copy":
            line = self.copy_groups([g])
            self._flash_status(u"📋 Đã copy: %s" % line)
        elif getattr(g, "target", None) is not None:
            self.jump_to_target(g.target)

    def tree_chip_at(self, tree, x, y):
        """('copy' | 'excel', group) under the mouse on an API row of a tree, else None."""
        path = tree.getPathForLocation(x, y)
        if path is None:
            return None
        node = path.getLastPathComponent()
        kind, g = self._extract_node_kind_payload(node)
        if kind != "GROUP" or g is None:
            return None
        renderer = tree.getCellRenderer()
        if not isinstance(renderer, HierarchyTreeRenderer):
            return None
        bounds = tree.getPathBounds(path)
        comp = renderer.getTreeCellRendererComponent(tree, node, False, False, True, tree.getRowForPath(path), False)
        icon = comp.getIcon()
        rel = x - bounds.x - comp.getInsets().left
        if isinstance(icon, _GroupIcon) and _GroupIcon.COPY_X - 1 <= rel <= icon.getIconWidth() + 1:
            return "copy", g
        badge = excel_badge(g)
        text = u_text(comp.getText())
        if badge and badge in text:
            fm = comp.getFontMetrics(comp.getFont())
            start = (icon.getIconWidth() if icon is not None else 0) + comp.getIconTextGap() + \
                fm.stringWidth(text[:text.index(badge)])
            if start - 2 <= rel <= start + fm.stringWidth(badge) + 2:
                return "excel", g
        return None

    def _refresh_target_controls(self, groups=None):
        targets = self.targets
        loaded = bool(targets)
        info = getattr(self, "lbl_target_info", None)
        if info is not None:
            info.setText((u"Đã nạp %d API từ %s (sheet %s)" % (len(targets), targets.source, targets.sheet))
                         if loaded else u"Chưa nạp file - extension bắt API như bình thường")
        for name in ("cb_target_only", "cb_target_only_mirror", "btn_target_clear"):
            widget = getattr(self, name, None)
            if widget is not None:
                widget.setEnabled(loaded)
        mirror = getattr(self, "cb_target_only_mirror", None)
        if mirror is not None:
            mirror.setSelected(bool(self.config.get("target_only", False)))
        label = getattr(self, "lbl_coverage", None)
        if label is None:
            return
        if not loaded:
            label.setText(u"Chưa nạp file. Bấm 'Nạp file Excel' - file cần các cột STT | PROTOCOL (method) | PATH | "
                          u"POSITION (tùy chọn); tham số {id} [id] (id) <id> :id * trong path được hiểu là giá trị bất kỳ.")
            return
        if groups is None:
            groups = self.group_model.all_groups() if self.group_model is not None else []
        hit = len([1 for e, found in coverage_rows(targets, groups) if found])
        total = len(targets)
        mode = u"chỉ bắt API trong danh sách" if self.config.get("target_only") else u"bắt mọi API (danh sách chỉ để đối chiếu)"
        outside = len([1 for g in groups if getattr(g, "target", None) is None])
        copied = len([1 for g in groups if getattr(g, "copied_label", None)])
        dups = len(targets.duplicates()) if hasattr(targets, "duplicates") else 0
        extra = []
        if outside:
            extra.append(u"%d API ngoài danh sách" % outside)
        if dups:
            extra.append(u"%d dòng trùng trong file" % dups)
        if copied:
            extra.append(u"📋 đã copy %d" % copied)
        label.setText(u"%s  ·  %d API  ·  Đã bắt %d/%d (%d%%)  ·  Còn %d chưa bắt%s  ·  Chế độ: %s"
                      % (targets.source, total, hit, total, (hit * 100 // total) if total else 0, total - hit,
                         "".join([u"  ·  " + x for x in extra]), mode))

    def set_targets(self, targets):
        self.targets = targets if targets else None
        sig = targets_signature(self.targets)
        if sig != self.target_hits.signature:
            self.target_hits.reset(sig)
            self._save_hits(True)
        try:
            self.callbacks.saveExtensionSetting(SETTINGS_KEY_TARGETS, targets.to_json() if targets else "")
        except (Throwable, Exception):
            self._print_error("Could not save the Excel API list:\n%s" % u_text(traceback.format_exc()))
        self._retag_groups()

    def _save_hits(self, force=False):
        hits = self.target_hits
        if not (hits.dirty or force):
            return
        now = time.time()
        if not force and now - self._hits_saved_at < 3.0:
            return
        self._hits_saved_at = now
        try:
            self.callbacks.saveExtensionSetting(SETTINGS_KEY_TARGET_HITS, hits.to_json())
        except (Throwable, Exception):
            self._print_error("Could not save the Excel hit counters:\n%s" % u_text(traceback.format_exc()))

    def _on_reset_hits(self, event):
        if JOptionPane.showConfirmDialog(self.main_panel, "Đặt lại bộ đếm lượt gặp của mọi dòng Excel về 0?",
                                         EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.target_hits.reset(targets_signature(self.targets))
        self._save_hits(True)
        self._stale_coverage = True
        self._ui_tick(None)

    def _target_match(self, method, path, host=None, cfg=None):
        targets = self.targets
        if not targets:
            return None
        cfg = cfg or self.config
        return targets.match(method, path, cfg.get("target_allow_prefix", False), host,
                             cfg.get("target_ids_as_params", True), cfg.get("target_query_mode", "ignore"))

    def _retag_groups(self):
        """Match every already captured API against the current list (after load / option change)."""
        if self.group_model is None:
            return
        for g in self.group_model.all_groups():
            g.target = self._target_match(g.method, g.path, g.host) if self.targets else None
        self._stale_coverage = True
        self._refresh_feature_views()

    def _on_load_targets(self, event):
        chooser = JFileChooser()
        chooser.setFileFilter(FileNameExtensionFilter("Excel (.xlsx)", "xlsx"))
        if chooser.showOpenDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        try:
            sheet_names = xlsx_sheet_names(f.getAbsolutePath())
            index = 0
            if len(sheet_names) > 1:
                pick = JOptionPane.showInputDialog(
                    self.main_panel, "File có %d sheet. Chọn sheet chứa danh sách API:" % len(sheet_names),
                    EXT_NAME, JOptionPane.QUESTION_MESSAGE, None, sheet_names, sheet_names[0])
                if pick is None:
                    return
                index = list(sheet_names).index(pick)
            sheet, rows = read_xlsx_rows(f.getAbsolutePath(), index)
            targets = build_target_list(rows, f.getName(), sheet)
        except (Throwable, Exception) as e:
            JOptionPane.showMessageDialog(self.main_panel, "Không đọc được file Excel: %s" % u_text(e), EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)
            return
        if not len(targets):
            JOptionPane.showMessageDialog(
                self.main_panel, "Không tìm thấy dòng API nào. File cần có cột PATH (hoặc URL / Endpoint) chứa "
                                 "đường dẫn bắt đầu bằng '/'.", EXT_NAME, JOptionPane.WARNING_MESSAGE)
            return
        self.set_targets(targets)
        groups = self.group_model.all_groups()
        already = len([1 for e, found in coverage_rows(targets, groups) if found])
        self.log("Đã nạp %d API từ file Excel %s (sheet %s); khớp sẵn %d API đã bắt."
                 % (len(targets), targets.source, targets.sheet, already))
        choice = JOptionPane.showConfirmDialog(
            self.main_panel,
            "Đã nạp %d API từ %s.\n%d API trong danh sách đã được bắt từ trước.\n\n"
            "Bật chế độ 'Chỉ bắt API có trong danh sách'?\n(Không: vẫn bắt mọi API, danh sách chỉ để theo dõi độ phủ)"
            % (len(targets), targets.source, already), EXT_NAME, JOptionPane.YES_NO_OPTION)
        self._set_target_only(choice == JOptionPane.YES_OPTION)
        self.tabs.setSelectedComponent(self.coverage_panel)

    def _on_clear_targets(self, event):
        if not self.targets:
            return
        if JOptionPane.showConfirmDialog(self.main_panel, "Bỏ danh sách API từ file %s?" % self.targets.source,
                                         EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self._set_target_only(False)
        self.set_targets(None)
        self.log("Đã bỏ danh sách API từ file Excel.")
        self._ui_tick(None)

    def _set_target_only(self, enabled):
        cb = getattr(self, "cb_target_only", None)
        if cb is not None:
            cb.setSelected(bool(enabled))
            self._on_settings_changed(None)
        else:
            cfg = self.get_config()
            cfg["target_only"] = bool(enabled)
            self.apply_config(cfg)
        self._stale_coverage = True
        self._ui_tick(None)

    def _on_target_only_mirror(self, event):
        self._set_target_only(self.cb_target_only_mirror.isSelected())

    def _on_send_target_groups(self, event):
        groups = [g for g in self.group_model.all_groups() if getattr(g, "target", None) is not None]
        pending = [(g, [r for r in g.results if r.state == STATE_NOT_SENT]) for g in groups]
        pending = [(g, rs) for g, rs in pending if rs]
        if not pending:
            JOptionPane.showMessageDialog(self.main_panel, "Không có API nào trong danh sách đang chờ gửi.",
                                          EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        for g, rs in pending:
            self.replay(g, rs)
        self.log("Xếp hàng gửi %d API thuộc danh sách Excel." % len(pending))

    def _on_coverage_jump(self):
        vr = self.coverage_table.getSelectedRow()
        if vr < 0:
            return
        groups = self.coverage_model.groups_at(self.coverage_table.convertRowIndexToModel(vr))
        if not groups:
            return
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self.tabs.setSelectedIndex(0)
        self._select_group_in_table(groups[0])

    # ---- Log tab: grouped, collapsed, loaded on expand
    def _build_log_tab(self):
        panel = JPanel(BorderLayout(4, 4))
        bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        btn_xlsx = JButton("Xuất Excel (.xlsx)...", actionPerformed=self._on_export_excel)
        btn_xlsx.setFont(btn_xlsx.getFont().deriveFont(Font.BOLD))
        btn_xlsx.setBackground(Color(22, 163, 74))
        btn_xlsx.setForeground(Color(255, 255, 255))
        bar.add(btn_xlsx)
        bar.add(JButton("Mở các nhánh", actionPerformed=self._on_log_expand_branches))
        bar.add(JButton("Thu gọn tất cả", actionPerformed=self._on_log_collapse_all))
        bar.add(JButton("Xóa nhật ký hệ thống", actionPerformed=self._on_log_clear_system))
        hint = JLabel("   Mỗi nhánh > API > chi tiết chỉ được tải khi bạn bấm mở. Click đúp 1 API để xem ở tab API Groups.")
        bg, fg = _ui_colors()
        hint.setForeground(_mix(fg, bg, 0.42))
        bar.add(hint)
        panel.add(bar, BorderLayout.NORTH)

        self.log_tree_model = DefaultTreeModel(HierarchyTreeNode("ROOT", "", "Nhật ký", key=("ROOT",)))
        self.log_tree = JTree(self.log_tree_model)
        self.log_tree.setRootVisible(False)
        self.log_tree.setShowsRootHandles(True)
        self.log_tree.setRowHeight(26)
        self.log_tree.setLargeModel(True)
        self.log_tree.setCellRenderer(HierarchyTreeRenderer())
        self.log_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.log_tree.addTreeWillExpandListener(_LazyTreeLoader(
            lambda node: self._lazy_load_tree_node("log", self.log_tree_model, node)))
        self.log_tree.addMouseListener(_DoubleClick(self._on_log_jump_to_group))
        panel.add(JScrollPane(self.log_tree), BorderLayout.CENTER)
        return panel

    def _on_log_expand_branches(self, event):
        tree = self.log_tree
        for i in range(tree.getRowCount() - 1, -1, -1):
            node = tree.getPathForRow(i).getLastPathComponent()
            if getattr(node, "kind", None) == "LOGBRANCH":
                tree.expandRow(i)

    def _on_log_collapse_all(self, event):
        tree = self.log_tree
        for i in range(tree.getRowCount() - 1, -1, -1):
            tree.collapseRow(i)
        self._tree_states["log"]["expanded"] = set()

    def _on_log_clear_system(self, event):
        with self._log_lock:
            self._log_system.clear()
        self._stale_log = True
        self._ui_tick(None)

    def _on_log_jump_to_group(self):
        path = self.log_tree.getSelectionPath()
        if path is None:
            return
        node = path.getLastPathComponent()
        kind = getattr(node, "kind", None)
        if kind == "LOGAPI":
            group, res = node.payload, None
        elif kind == "LOGRES":
            group, res = node.payload
        else:
            return
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self.tabs.setSelectedIndex(0)
        self._select_group_in_table(group, target_result=res)

    def _on_export_excel(self, event):
        groups = self.group_model.all_groups() if self.group_model is not None else []
        if not groups and not self.targets:
            JOptionPane.showMessageDialog(self.main_panel, "Chưa có API nào để xuất.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        chooser = JFileChooser()
        chooser.setSelectedFile(File("theMythOfCrawl_API_%s.xlsx" % time.strftime("%Y%m%d_%H%M")))
        chooser.setFileFilter(FileNameExtensionFilter("Excel (.xlsx)", "xlsx"))
        if chooser.showSaveDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        if not f.getName().lower().endswith(".xlsx"):
            f = File(f.getAbsolutePath() + ".xlsx")
        if f.exists() and JOptionPane.showConfirmDialog(
                self.main_panel, "Ghi đè %s?" % f.getName(), EXT_NAME,
                JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        try:
            cfg = self.get_config()
            data = build_api_workbook(groups, self.targets, cfg.get("copy_format"),
                                      cfg.get("excel_position_copy_format", True),
                                      lambda g: self.copy_label_for(g, assign=False), self.target_hits)
            out = open(f.getAbsolutePath(), "wb")
            try:
                out.write(data)
            finally:
                out.close()
            self.log("Đã xuất %d API ra Excel: %s" % (len(groups), f.getAbsolutePath()))
            JOptionPane.showMessageDialog(self.main_panel, "Đã xuất %d API ra:\n%s" % (len(groups), f.getAbsolutePath()),
                                          EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
        except (Throwable, Exception) as e:
            JOptionPane.showMessageDialog(self.main_panel, "Xuất Excel thất bại: %s" % u_text(e), EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)

    # ---- History & Features tab (Minimalist top bar + Right-click tree menu + Audit summary)
    def _build_history_tab(self):
        panel = JPanel(BorderLayout(4, 4))
        top_bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        top_bar.add(JButton("▶ Gửi mục đang chọn", actionPerformed=self._on_replay_tree_selection))
        top_bar.add(JButton("📤 Đẩy -> Burp Repeater", actionPerformed=self._on_send_tree_repeater))
        top_bar.add(JButton("+ Sub-folder con...", actionPerformed=self._on_append_subfolder))
        top_bar.add(JButton("+ Nhánh mới...", actionPerformed=self._on_next_feature))
        top_bar.add(JButton("✏ Đổi tên...", actionPerformed=self._on_rename_tree_feature))
        top_bar.add(JButton("🔍 Xem ở tab API Groups", actionPerformed=self._on_jump_to_group_from_tree))
        top_bar.add(JButton("📊 Xuất Excel (.xlsx)...", actionPerformed=self._on_export_excel))
        top_bar.add(JButton("📄 Export Báo cáo (.txt/.md)...", actionPerformed=self._on_export_history_report))
        top_bar.add(JButton("↻ Refresh", actionPerformed=lambda e: self._refresh_feature_views()))
        panel.add(top_bar, BorderLayout.NORTH)

        root = HierarchyTreeNode("ROOT", "", "Lịch sử Chức năng & API")
        self.history_tree_model = DefaultTreeModel(root)
        self.history_tree = JTree(self.history_tree_model)
        self.history_tree.setRowHeight(26)
        self.history_tree.setLargeModel(True)
        self.history_tree.setCellRenderer(HierarchyTreeRenderer())
        self.history_tree.addTreeWillExpandListener(_LazyTreeLoader(
            lambda node: self._lazy_load_tree_node("history", self.history_tree_model, node)))
        self.history_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.history_tree.addTreeSelectionListener(_TreeListener(self._on_history_tree_selected))
        self.history_tree.addMouseListener(
            _TreePopupListener(self.history_tree, self._show_history_tree_popup))

        tree_panel = JPanel(BorderLayout())
        tree_panel.setBorder(BorderFactory.createTitledBorder(
            "Cây phân cấp Sub-folder & API (Chuột phải vào mục bất kỳ để Gửi / Đổi tên / Xem chi tiết)"))
        tree_panel.add(JScrollPane(self.history_tree), BorderLayout.CENTER)

        self.history_summary_area = JTextArea()
        self.history_summary_area.setEditable(False)
        self.history_summary_area.setFont(Font("Monospaced", Font.PLAIN, 12))
        summary_panel = JPanel(BorderLayout())
        summary_panel.setBorder(BorderFactory.createTitledBorder(
            "Bản tổng hợp Audit (Danh sách Chức năng, API theo thứ tự & kết quả các Role)"))
        summary_panel.add(JScrollPane(self.history_summary_area), BorderLayout.CENTER)

        split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, tree_panel, summary_panel)
        split.setResizeWeight(0.42)
        panel.add(split, BorderLayout.CENTER)
        return panel

    # ---- Roles tab (Minimalist top bar + Right-click role table + Inline full RoleEditorPanel on right)
    def _build_roles_tab(self):
        panel = JPanel(BorderLayout(4, 4))
        self.role_model = RoleTableModel(self)
        self.role_table = JTable(self.role_model)
        self.role_table.setRowHeight(24)
        self.role_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.role_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_role_row_selected))
        self.role_table.addMouseListener(_DoubleClick(lambda: self._on_edit_role(None)))
        self.role_table.addMouseListener(
            _TablePopupListener(self.role_table, self._show_role_table_popup))
        for col, width in ((0, 35), (1, 55), (2, 160), (3, 360)):
            self.role_table.getColumnModel().getColumn(col).setPreferredWidth(width)
        self.role_model.reload()

        left_panel = JPanel(BorderLayout(2, 2))
        left_panel.setBorder(BorderFactory.createTitledBorder(
            "Danh sách Role / Profile (Click chọn để sửa bên phải | Chuột phải để Nhân bản / Xóa / Đổi thứ tự)"))

        role_top_bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        role_top_bar.add(JButton("+ Thêm Role...", actionPerformed=self._on_add_role))
        role_top_bar.add(JButton("✏ Sửa Dialog...", actionPerformed=self._on_edit_role))
        role_top_bar.add(JButton("🗑 Xóa", actionPerformed=self._on_delete_roles))
        self.btn_role_more = JButton("⚙ Thao tác Role ▾",
                                     actionPerformed=lambda e: self._show_role_actions_menu(self.btn_role_more))
        role_top_bar.add(self.btn_role_more)
        btn_scope = JButton("🎛 Bật/Tắt theo phạm vi...", actionPerformed=lambda e: self.open_role_scope_dialog(False))
        btn_scope.setToolTipText("Tắt / bật role cho toàn bộ, cho từng nhánh hoặc từng API gốc")
        role_top_bar.add(btn_scope)

        north = JPanel(BorderLayout(2, 4))
        north.add(role_top_bar, BorderLayout.NORTH)
        north.add(self._build_original_profile_bar(), BorderLayout.SOUTH)
        left_panel.add(north, BorderLayout.NORTH)
        left_panel.add(JScrollPane(self.role_table), BorderLayout.CENTER)

        first_role = self.roles.get(0) if self.roles.count() > 0 else {
            "name": "01_Admin", "enabled": True, "headers": []
        }
        self.inline_role_editor = RoleEditorPanel(first_role, inline_save_fn=self._on_save_inline_role)
        self.inline_role_editor.setBorder(BorderFactory.createTitledBorder(
            "Chỉnh sửa Profile đang chọn (Header / Cookie / Session / JWT - Bấm 'Save Profile Changes' để lưu)"))

        split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, left_panel, self.inline_role_editor)
        split.setResizeWeight(0.38)
        panel.add(split, BorderLayout.CENTER)
        if self.roles.count() > 0:
            self.role_table.setRowSelectionInterval(0, 0)
        return panel

    def _build_original_profile_bar(self):
        """Pinned 'API gốc' profile above the role list: always present, never deleted or moved."""
        bg, fg = _ui_colors()
        pal = RowPalette.of(bg, fg)
        bar = JPanel(BorderLayout(6, 2))
        bar.setBackground(_mix(bg, pal.orig_accent, 0.08))
        bar.setBorder(BorderFactory.createCompoundBorder(
            BorderFactory.createMatteBorder(0, 4, 0, 0, pal.orig_accent),
            BorderFactory.createEmptyBorder(5, 8, 5, 8)))
        title = JLabel("📌 " + ORIGINAL_PROFILE_NAME)
        title.setFont(title.getFont().deriveFont(Font.BOLD))
        title.setForeground(pal.orig_fg)
        self.lbl_original_profile = JLabel(" ")
        self.lbl_original_profile.setForeground(pal.muted)
        text = JPanel(BorderLayout())
        text.setOpaque(False)
        text.add(title, BorderLayout.NORTH)
        text.add(self.lbl_original_profile, BorderLayout.SOUTH)
        bar.add(text, BorderLayout.CENTER)
        buttons = JPanel(FlowLayout(FlowLayout.RIGHT, 4, 0))
        buttons.setOpaque(False)
        self.cb_original_profile = JCheckBox("Áp dụng", bool(self.original_profile.get("enabled")))
        self.cb_original_profile.setOpaque(False)
        self.cb_original_profile.setToolTipText("Bật: rule của profile này được áp vào API gốc khi xem / gửi lại / đẩy Repeater")
        self.cb_original_profile.addActionListener(_Action(self._on_toggle_original_profile))
        buttons.add(self.cb_original_profile)
        buttons.add(JButton("✏ Sửa profile API gốc", actionPerformed=self._on_edit_original_profile))
        bar.add(buttons, BorderLayout.EAST)
        self._refresh_original_profile_bar()
        return bar

    def _refresh_original_profile_bar(self):
        label = getattr(self, "lbl_original_profile", None)
        if label is None:
            return
        prof = self.original_profile
        n = len(prof.get("headers", []))
        if not n:
            label.setText("Chưa có rule - API gốc được gửi đúng như lúc bắt")
        elif prof.get("enabled"):
            label.setText("Đang áp dụng %d rule cho API gốc (API bắt từ giờ; API cũ: 'Rebuild Roles')" % n)
        else:
            label.setText("%d rule - đang TẮT, API gốc được gửi đúng như lúc bắt" % n)
        cb = getattr(self, "cb_original_profile", None)
        if cb is not None and cb.isSelected() != bool(prof.get("enabled")):
            cb.setSelected(bool(prof.get("enabled")))

    def _on_toggle_original_profile(self, event):
        prof = dict(self.original_profile)
        prof["enabled"] = self.cb_original_profile.isSelected()
        self.save_original_profile(prof)
        if self._inline_target[0] == "orig":
            self.inline_role_editor.enabled_box.setSelected(prof["enabled"])
        self.log("Profile API gốc: %s." % ("BẬT" if prof["enabled"] else "TẮT"))

    def _on_edit_original_profile(self, event):
        self._inline_target = ("orig",)
        self.role_table.clearSelection()
        self.inline_role_editor.set_original_mode(True)
        self.inline_role_editor.load_role(self.original_profile)
        self.inline_role_editor.setBorder(BorderFactory.createTitledBorder(
            "Đang sửa: Profile API GỐC (Acc Crawl) - rule áp vào request gốc khi xem / gửi lại / đẩy Repeater"))

    # ---- Settings tab
    def _build_settings_tab(self, cfg):
        """Four colour-coded sections; plain Swing text only (Burp disables HTML in labels)."""
        self._syncing_settings = False
        on_change = self._on_settings_changed

        def check(text, value):
            cb = JCheckBox(text, value, actionPerformed=on_change)
            cb.setOpaque(False)
            return cb

        self.cb_scope = check("Chỉ bắt API nằm trong Target Scope của Burp", cfg["in_scope_only"])
        self.cb_static = check("Bỏ qua file tĩnh có đuôi:", cfg["ignore_static"])
        self.tf_static = JTextField(cfg["static_ext"], 50)
        self.tf_static.addActionListener(_Action(on_change))
        self.cb_regex = check("Chỉ bắt path khớp Regex:", cfg["api_regex_enabled"])
        self.tf_regex = JTextField(cfg["api_regex"], 50)
        self.tf_regex.addActionListener(_Action(on_change))
        self.cb_options = check("Bỏ qua OPTIONS / HEAD (CORS preflight)", cfg["ignore_options_head"])
        self.regex_error = JLabel("")  # empty -> takes no height until there is an error
        self.regex_error.setForeground(Color(220, 38, 38))

        self.cb_dedup = check("Chỉ nhân bản mỗi endpoint 1 lần (Method + Host + Path)", cfg["dedup"])
        self.cb_dedup_ids = check("Coi số / UUID / chuỗi hex dài trong path là {id} khi so trùng",
                                  cfg["dedup_normalize_ids"])
        self.cb_dedup_feature = check("Chống trùng riêng theo từng Nhánh (được bắt lại API cũ khi sang nhánh mới)",
                                      cfg.get("dedup_per_feature", False))

        self.cb_send_profile = JComboBox([label for _, label, _, _, _ in SEND_PROFILES])
        self.cb_send_profile.setSelectedIndex(self._profile_index(cfg["send_profile"]))
        self.cb_send_profile.addActionListener(_Action(self._on_send_profile_changed))
        self.tf_delay = self._num_field(cfg["send_delay_ms"])
        self.tf_jitter = self._num_field(cfg["send_jitter_pct"])
        self.tf_conc = self._num_field(cfg["host_concurrency"])
        self.tf_retries = self._num_field(cfg["max_retries"])
        self.tf_threads = self._num_field(cfg["threads"])
        self.lbl_pacing = JLabel(" ")
        self.cb_auto_send_original = check(
            "Khi tự động gửi: gửi lại cả API gốc (đã áp profile API gốc nếu bật)",
            cfg.get("auto_send_original", False))
        self.cb_store_disk = check("Lưu request / response vào file tạm của Burp thay vì RAM (khuyên dùng khi bắt nhiều API)",
                                   cfg.get("store_on_disk", True))

        self.cb_number = check("Thêm số thứ tự role vào tên tab (01_, 02_ ...) nếu tên chưa có",
                               cfg["number_roles_in_tab"])
        self.cb_feat_tab = check("Gắn mã Nhánh vào tên tab: [F01-G01:POST /v1/...] thay vì [G01:POST /v1/...]",
                                 cfg.get("include_feature_in_tab", False))
        self.tf_pathlen = self._num_field(cfg["short_path_len"])

        self.cb_target_only = check("Chỉ bắt API có trong danh sách Excel (thay cho bộ lọc Regex)",
                                    cfg.get("target_only", False))
        self.cb_target_position = check("Tự xếp API vào nhánh theo cột POSITION của file (nếu ô đó có giá trị)",
                                        cfg.get("target_use_position", True))
        self.cb_target_prefix = check("Cho phép path thực tế có thêm tiền tố phía trước (vd /api/v1 + /apt/test)",
                                      cfg.get("target_allow_prefix", False))
        self.cb_target_ids = check("Coi số / UUID / chuỗi hex trong file là tham số (file ghi /users/123 vẫn khớp /users/456)",
                                   cfg.get("target_ids_as_params", True))
        self.cb_target_query = JComboBox([label for _, label in TARGET_QUERY_MODES])
        self.cb_target_query.setSelectedIndex([k for k, _ in TARGET_QUERY_MODES].index(cfg["target_query_mode"]))
        self.cb_target_query.addActionListener(_Action(on_change))
        self.tf_copy_format = JTextField(cfg["copy_format"], 30)
        self.tf_copy_format.addActionListener(_Action(on_change))
        self.tf_copy_format.addFocusListener(_FocusLost(lambda: self._on_settings_changed(None)))
        self.cb_copy_fallback = JComboBox([label for _, label in COPY_STT_FALLBACKS])
        self.cb_copy_fallback.setSelectedIndex([k for k, _ in COPY_STT_FALLBACKS].index(cfg["copy_stt_fallback"]))
        self.cb_copy_fallback.addActionListener(_Action(on_change))
        self.lbl_copy_counter = JLabel(" ")
        self.cb_excel_position_copy = check("Khi xuất Excel: cột POSITION còn trống được ghi theo định dạng copy (vd 200. / > contact > button \"send\")",
                                            cfg.get("excel_position_copy_format", True))
        self.btn_target_load = JButton("Nạp file Excel (.xlsx)...", actionPerformed=self._on_load_targets)
        self.lbl_target_info = JLabel(" ")

        content = JPanel()
        content.setLayout(BoxLayout(content, BoxLayout.Y_AXIS))
        content.setBorder(BorderFactory.createEmptyBorder(10, 12, 10, 12))
        sections = [
            ("1.  Bắt API từ Proxy", (37, 99, 235),
             "Request nào đi qua Proxy được bắt và nhân bản theo Role. Bắt thủ công (chuột phải > theMythOfCrawl) "
             "luôn bỏ qua bộ lọc này, trừ mục 'apply capture filters'.",
             [("check", self.cb_scope),
              ("pair", self.cb_static, self.tf_static),
              ("pair", self.cb_regex, self.tf_regex),
              ("pair", None, self.regex_error),
              ("check", self.cb_options)]),
            ("2.  Chống trùng lặp", (147, 51, 234),
             "Tránh nhân bản lại cùng một endpoint nhiều lần.",
             [("check", self.cb_dedup), ("check", self.cb_dedup_ids), ("check", self.cb_dedup_feature)]),
            ("3.  Gửi request & chống lỗi 429", (22, 163, 74),
             "Mọi request (tự gửi sau khi crawl, gửi hàng loạt, gửi lẻ) đi qua 1 hàng đợi theo từng host, "
             "giãn cách ngẫu nhiên như người dùng thật. Gặp 429/503: tự dừng theo Retry-After, giảm tốc x2, "
             "gửi từng request một rồi gửi lại; tự nhanh dần lại sau 8 lần thành công.",
             [("field", "Chế độ gửi:", self.cb_send_profile, None),
              ("field", "Khoảng nghỉ giữa 2 request (ms):", self.tf_delay, self.lbl_pacing),
              ("field", "Dao động ngẫu nhiên (%):", self.tf_jitter, "nghỉ = khoảng nghỉ ± % này"),
              ("field", "Số request song song mỗi host:", self.tf_conc, "1 = lần lượt như người thật"),
              ("field", "Tự gửi lại khi gặp 429 / 503 (lần):", self.tf_retries, None),
              ("field", "Tổng số luồng gửi (mọi host):", self.tf_threads, None),
              ("check", self.cb_auto_send_original),
              ("check", self.cb_store_disk)]),
            ("4.  Danh sách API từ file Excel (tùy chọn)", (219, 39, 119),
             "Nạp file .xlsx gồm các cột STT | PROTOCOL (method) | PATH | POSITION. Tham số trong path như "
             "{id}, [id], (id), <id>, :id, * được hiểu là giá trị bất kỳ. Không nạp file thì extension chạy như bình thường. "
             "Xem tiến độ ở tab 'Độ phủ Excel'.",
             [("pair", self.btn_target_load, self.lbl_target_info),
              ("check", self.cb_target_only), ("check", self.cb_target_position),
              ("check", self.cb_target_prefix),
              ("check", self.cb_target_ids),
              ("field", "Query trong file Excel:", self.cb_target_query, None)]),
            ("6.  Copy STT + Path (để dán lên server / báo cáo)", (13, 148, 136),
             "Chuột phải API / nhánh > 'Copy STT + Path', hoặc Ctrl+Shift+C. STT lấy từ file Excel (dòng khớp); "
             "không có file thì theo lựa chọn bên dưới. Mẫu dùng được: {stt} {path} {method} {endpoint} {url} {api}.",
             [("field", "Mẫu copy:", self.tf_copy_format, "mặc định: {stt}. {path}"),
              ("field", "Khi không có STT từ Excel:", self.cb_copy_fallback, self.lbl_copy_counter),
              ("pair", JButton("Đặt lại bộ đếm về 1", actionPerformed=self._on_reset_copy_counter), JLabel(" ")),
              ("check", self.cb_excel_position_copy)]),
            ("5.  Burp Repeater & tên tab", (234, 88, 12),
             "Cách đặt tên tab khi đẩy sang Burp Repeater.",
             [("check", self.cb_number), ("check", self.cb_feat_tab),
              ("field", "Độ dài tối đa của path trong tên tab:", self.tf_pathlen, None)]),
        ]
        for title, rgb, desc, rows in sections:
            content.add(self._settings_section(title, Color(rgb[0], rgb[1], rgb[2]), desc, rows))
            content.add(Box.createVerticalStrut(10))

        btns = JPanel(FlowLayout(FlowLayout.LEFT, 6, 0))
        btns.setAlignmentX(0.0)
        apply_btn = JButton("Áp dụng", actionPerformed=on_change)
        apply_btn.setFont(apply_btn.getFont().deriveFont(Font.BOLD))
        btns.add(apply_btn)
        btns.add(JButton("Khôi phục mặc định", actionPerformed=self._on_restore_defaults))
        self.lbl_settings_saved = JLabel(" ")
        btns.add(self.lbl_settings_saved)
        content.add(btns)
        self._sync_settings_fields(cfg)
        # Width-tracking holder: sections keep their natural height and the notes wrap.
        holder = _ViewportWidthPanel(BorderLayout())
        holder.add(content, BorderLayout.NORTH)
        scroll = JScrollPane(holder)
        scroll.getVerticalScrollBar().setUnitIncrement(16)
        return scroll

    def _settings_section(self, title, accent, desc, rows):
        bg, fg = _ui_colors()
        muted = _mix(fg, bg, 0.42)
        tint = _mix(bg, accent, 0.06)
        section = JPanel(BorderLayout(0, 6))
        section.setAlignmentX(0.0)
        section.setBackground(tint)
        section.setBorder(BorderFactory.createCompoundBorder(
            BorderFactory.createMatteBorder(0, 4, 0, 0, accent),
            BorderFactory.createEmptyBorder(8, 12, 10, 12)))
        head = JPanel(BorderLayout(0, 2))
        head.setOpaque(False)
        lbl = JLabel(title)
        lbl.setFont(_font_resized(lbl.getFont(), Font.BOLD, 2))
        lbl.setForeground(accent)
        head.add(lbl, BorderLayout.NORTH)
        note = JTextArea(desc)
        note.setEditable(False)
        note.setFocusable(False)
        note.setLineWrap(True)
        note.setWrapStyleWord(True)
        note.setOpaque(False)
        note.setBackground(tint)  # some look-and-feels paint text areas even when not opaque
        note.setBorder(None)
        note.setFont(_font_resized(lbl.getFont(), Font.PLAIN, -2))
        note.setForeground(muted)
        head.add(note, BorderLayout.CENTER)
        section.add(head, BorderLayout.NORTH)

        form = JPanel(GridBagLayout())
        form.setOpaque(False)
        gc = GridBagConstraints()
        gc.insets = Insets(3, 2, 3, 8)
        gc.anchor = GridBagConstraints.WEST
        for r, row in enumerate(rows):
            gc.gridy = r
            gc.gridx = 0
            gc.weightx = 0.0
            gc.fill = GridBagConstraints.NONE
            kind = row[0]
            if kind == "check":
                gc.gridwidth = 3
                form.add(row[1], gc)
                gc.gridwidth = 1
                continue
            if kind == "pair":
                if row[1] is not None:
                    form.add(row[1], gc)
                gc.gridx = 1
                gc.gridwidth = 2
                gc.weightx = 1.0
                gc.fill = GridBagConstraints.HORIZONTAL
                form.add(row[2], gc)
                gc.gridwidth = 1
                continue
            label = JLabel(row[1])
            form.add(label, gc)
            gc.gridx = 1
            form.add(row[2], gc)
            hint = row[3]
            if hint is not None:
                gc.gridx = 2
                gc.weightx = 1.0
                if not isinstance(hint, JLabel):
                    hint = JLabel(hint)
                hint.setForeground(muted)
                form.add(hint, gc)
        gc.gridy = 0
        gc.gridx = 3
        gc.weightx = 1.0
        gc.insets = Insets(0, 0, 0, 0)
        form.add(Box.createHorizontalGlue(), gc)
        section.add(form, BorderLayout.CENTER)
        return section

    def _num_field(self, value):
        field = JTextField(u_text(value), 7)
        field.setHorizontalAlignment(JTextField.RIGHT)
        field.addActionListener(_Action(self._on_settings_changed))
        field.addFocusListener(_FocusLost(lambda: self._on_settings_changed(None)))
        return field

    @staticmethod
    def _profile_index(key):
        for i, p in enumerate(SEND_PROFILES):
            if p[0] == key:
                return i
        return 0

    def _read_int(self, field, key):
        try:
            return int(u_text(field.getText()).strip())
        except (ValueError, Exception):
            return self.config.get(key, DEFAULT_CONFIG[key])

    def _sync_settings_fields(self, cfg):
        """Show the normalised config values (presets, clamping) in the form."""
        self._syncing_settings = True
        try:
            for field, key in ((self.tf_delay, "send_delay_ms"), (self.tf_jitter, "send_jitter_pct"),
                               (self.tf_conc, "host_concurrency"), (self.tf_retries, "max_retries"),
                               (self.tf_threads, "threads"), (self.tf_pathlen, "short_path_len")):
                if u_text(field.getText()).strip() != u_text(cfg[key]):
                    field.setText(u_text(cfg[key]))
            idx = self._profile_index(cfg["send_profile"])
            if self.cb_send_profile.getSelectedIndex() != idx:
                self.cb_send_profile.setSelectedIndex(idx)
            if getattr(self, "lbl_copy_counter", None) is not None:
                self.lbl_copy_counter.setText("số tiếp theo nếu đếm tăng dần: %d" % cfg.get("copy_counter", 1))
            delay = cfg["send_delay_ms"]
            if delay > 0:
                per_min = int(60000.0 / delay * cfg["host_concurrency"])
                self.lbl_pacing.setText("tối đa ~%d request / phút cho mỗi host" % per_min)
            else:
                self.lbl_pacing.setText("không giãn cách - rất dễ bị 429")
        finally:
            self._syncing_settings = False

    def _sync_settings_ui(self, cfg):
        """Show `cfg` in every settings widget (setSelected/setText fire no action events)."""
        if getattr(self, "cb_send_profile", None) is None:
            return
        self._syncing_settings = True
        try:
            for name, key in (("cb_capture", "capture_enabled"), ("cb_auto_send", "auto_send"),
                              ("cb_auto_repeater", "auto_repeater"), ("cb_scope", "in_scope_only"),
                              ("cb_top_scope", "in_scope_only"), ("cb_static", "ignore_static"),
                              ("cb_regex", "api_regex_enabled"), ("cb_top_regex", "api_regex_enabled"),
                              ("cb_options", "ignore_options_head"), ("cb_dedup", "dedup"),
                              ("cb_dedup_ids", "dedup_normalize_ids"), ("cb_dedup_feature", "dedup_per_feature"),
                              ("cb_number", "number_roles_in_tab"), ("cb_feat_tab", "include_feature_in_tab"),
                              ("cb_store_disk", "store_on_disk"), ("cb_target_only", "target_only"),
                              ("cb_auto_send_original", "auto_send_original"),
                              ("cb_target_only_mirror", "target_only"),
                              ("cb_target_position", "target_use_position"),
                              ("cb_target_prefix", "target_allow_prefix"),
                              ("cb_target_ids", "target_ids_as_params"),
                              ("cb_excel_position_copy", "excel_position_copy_format")):
                widget = getattr(self, name, None)
                if widget is not None and widget.isSelected() != bool(cfg.get(key)):
                    widget.setSelected(bool(cfg.get(key)))
            for combo, key, options in ((getattr(self, "cb_target_query", None), "target_query_mode", TARGET_QUERY_MODES),
                                        (getattr(self, "cb_copy_fallback", None), "copy_stt_fallback", COPY_STT_FALLBACKS)):
                if combo is not None:
                    idx = [k for k, _ in options].index(cfg.get(key, options[0][0]))
                    if combo.getSelectedIndex() != idx:
                        combo.setSelectedIndex(idx)
            for name, key in (("tf_static", "static_ext"), ("tf_regex", "api_regex"), ("tf_copy_format", "copy_format")):
                widget = getattr(self, name, None)
                if widget is not None and u_text(widget.getText()) != u_text(cfg.get(key)):
                    widget.setText(u_text(cfg.get(key)))
        finally:
            self._syncing_settings = False
        self._sync_settings_fields(cfg)
        self._refresh_send_controls()
        self._refresh_target_controls()

    def _on_send_profile_changed(self, event):
        if getattr(self, "_syncing_settings", False):
            return
        key = SEND_PROFILES[max(0, self.cb_send_profile.getSelectedIndex())][0]
        cfg = self.get_config()
        cfg["send_profile"] = key
        self.apply_config(cfg)
        self._sync_settings_fields(self.get_config())

    def _collect_settings(self):
        profile = SEND_PROFILES[max(0, self.cb_send_profile.getSelectedIndex())]
        delay = self._read_int(self.tf_delay, "send_delay_ms")
        jitter = self._read_int(self.tf_jitter, "send_jitter_pct")
        conc = self._read_int(self.tf_conc, "host_concurrency")
        key = profile[0]
        if key != "CUSTOM" and (delay, jitter, conc) != (profile[2], profile[3], profile[4]):
            key = "CUSTOM"  # the user typed their own numbers
        return {
            "capture_enabled": self.cb_capture.isSelected(),
            "auto_repeater": self.cb_auto_repeater.isSelected(),
            "auto_send": self.cb_auto_send.isSelected(),
            "in_scope_only": self.cb_scope.isSelected(),
            "ignore_static": self.cb_static.isSelected(),
            "static_ext": self.tf_static.getText(),
            "api_regex_enabled": self.cb_regex.isSelected(),
            "api_regex": self.tf_regex.getText(),
            "ignore_options_head": self.cb_options.isSelected(),
            "dedup": self.cb_dedup.isSelected(),
            "dedup_normalize_ids": self.cb_dedup_ids.isSelected(),
            "dedup_per_feature": self.cb_dedup_feature.isSelected(),
            "number_roles_in_tab": self.cb_number.isSelected(),
            "include_feature_in_tab": self.cb_feat_tab.isSelected(),
            "threads": self._read_int(self.tf_threads, "threads"),
            "short_path_len": self._read_int(self.tf_pathlen, "short_path_len"),
            "store_on_disk": self.cb_store_disk.isSelected(),
            "auto_send_original": self.cb_auto_send_original.isSelected(),
            "send_profile": key,
            "send_delay_ms": delay,
            "send_jitter_pct": jitter,
            "host_concurrency": conc,
            "max_retries": self._read_int(self.tf_retries, "max_retries"),
            "target_only": self.cb_target_only.isSelected(),
            "target_use_position": self.cb_target_position.isSelected(),
            "target_allow_prefix": self.cb_target_prefix.isSelected(),
            "target_ids_as_params": self.cb_target_ids.isSelected(),
            "target_query_mode": TARGET_QUERY_MODES[max(0, self.cb_target_query.getSelectedIndex())][0],
            "copy_format": u_text(self.tf_copy_format.getText()),
            "copy_stt_fallback": COPY_STT_FALLBACKS[max(0, self.cb_copy_fallback.getSelectedIndex())][0],
            "copy_counter": self.config.get("copy_counter", 1),
            "excel_position_copy_format": self.cb_excel_position_copy.isSelected(),
        }

    def _on_top_filter_toggled(self, event):
        if getattr(self, "cb_scope", None) is not None and getattr(self, "cb_top_scope", None) is not None:
            self.cb_scope.setSelected(self.cb_top_scope.isSelected())
        if getattr(self, "cb_regex", None) is not None and getattr(self, "cb_top_regex", None) is not None:
            self.cb_regex.setSelected(self.cb_top_regex.isSelected())
        self._on_settings_changed(event)

    def _on_settings_changed(self, event):
        if getattr(self, "_syncing_settings", False) or getattr(self, "cb_send_profile", None) is None:
            return
        if getattr(self, "cb_top_scope", None) is not None:
            self.cb_top_scope.setSelected(self.cb_scope.isSelected())
        if getattr(self, "cb_top_regex", None) is not None:
            self.cb_top_regex.setSelected(self.cb_regex.isSelected())
        self._collecting_settings = True
        try:
            err = self.apply_config(self._collect_settings())
        finally:
            self._collecting_settings = False
        if err and self.cb_regex.isSelected():
            self.regex_error.setText("Regex không hợp lệ - bộ lọc path đang tắt: %s" % err)
        else:
            self.regex_error.setText("")
        self._sync_settings_fields(self.get_config())
        self.lbl_settings_saved.setText("Đã lưu lúc %s" % time.strftime("%H:%M:%S"))
        self._refresh_send_controls()
        self._refresh_target_controls()

    def _on_restore_defaults(self, event):
        d = merge_config({})
        self._syncing_settings = True
        try:
            self.cb_scope.setSelected(d["in_scope_only"])
            self.cb_static.setSelected(d["ignore_static"])
            self.tf_static.setText(d["static_ext"])
            self.cb_regex.setSelected(d["api_regex_enabled"])
            self.tf_regex.setText(d["api_regex"])
            self.cb_options.setSelected(d["ignore_options_head"])
            self.cb_dedup.setSelected(d["dedup"])
            self.cb_dedup_ids.setSelected(d["dedup_normalize_ids"])
            self.cb_dedup_feature.setSelected(d["dedup_per_feature"])
            self.cb_number.setSelected(d["number_roles_in_tab"])
            self.cb_feat_tab.setSelected(d["include_feature_in_tab"])
            self.cb_auto_send.setSelected(d["auto_send"])
            self.cb_auto_repeater.setSelected(d["auto_repeater"])
            self.cb_store_disk.setSelected(d["store_on_disk"])
            self.cb_auto_send_original.setSelected(d["auto_send_original"])
            self.cb_send_profile.setSelectedIndex(self._profile_index(d["send_profile"]))
            self.cb_target_only.setSelected(d["target_only"])
            self.cb_target_position.setSelected(d["target_use_position"])
            self.cb_target_prefix.setSelected(d["target_allow_prefix"])
            self.cb_target_ids.setSelected(d["target_ids_as_params"])
            self.cb_target_query.setSelectedIndex(0)
            self.tf_copy_format.setText(d["copy_format"])
            self.cb_copy_fallback.setSelectedIndex(0)
            self.cb_excel_position_copy.setSelected(d["excel_position_copy_format"])
        finally:
            self._syncing_settings = False
        self._sync_settings_fields(d)
        self._on_settings_changed(None)

    # ---- Send mode (crawl + send  /  crawl only) and the request queue
    def _refresh_send_controls(self):
        btn = getattr(self, "btn_send_mode", None)
        if btn is None:
            return
        sending = bool(self.config.get("auto_send", False))
        queued, inflight, penalty, wait = self.dispatcher.snapshot()
        state = (sending, queued, inflight, int(penalty), int(wait + 0.99))
        if state == self._send_ui_state:
            return
        self._send_ui_state = state
        if sending:
            btn.setText("⏸  ĐANG GỬI  (bấm để dừng)")
            btn.setBackground(Color(22, 163, 74))
            btn.setToolTipText("Crawl xong gửi luôn. Bấm để chuyển sang CHỈ CRAWL: hủy mọi request đang chờ.")
        else:
            btn.setText("▶  CHỈ CRAWL  (bấm để gửi)")
            btn.setBackground(Color(100, 116, 139))
            btn.setToolTipText("API vẫn được bắt nhưng không gửi. Bấm để bật gửi: API bắt từ giờ sẽ gửi ngay.")
        btn.setForeground(Color(255, 255, 255))
        total = queued + inflight
        q = self.btn_queue
        if total:
            text = "✖ Hủy hàng đợi (%d)" % total
        else:
            text = "Hàng đợi: 0"
        if penalty > 1.0:
            text += "  ·  chậm x%d" % int(penalty)
        if wait > 0.5:
            text += "  ·  chờ %ds (429)" % int(wait + 0.99)
        q.setText(text)
        q.setEnabled(total > 0)
        q.setForeground(Color(220, 38, 38) if (penalty > 1.0 or wait > 0.5) else UIManager.getColor("Button.foreground"))

    def set_sending(self, enabled):
        cfg = self.get_config()
        cfg["auto_send"] = bool(enabled)
        if getattr(self, "cb_auto_send", None) is not None:
            self.cb_auto_send.setSelected(bool(enabled))
        self.apply_config(cfg)
        self.log("Chế độ gửi: %s" % ("ĐANG GỬI - crawl xong gửi luôn" if enabled
                                      else "CHỈ CRAWL - bắt API nhưng không gửi"))
        self._refresh_send_controls()
        self.update_status()

    def _unsent_results(self):
        out = []
        for g in self.group_model.all_groups():
            pending = [r for r in g.results if r.state == STATE_NOT_SENT]
            if pending:
                out.append((g, pending))
        return out

    def _on_toggle_send_mode(self, event):
        if self.get_config().get("auto_send", False):
            self.set_sending(False)
            return
        self.set_sending(True)
        unsent = self._unsent_results()
        if not unsent:
            return
        n_req = sum([len(p) for _, p in unsent])
        choice = JOptionPane.showConfirmDialog(
            self.main_panel,
            "Đã BẬT gửi: API bắt từ giờ sẽ được gửi ngay.\n\n"
            "Có %d API (%d request) đã crawl trong lúc dừng nhưng chưa gửi.\nGửi luôn bây giờ?" % (len(unsent), n_req),
            EXT_NAME, JOptionPane.YES_NO_OPTION)
        if choice == JOptionPane.YES_OPTION:
            for g, pending in unsent:
                self.replay(g, pending)

    def _on_send_all_unsent(self, event):
        unsent = self._unsent_results()
        for g, pending in unsent:
            self.replay(g, pending)
        self.log("Xếp hàng gửi %d API chưa gửi." % len(unsent))

    def _on_cancel_queue(self, event):
        self.cancel_pending_sends("Đã hủy hàng đợi")
        self._ui_tick(None)

    # ---- Dynamic N-Level Sub-Folder Chips & Dropdown Menus
    def _rebuild_subfolder_chips(self, path_text):
        panel = getattr(self, "subfolder_chips_panel", None)
        if panel is None:
            return
        self._chips_path = path_text
        panel.removeAll()
        parts = split_hierarchy_path(path_text)
        for idx, seg in enumerate(parts):
            if idx > 0:
                arrow = JLabel("›")
                arrow.setFont(Font("Dialog", Font.BOLD, 11))
                panel.add(arrow)
            chip_btn = JButton("[%d] %s ▾" % (idx + 1, seg))
            chip_btn.setMargin(Insets(1, 5, 1, 5))
            chip_btn.setFont(Font("Dialog", Font.BOLD if idx == len(parts) - 1 else Font.PLAIN, 11))
            chip_btn.setBackground(Color(232, 240, 254) if idx == len(parts) - 1 else Color(245, 246, 250))
            chip_btn.addActionListener(_Action(self._show_subfolder_chip_menu, chip_btn, idx))
            panel.add(chip_btn)
        add_chip = JButton("+", actionPerformed=self._on_append_subfolder)
        add_chip.setMargin(Insets(1, 5, 1, 5))
        add_chip.setFont(Font("Dialog", Font.BOLD, 11))
        add_chip.setToolTipText("Thêm nhanh 1 cấp Sub-folder con vào cuối")
        panel.add(add_chip)
        panel.revalidate()
        panel.repaint()

    def _show_capture_options_menu(self, btn):
        menu = JPopupMenu()

        def add_toggle(label, cb, is_top_filter=False):
            mark = "☑ " if cb.isSelected() else "☐ "

            def toggle(e):
                cb.setSelected(not cb.isSelected())
                if is_top_filter:
                    self._on_top_filter_toggled(e)
                else:
                    self._on_settings_changed(e)

            menu.add(JMenuItem(mark + label, actionPerformed=toggle))

        add_toggle("In-Scope Only (Chỉ bắt API trong Target Scope)", self.cb_top_scope, is_top_filter=True)
        add_toggle("API Path Regex (Chỉ bắt URL khớp Regex API)", self.cb_top_regex, is_top_filter=True)
        menu.addSeparator()
        add_toggle("Cho phép Tự động Gửi ngầm (Auto-Send 1..N Roles)", self.cb_auto_send)
        add_toggle("Tự động đẩy sang Burp Repeater khi bắt", self.cb_auto_repeater)
        menu.addSeparator()
        menu.add(JMenuItem("⚙ Mở tab Cấu hình & Bộ lọc chi tiết...",
                           actionPerformed=lambda e: self.tabs.setSelectedIndex(3)))
        menu.add(JMenuItem("♻ Reset Dedup Cache (Cho phép bắt lại API cũ)",
                           actionPerformed=self._on_reset_dedup))
        menu.show(btn, 0, btn.getHeight())

    def _show_path_actions_menu(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem("💾 Lưu đường dẫn Path đang nhập trong ô",
                           actionPerformed=self._on_apply_active_feature_name))
        menu.add(JMenuItem("➕ Thêm Sub-folder con vào cuối Path...",
                           actionPerformed=self._on_append_subfolder))
        menu.add(JMenuItem("➕ Tạo Nhánh mới cùng cấp (Action tiếp theo)...",
                           actionPerformed=self._on_next_feature))
        menu.add(JMenuItem("⬆ Lùi 1 cấp (Về thư mục cha)",
                           actionPerformed=self._on_pop_subfolder))
        menu.add(JMenuItem("⚙ Quản lý các cấp Sub-folder (Thêm / Xóa / Sửa / Đổi thứ tự)...",
                           actionPerformed=self._on_open_subfolder_manager))

        if getattr(self, "cb_existing_paths", None) is not None and self.cb_existing_paths.getItemCount() > 0:
            menu.addSeparator()
            cur_act = self.active_feature().name
            for i in range(min(self.cb_existing_paths.getItemCount(), 20)):
                p = u_text(self.cb_existing_paths.getItemAt(i))
                prefix = "🎯 [Đang bắt] " if p == cur_act else "📂 Chuyển sang: "
                item = JMenuItem(prefix + p)
                item.addActionListener(_Action(self._apply_or_switch_path, p, False))
                menu.add(item)

        menu.addSeparator()
        menu.add(JMenuItem("🗑 Xóa Nhánh hiện tại...", actionPerformed=self._on_delete_active_branch))
        menu.show(btn, 0, btn.getHeight())

    def _show_send_dropdown_menu(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem("🎯 Gửi có chọn Role (API gốc / role nào / bỏ role nào)...",
                           actionPerformed=lambda e: self._open_push_dialog("send")))
        menu.addSeparator()
        menu.add(JMenuItem("▶ Gửi API đang chọn (Tất cả Roles)", actionPerformed=self._on_replay_all))
        menu.add(JMenuItem("▶ Gửi lại Role đang chọn", actionPerformed=self._on_replay_selected))
        menu.add(JMenuItem("▶▶ Gửi toàn bộ Nhánh đang chọn (Đệ quy tất cả cấp con)",
                           actionPerformed=self._on_replay_selected_hierarchy_or_feature))
        menu.addSeparator()
        menu.add(JMenuItem("▶ Gửi tất cả request CHƯA GỬI (crawl lúc đang dừng)", actionPerformed=self._on_send_all_unsent))
        menu.add(JMenuItem("✖ Hủy hàng đợi gửi", actionPerformed=self._on_cancel_queue))
        menu.add(JMenuItem("▶▶ Gửi tất cả API đã bắt (%d API)" % len(self.group_model.all_groups()),
                           actionPerformed=lambda e: [self.replay(g, self.default_targets(g)) for g in self.group_model.all_groups()]))
        menu.show(btn, 0, btn.getHeight())

    def _show_repeater_dropdown_menu(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem("🎯 Đẩy có chọn Role (API gốc / role nào / bỏ role nào)...",
                           actionPerformed=lambda e: self._open_push_dialog("push")))
        menu.addSeparator()
        menu.add(JMenuItem("📤 Đẩy API đang chọn -> Burp Repeater", actionPerformed=self._on_send_group))
        menu.add(JMenuItem("📤 Đẩy Role đang chọn -> Burp Repeater", actionPerformed=self._on_send_role))
        menu.add(JMenuItem("📤 Đẩy cả Nhánh đang chọn -> Burp Repeater",
                           actionPerformed=self._on_send_selected_hierarchy_repeater))
        menu.addSeparator()
        cur_mode = self.cb_repeater_mode.getSelectedIndex() if getattr(self, "cb_repeater_mode", None) else 0
        modes = [
            "Kiểu 1 (Khuyên dùng): Tên gọn G01•Role + Tự copy tên Group",
            "Kiểu 2: Chỉ đẩy các Role bị Lỗi/Lệch (Vàng/Cam)",
            "Kiểu 3: Tên đầy đủ [G01:METHOD /path] Role"
        ]
        for idx, label in enumerate(modes):
            mark = "● " if idx == cur_mode else "○ "
            item = JMenuItem(mark + label)
            item.addActionListener(_Action(self.cb_repeater_mode.setSelectedIndex, idx))
            menu.add(item)
        menu.show(btn, 0, btn.getHeight())

    def _show_tools_dropdown_menu(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem("📁 Đổi Group Path cho API đang chọn...", actionPerformed=self._on_move_groups_feature))
        menu.add(JMenuItem("🔄 Rebuild Roles cho API đang chọn (Áp dụng lại cấu hình Role)",
                           actionPerformed=self._on_rebuild))
        menu.add(JMenuItem("📌 Xem Request/Response của API Gốc (Acc Crawl)", actionPerformed=self._on_show_original))
        menu.addSeparator()
        menu.add(JMenuItem("📊 Xuất Excel (.xlsx): STT / Method / Path / Vị trí...", actionPerformed=self._on_export_excel))
        menu.add(JMenuItem("💾 Export Matrix JSON...", actionPerformed=self._on_export_matrix))
        menu.add(JMenuItem("📄 Export Báo cáo Lịch sử (.txt/.md)...", actionPerformed=self._on_export_history_report))
        menu.addSeparator()
        menu.add(JMenuItem("🗑 Xóa API đang chọn", actionPerformed=self._on_delete_groups))
        menu.add(JMenuItem("♻ Reset Dedup Cache", actionPerformed=self._on_reset_dedup))
        menu.add(JMenuItem("🧹 Clear All (Xóa toàn bộ API & Nhánh)", actionPerformed=self._on_clear_groups))
        menu.show(btn, 0, btn.getHeight())

    def _show_branch_actions_menu(self, btn):
        menu = JPopupMenu()
        for label, handler in [
            ("▶ Gửi toàn bộ Nhánh đang chọn", self._on_replay_selected_hierarchy_or_feature),
            ("📤 Đẩy Nhánh đang chọn -> Burp Repeater", self._on_send_selected_hierarchy_repeater),
            ("🎯 Đẩy / Gửi Nhánh có chọn Role...", lambda e: self._open_push_dialog("push")),
            ("🎯 Đặt làm Nhánh đang bắt (Active Path)", self._on_set_selected_feature_active),
            ("➕ Thêm Sub-folder con vào Nhánh đang chọn...", self._on_add_subfolder_to_selected_tree),
            ("✏ Đổi tên Nhánh đang chọn...", self._on_rename_selected_feature),
            ("⚙ Quản lý các cấp Sub-folder...", self._on_open_subfolder_manager),
            ("🗑 Xóa Nhánh đang chọn...", self._on_delete_selected_tree_branch),
            ("👁 Xem tất cả API (Bỏ lọc Nhánh)", self._on_show_all_features),
        ]:
            menu.add(JMenuItem(label, actionPerformed=handler))
        menu.show(btn, 0, btn.getHeight())

    def _show_inline_repeater_more_menu(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem("↺ Khôi phục Request về trạng thái ban đầu",
                           actionPerformed=self._on_inline_repeater_reset_req))
        menu.add(JMenuItem("📤 Đẩy Tab Role hiện tại -> Burp Repeater", actionPerformed=self._on_send_role))
        menu.add(JMenuItem("📤 Đẩy cả API Group -> Burp Repeater", actionPerformed=self._on_send_group))
        menu.show(btn, 0, btn.getHeight())

    def _show_feature_table_popup(self, event):
        menu = JPopupMenu()
        for label, handler in [
            ("▶ Gửi toàn bộ Nhánh đang chọn", self._on_replay_selected_hierarchy_or_feature),
            ("📤 Đẩy Nhánh đang chọn -> Burp Repeater", self._on_send_selected_hierarchy_repeater),
            ("🎯 Đẩy / Gửi Nhánh có chọn Role...", lambda e: self._open_push_dialog("push")),
            ("🎯 Đặt làm Nhánh đang bắt (Active Path)", self._on_set_selected_feature_active),
            ("➕ Thêm Sub-folder con...", self._on_add_subfolder_to_selected_tree),
            ("✏ Đổi tên Nhánh...", self._on_rename_selected_feature),
            ("🗑 Xóa Nhánh...", self._on_delete_selected_tree_branch),
            ("👁 Xem tất cả API", self._on_show_all_features),
        ]:
            menu.add(JMenuItem(label, actionPerformed=handler))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def _show_group_table_popup(self, event):
        groups = self._selected_groups()
        menu = JPopupMenu()
        cnt = len(groups)
        menu.add(JMenuItem("▶ Gửi %d API đang chọn (N Roles)" % (cnt or 1), actionPerformed=self._on_replay_all))
        menu.add(JMenuItem("📤 Đẩy %d API đang chọn -> Burp Repeater" % (cnt or 1), actionPerformed=self._on_send_group))
        menu.add(JMenuItem("📋 Copy STT + Path (%d API)     Ctrl+Shift+C" % (cnt or 1),
                           actionPerformed=lambda e: (setattr(self, "_scope_source", "table"), self._on_copy_scope())))
        menu.add(JMenuItem("🎯 Đẩy / Gửi %d API có chọn Role (API gốc / role nào)..." % (cnt or 1),
                           actionPerformed=lambda e: self._open_push_dialog(
                               "push", groups or None, "%d API đang chọn" % len(groups))))
        menu.add(JMenuItem("🎛 Bật / Tắt Role cho %d API đang chọn..." % (cnt or 1),
                           actionPerformed=lambda e: self.open_role_scope_dialog(False, "api", apis=groups)))
        menu.addSeparator()
        menu.add(JMenuItem("📁 Đổi Group Path cho API đang chọn...", actionPerformed=self._on_move_groups_feature))
        menu.add(JMenuItem("🔄 Rebuild Roles cho API đang chọn", actionPerformed=self._on_rebuild))
        menu.add(JMenuItem("📌 Xem API Gốc (Acc Crawl)", actionPerformed=self._on_show_original))
        menu.addSeparator()
        menu.add(JMenuItem("🗑 Xóa API đang chọn", actionPerformed=self._on_delete_groups))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def _show_result_table_popup(self, event):
        menu = JPopupMenu()
        menu.add(JMenuItem("▶ Gửi lại Role đang chọn", actionPerformed=self._on_replay_selected))
        menu.add(JMenuItem("▶▶ Gửi toàn bộ Roles của API này", actionPerformed=self._on_replay_all))
        menu.addSeparator()
        menu.add(JMenuItem("📤 Đẩy Role đang chọn -> Burp Repeater", actionPerformed=self._on_send_role))
        menu.add(JMenuItem("📤 Đẩy cả API Group -> Burp Repeater", actionPerformed=self._on_send_group))
        menu.addSeparator()
        menu.add(JMenuItem("📌 Xem API Gốc (Acc Crawl)", actionPerformed=self._on_show_original))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def _show_history_tree_popup(self, event):
        menu = JPopupMenu()
        for label, handler in [
            ("▶ Gửi mục đang chọn", self._on_replay_tree_selection),
            ("📤 Đẩy mục đang chọn -> Burp Repeater", self._on_send_tree_repeater),
            ("🔍 Xem chi tiết trong tab API Groups", self._on_jump_to_group_from_tree),
            ("➕ Thêm Sub-folder con...", self._on_append_subfolder),
            ("✏ Đổi tên Nhánh đang chọn...", self._on_rename_tree_feature),
            ("📄 Export Báo cáo Lịch sử (.txt/.md)...", self._on_export_history_report),
        ]:
            menu.add(JMenuItem(label, actionPerformed=handler))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def _show_role_actions_menu(self, btn):
        menu = JPopupMenu()
        for label, handler in [
            ("📋 Nhân bản Role đang chọn (Duplicate)", self._on_duplicate_role),
            ("⬆ Di chuyển lên (Move Up)", lambda e: self._on_move_role(-1)),
            ("⬇ Di chuyển xuống (Move Down)", lambda e: self._on_move_role(1)),
            (None, None),
            ("✅ Bật tất cả Role (Enable All)", lambda e: self._on_enable_all(True)),
            ("⬜ Tắt tất cả Role (Disable All)", lambda e: self._on_enable_all(False)),
            ("🎛 Bật / Tắt Role theo phạm vi (nhánh / API)...", lambda e: self.open_role_scope_dialog(False)),
            (None, None),
            ("📂 Import Roles từ JSON...", self._on_import_roles),
            ("💾 Export Roles ra JSON...", self._on_export_roles),
            (None, None),
            ("⚡ Nạp mẫu 10 Roles chuẩn (Load 10-Role Template)", self._on_load_template),
        ]:
            if label is None:
                menu.addSeparator()
                continue
            menu.add(JMenuItem(label, actionPerformed=handler))
        menu.show(btn, 0, btn.getHeight())

    def _show_role_table_popup(self, event):
        menu = JPopupMenu()
        for label, handler in [
            ("✏ Sửa Role trong hộp thoại...", self._on_edit_role),
            ("📋 Nhân bản Role (Duplicate)", self._on_duplicate_role),
            ("🗑 Xóa Role đang chọn", self._on_delete_roles),
            (None, None),
            ("⬆ Di chuyển lên (Move Up)", lambda e: self._on_move_role(-1)),
            ("⬇ Di chuyển xuống (Move Down)", lambda e: self._on_move_role(1)),
            (None, None),
            ("✅ Bật tất cả Role (Enable All)", lambda e: self._on_enable_all(True)),
            ("⬜ Tắt tất cả Role (Disable All)", lambda e: self._on_enable_all(False)),
        ]:
            if label is None:
                menu.addSeparator()
                continue
            menu.add(JMenuItem(label, actionPerformed=handler))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def _show_subfolder_chip_menu(self, btn, seg_index):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        if not (0 <= seg_index < len(parts)):
            return
        seg_name = parts[seg_index]
        prefix_up_to_here = " > ".join(parts[:seg_index + 1])

        menu = JPopupMenu()
        menu.add(JMenuItem("✏ Sửa tên Cấp %d (\"%s\")..." % (seg_index + 1, seg_name),
                           actionPerformed=lambda e: self._on_chip_rename_segment(seg_index)))
        menu.add(JMenuItem("➕ Chèn Sub-folder con ngay sau Cấp %d..." % (seg_index + 1),
                           actionPerformed=lambda e: self._on_chip_insert_after(seg_index)))
        menu.add(JMenuItem("🔄 Đổi sang nhánh cùng cấp mới tại Cấp %d..." % (seg_index + 1),
                           actionPerformed=lambda e: self._on_chip_new_sibling_at(seg_index)))

        if seg_index < len(parts) - 1:
            menu.add(JMenuItem("🎯 Cắt Path chỉ giữ tới Cấp %d (\"%s\")" % (seg_index + 1, prefix_up_to_here),
                               actionPerformed=lambda e: self._apply_or_switch_path(prefix_up_to_here, rename_current=True)))

        if len(parts) > 1:
            menu.addSeparator()
            menu.add(JMenuItem("🗑 Xóa Cấp %d (\"%s\") khỏi Path" % (seg_index + 1, seg_name),
                               actionPerformed=lambda e: self._on_chip_delete_segment(seg_index)))

        menu.show(btn, 0, btn.getHeight())

    def _apply_or_switch_path(self, new_path, rename_current=True):
        clean = normalize_hierarchy_path(new_path)
        if getattr(self, "tf_feature_name", None) is not None:
            self.tf_feature_name.setText(clean)
        self._rebuild_subfolder_chips(clean)
        act = self.active_feature()
        if rename_current:
            self.rename_feature(act.fid, clean)
        else:
            feat = self.find_or_create_feature_by_path(clean, make_active=True)
            self.set_active_feature(feat.fid)

    def _on_chip_rename_segment(self, seg_index):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        if not (0 <= seg_index < len(parts)):
            return
        old_prefix = " > ".join(parts[:seg_index + 1])
        new_seg = JOptionPane.showInputDialog(
            self.main_panel,
            "Nhập tên mới cho Cấp %d (có thể nhập nhiều cấp cách nhau bởi '>'):" % (seg_index + 1),
            parts[seg_index])
        if new_seg is None or not u_text(new_seg).strip():
            return
        new_prefix = " > ".join(parts[:seg_index] + split_hierarchy_path(new_seg))
        self.rename_hierarchy_prefix(old_prefix, new_prefix)

    def _on_chip_insert_after(self, seg_index):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        new_seg = JOptionPane.showInputDialog(
            self.main_panel,
            "Nhập tên Sub-folder muốn chèn sau Cấp %d (\"%s\"):" % (seg_index + 1, parts[seg_index]),
            "Subfolder_%d" % (seg_index + 2))
        if new_seg is None or not u_text(new_seg).strip():
            return
        updated = insert_hierarchy_segment_after(act.name, seg_index, new_seg)
        self._apply_or_switch_path(updated, rename_current=True)

    def _on_chip_new_sibling_at(self, seg_index):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        if not (0 <= seg_index < len(parts)):
            return
        new_seg = JOptionPane.showInputDialog(
            self.main_panel,
            "Tạo nhánh mới cùng cấp tại Cấp %d (thay cho \"%s\"):" % (seg_index + 1, parts[seg_index]),
            "%s_2" % parts[seg_index])
        if new_seg is None or not u_text(new_seg).strip():
            return
        new_path = " > ".join(parts[:seg_index] + split_hierarchy_path(new_seg))
        self._apply_or_switch_path(new_path, rename_current=False)

    def _on_chip_delete_segment(self, seg_index):
        act = self.active_feature()
        updated = delete_hierarchy_segment_at(act.name, seg_index)
        self._apply_or_switch_path(updated, rename_current=True)

    def _on_append_subfolder(self, event):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        sub = JOptionPane.showInputDialog(
            self.main_panel,
            "Thêm Sub-folder con vào cuối đường dẫn hiện tại:\n"
            "Hiện tại (%d cấp): %s\n"
            "(Có thể nhập 1 hoặc nhiều cấp cách nhau bởi '>', ví dụ: menu_con > button_A)"
            % (len(parts), act.name),
            "Subfolder_%d" % (len(parts) + 1))
        if sub is None or not u_text(sub).strip():
            return
        new_path = append_hierarchy_segment(act.name, sub)
        all_groups = self.group_model.all_groups() if self.group_model is not None else []
        cur_has_apis = any(g.fid == act.fid for g in all_groups)
        # If current branch already captured APIs, create a child branch; otherwise update current empty branch
        self._apply_or_switch_path(new_path, rename_current=(not cur_has_apis))

    def _on_pop_subfolder(self, event):
        act = self.active_feature()
        parts = split_hierarchy_path(act.name)
        if len(parts) <= 1:
            JOptionPane.showMessageDialog(
                self.main_panel, "Đường dẫn hiện chỉ có 1 cấp gốc ('%s')." % act.name,
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        parent_path = pop_hierarchy_segment(act.name)
        all_groups = self.group_model.all_groups() if self.group_model is not None else []
        cur_has_apis = any(g.fid == act.fid for g in all_groups)
        self._apply_or_switch_path(parent_path, rename_current=(not cur_has_apis))

    def _on_open_subfolder_manager(self, event):
        act = self.active_feature()
        res = SubFolderManagerDialog(self.main_panel, act.name).show()
        if res is not None and u_text(res).strip():
            self._apply_or_switch_path(res, rename_current=True)

    def _on_existing_path_picked(self, event):
        if getattr(self, "_updating_path_combos", False) or getattr(self, "cb_existing_paths", None) is None:
            return
        sel = self.cb_existing_paths.getSelectedItem()
        if sel is not None:
            path_str = normalize_hierarchy_path(sel)
            if path_str != self.active_feature().name:
                self._apply_or_switch_path(path_str, rename_current=False)

    def _on_delete_active_branch(self, event):
        act = self.active_feature()
        self._prompt_delete_branch(act.name)

    def _on_delete_selected_tree_branch(self, event):
        prefix = self._selected_hierarchy_prefix() or self.active_feature().name
        self._prompt_delete_branch(prefix)

    def _prompt_delete_branch(self, prefix_path):
        clean = normalize_hierarchy_path(prefix_path)
        matched = self.groups_for_hierarchy_prefix(clean)
        choice = JOptionPane.showOptionDialog(
            self.main_panel,
            "Bạn muốn xóa nhánh Sub-folder '%s' (%d API bên trong) như thế nào?" % (clean, len(matched)),
            EXT_NAME, JOptionPane.DEFAULT_OPTION, JOptionPane.QUESTION_MESSAGE, None,
            ["Chỉ xóa Nhánh (Chuyển API lên cấp cha)", "Xóa cả Nhánh lẫn %d API" % len(matched), "Hủy"],
            "Chỉ xóa Nhánh (Chuyển API lên cấp cha)")
        if choice == 0:
            self.delete_hierarchy_prefix(clean, delete_apis=False)
        elif choice == 1:
            self.delete_hierarchy_prefix(clean, delete_apis=True)

    def _on_add_subfolder_to_selected_tree(self, event):
        base_prefix = self._selected_hierarchy_prefix() or self.active_feature().name
        sub = JOptionPane.showInputDialog(
            self.main_panel,
            "Thêm Sub-folder con bên dưới nhánh '%s':\n(Có thể nhập nhiều cấp cách nhau bởi '>')" % base_prefix,
            "Subfolder_mới")
        if sub is None or not u_text(sub).strip():
            return
        new_path = append_hierarchy_segment(base_prefix, sub)
        self._apply_or_switch_path(new_path, rename_current=False)

    def _show_left_tree_popup(self, event):
        kind, payload = self._selected_left_tree_payload()
        menu = JPopupMenu()
        if kind in ("FOLDER", "ROOT"):
            prefix = payload if kind == "FOLDER" else ""
            title = prefix or "Tất cả"
            menu.add(JMenuItem("▶ Gửi (Replay) toàn bộ Nhánh \"%s\"" % title,
                               actionPerformed=self._on_replay_selected_hierarchy_or_feature))
            menu.add(JMenuItem("➕ Thêm Sub-folder con vào \"%s\"..." % title,
                               actionPerformed=self._on_add_subfolder_to_selected_tree))

            if kind == "FOLDER":
                menu.add(JMenuItem("🎯 Đặt \"%s\" làm Nhánh đang bắt (Active Path)" % title,
                                   actionPerformed=self._on_set_selected_feature_active))
                menu.add(JMenuItem("✏ Đổi tên Nhánh \"%s\" (Cập nhật cả cấp con)..." % title,
                                   actionPerformed=self._on_rename_selected_feature))
                menu.add(JMenuItem("📤 Đẩy Nhánh \"%s\" sang Burp Repeater" % title,
                                   actionPerformed=self._on_send_selected_hierarchy_repeater))
                menu.add(JMenuItem("🎯 Đẩy / Gửi Nhánh \"%s\" có chọn Role..." % title,
                                   actionPerformed=lambda e: self._open_push_dialog("push")))
                menu.add(JMenuItem("📋 Copy path nhánh \"%s\"" % title, actionPerformed=self._on_copy_branch_path))
                menu.add(JMenuItem("📋 Copy STT + Path của các API trong nhánh", actionPerformed=self._on_copy_scope))
                menu.add(JMenuItem("🎛 Bật / Tắt Role cho nhánh \"%s\"..." % title,
                                   actionPerformed=lambda e, p=prefix: self.open_role_scope_dialog(
                                       False, "branch", branches=[p])))
                menu.addSeparator()
                menu.add(JMenuItem("🗑 Xóa Nhánh \"%s\"..." % title,
                                   actionPerformed=self._on_delete_selected_tree_branch))
        elif kind in ("GROUP", "ORIG", "ROLE"):
            g = payload if kind == "GROUP" else payload[0]
            menu.add(JMenuItem(("▶ Gửi API #%d (%d Roles)" % (g.gid, len(g.results))) if g.results
                               else ("▶ Gửi API #%d (API gốc - 0 role)" % g.gid),
                               actionPerformed=lambda e: self.replay(g, self.default_targets(g))))
            menu.add(JMenuItem("📤 Đẩy API #%d sang Burp Repeater (Gọn)" % g.gid,
                               actionPerformed=lambda e: self._dispatch_group_with_selected_mode(g)))
            menu.add(JMenuItem("📋 Copy STT + Path   (%s)" % self.copy_label_for(g, assign=False)[:60],
                               actionPerformed=lambda e: self.copy_groups([g])))
            menu.add(JMenuItem("🎯 Đẩy / Gửi API #%d có chọn Role..." % g.gid,
                               actionPerformed=lambda e: self._open_push_dialog("push", [g], format_api_label(g.gid))))
            menu.add(JMenuItem("🎛 Bật / Tắt Role cho API #%d..." % g.gid,
                               actionPerformed=lambda e: self.open_role_scope_dialog(False, "api", apis=[g])))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def update_status(self):
        """Refresh the header bar: immediately on the EDT, otherwise at the next UI tick."""
        if SwingUtilities.isEventDispatchThread():
            self._do_update_status()
        else:
            self._mark(status=True)

    def _do_update_status(self):
        if self.status_label is None or getattr(self, "btn_replay_all", None) is None:
            return
        cfg = self.get_config()
        stats = self._stats
        if stats is None:
            stats = HierarchyStats(self.features_list(), [])
        act = self.active_feature()
        mode_str = "Gửi: BẬT" if cfg.get("auto_send") else "Chỉ crawl"
        excel = ""
        if self.targets:
            excel = " | Excel: %d/%d" % (len([e for e in self.targets.entries if id(e) in stats.target_hits]),
                                         len(self.targets))
        self.status_label.setText(
            "%s | Roles: %d/%d | Nhánh: %d | API: %d (Vàng: %d)%s"
            % (mode_str, self.roles.enabled_count(), self.roles.count(),
               len(self.features_list()), stats.total, stats.info_exact, excel))
        if getattr(self, "lbl_active_feature", None) is not None:
            parts = split_hierarchy_path(act.name)
            self.lbl_active_feature.setText("Path [#%d | %d cấp]:" % (act.fid, len(parts)))
            if not self.tf_feature_name.hasFocus():
                self.tf_feature_name.setText(act.name)
            if act.name != self._chips_path:
                self._rebuild_subfolder_chips(act.name)
            self.lbl_feature_counter.setText("(%d API)" % len(stats.groups_of(act.fid)))
        g, _ = self.current_selection()
        count = len(g.results) if g is not None else self.roles.enabled_count()
        self.btn_replay_all.setText(("▶ Gửi API (%d Roles)" % count) if count else "▶ Gửi API gốc (0 role)")

    # ---------------------------------------- feature & history view helpers
    def _refresh_history_summary_only(self):
        if self.history_summary_area is None or self.group_model is None:
            return
        text = build_history_summary_text(self.features_list(), self.group_model.all_groups())
        self.history_summary_area.setText(text)
        self.history_summary_area.setCaretPosition(0)

    def _build_hierarchy_nodes(self, stats, root_label, state):
        """
        Build the nested tree:
          [Cấp 1] Toppage (11 API | ...)
            └── [Cấp 2] menu (11 API | ...)
                  └── API 1 [G01]: GET /path (1 Gốc + 10 Roles)
                        ├── [API GỐC] 00_Original      <- created only when the API node is
                        └── 01_Admin .. 10_Guest          expanded (see _load_group_children)
        Folder counters come from HierarchyStats (one pass), and an API costs 2 nodes
        instead of 2 + roles. Returns (root, nodes_by_key, nodes_to_expand).
        """
        root = HierarchyTreeNode("ROOT", "", root_label, audit_level=AUDIT_NONE, key=("ROOT",))
        nodes = {root.key: root}
        expand = []
        open_ids = set([id(root)])
        collapsed = state["collapsed"]
        expanded = state["expanded"]

        def ensure_folder_chain(parts):
            parent = root
            lowered = [p.lower() for p in parts]
            for idx in range(len(parts)):
                key = ("F", " > ".join(lowered[:idx + 1]))
                node = nodes.get(key)
                if node is None:
                    total, flagged, ok = stats.prefix.get(key[1], (0, 0, 0))
                    lvl, summary = audit_from_counts(total, flagged, ok)
                    node = HierarchyTreeNode(
                        "FOLDER", " > ".join(parts[:idx + 1]),
                        "%s   ·   %d API   ·   %s" % (parts[idx], total, summary),
                        audit_level=lvl, key=key, depth=idx + 1)
                    nodes[key] = node
                    parent.add(node)
                    if id(parent) in open_ids and key not in collapsed:
                        open_ids.add(id(node))
                        expand.append(node)
                parent = node
            return parent

        for path_str in stats.paths:
            ensure_folder_chain(split_hierarchy_path(path_str))

        for g in stats.groups:
            leaf = ensure_folder_chain(
                split_hierarchy_path(getattr(g, "feature_name", "") or DEFAULT_HIERARCHY_PATH))
            key = ("G", g.gid)
            g_audit = getattr(g, "_audit_summary", None) or evaluate_group_audit(g)[1]
            node = HierarchyTreeNode(
                "GROUP", g, group_tree_label(g, g_audit), audit_level=_group_level(g), key=key)
            nodes[key] = node
            if id(leaf) in open_ids and key in expanded:
                self._load_group_children(node, nodes)
                expand.append(node)
            else:
                node.loaded = False
                node.add(HierarchyTreeNode("LOADING", None, "..."))
            leaf.add(node)
        return root, nodes, expand

    @staticmethod
    def _load_group_children(g_node, nodes=None):
        """Replace an API node's placeholder with its real rows: 1 original + N roles."""
        g = g_node.payload
        g_node.removeAllChildren()
        entries = []
        if getattr(g, "orig_result", None) is not None:
            entries.append(("ORIG", ("O", g.gid), g.orig_result))
        for r in g.results:
            entries.append(("ROLE", ("R", g.gid, r.role_index), r))
        for kind, key, r in entries:
            lvl = getattr(r, "_audit_level", None) or evaluate_role_result(g, r)[0]
            badge = getattr(r, "_audit_badge", None) or evaluate_role_result(g, r)[1]
            child = HierarchyTreeNode(kind, (g, r), result_tree_label(r, badge),
                                      audit_level=lvl, key=key)
            g_node.add(child)
            if nodes is not None:
                nodes[key] = child
        g_node.loaded = True

    def _lazy_load_tree_node(self, name, model, node):
        if getattr(node, "loaded", True):
            return
        loader = {
            "GROUP": self._load_group_children,
            "LOGBRANCH": self._load_log_branch,
            "LOGAPI": self._load_log_api,
            "LOGSYS": self._load_log_system,
        }.get(getattr(node, "kind", None))
        if loader is not None:
            loader(node, self._tree_states[name]["nodes"])
            model.nodeStructureChanged(node)

    @staticmethod
    def _remember_tree_state(tree, state):
        """Folders are open unless the user collapsed them; every other node is closed unless opened."""
        collapsed = state["collapsed"]
        expanded = state["expanded"]
        for i in range(tree.getRowCount()):
            path = tree.getPathForRow(i)
            if path is None:
                continue
            node = path.getLastPathComponent()
            key = getattr(node, "key", None)
            if key is None or node.getChildCount() == 0:
                continue
            if getattr(node, "kind", None) == "FOLDER":
                if tree.isExpanded(i):
                    collapsed.discard(key)
                else:
                    collapsed.add(key)
            elif tree.isExpanded(i):
                expanded.add(key)
            else:
                expanded.discard(key)

    # ---- Log tree: branch > API > (log lines + role results), every level loaded on expand
    @staticmethod
    def _placeholder(node):
        node.loaded = False
        node.add(HierarchyTreeNode("LOADING", None, "..."))

    def _build_log_nodes(self, stats, root_label, state):
        root = HierarchyTreeNode("ROOT", "", root_label, key=("ROOT",))
        nodes = {root.key: root}
        expand = [root]
        expanded = state["expanded"]
        by_path = {}
        for g in stats.groups:
            by_path.setdefault(normalize_hierarchy_path(getattr(g, "feature_name", "") or DEFAULT_HIERARCHY_PATH),
                               []).append(g)
        for path in stats.paths:
            groups = by_path.get(path)
            if not groups:
                continue
            lvl, summary = evaluate_feature_audit(groups)
            node = HierarchyTreeNode(
                "LOGBRANCH", groups, "%s   ·   %d API   ·   %s" % (path, len(groups), summary),
                audit_level=lvl, key=("LB", path.lower()), depth=len(split_hierarchy_path(path)))
            self._placeholder(node)
            nodes[node.key] = node
            root.add(node)
        with self._log_lock:
            n_sys = len(self._log_system)
        sys_node = HierarchyTreeNode("LOGSYS", None, "Hệ thống & thao tác   ·   %d dòng" % n_sys, key=("LS",))
        self._placeholder(sys_node)
        nodes[sys_node.key] = sys_node
        root.add(sys_node)
        # Re-open what the user had open (loading those levels now, parents first).
        for i in range(root.getChildCount()):
            branch = root.getChildAt(i)
            if branch.key not in expanded:
                continue
            self._lazy_load_any(branch, nodes)
            expand.append(branch)
            for j in range(branch.getChildCount()):
                api = branch.getChildAt(j)
                if getattr(api, "key", None) in expanded:
                    self._lazy_load_any(api, nodes)
                    expand.append(api)
        return root, nodes, expand

    def _lazy_load_any(self, node, nodes):
        kind = node.kind
        if kind == "LOGBRANCH":
            self._load_log_branch(node, nodes)
        elif kind == "LOGAPI":
            self._load_log_api(node, nodes)
        elif kind == "LOGSYS":
            self._load_log_system(node, nodes)

    def _load_log_branch(self, node, nodes=None):
        node.removeAllChildren()
        for g in node.payload:
            g_audit = getattr(g, "_audit_summary", None) or evaluate_group_audit(g)[1]
            child = HierarchyTreeNode(
                "LOGAPI", g, "%s   ·   %s   ·   %s   ·   %s" % (
                    format_api_label(g.gid), "%s %s" % (g.method, short_path(g.path, 60)),
                    g.created, g_audit),
                audit_level=_group_level(g), key=("LA", g.gid))
            self._placeholder(child)
            node.add(child)
            if nodes is not None:
                nodes[child.key] = child
        node.loaded = True

    def _load_log_api(self, node, nodes=None):
        g = node.payload
        node.removeAllChildren()
        with self._log_lock:
            lines = list(self._log_by_gid.get(g.gid, ()))
        for idx, (ts, text) in enumerate(lines):
            node.add(HierarchyTreeNode("LOGLINE", None, "%s   %s" % (ts, text), key=("LL", g.gid, idx)))
        for r in g.all_entries():
            lvl, badge = evaluate_role_result(g, r)
            child = HierarchyTreeNode("LOGRES", (g, r), result_tree_label(r, badge), audit_level=lvl,
                                      key=("LR", g.gid, r.role_index))
            node.add(child)
            if nodes is not None:
                nodes[child.key] = child
        node.loaded = True

    def _load_log_system(self, node, nodes=None):
        node.removeAllChildren()
        with self._log_lock:
            lines = list(self._log_system)
        for idx, (ts, text) in enumerate(lines):
            node.add(HierarchyTreeNode("LOGLINE", None, "%s   %s" % (ts, text), key=("LSL", idx)))
        node.loaded = True

    def _rebuild_tree(self, name, tree, model, root_label, stats, force, builder=None):
        """
        Rebuild one tree, keeping the user's selection and expand/collapse choices.
        Unless forced by a user action, rebuilds are spaced out in proportion to their
        own cost, so a huge tree can never monopolise the EDT. Returns False if skipped.
        """
        state = self._tree_states[name]
        started = time.time()
        if not force and started < state["next_ok"]:
            return False
        self._remember_tree_state(tree, state)
        sel_path = tree.getSelectionPath()
        sel_key = getattr(sel_path.getLastPathComponent(), "key", None) if sel_path is not None else None
        root, nodes, expand = (builder or self._build_hierarchy_nodes)(stats, root_label, state)
        state["nodes"] = nodes
        state["collapsed"] = set([k for k in state["collapsed"] if k in nodes])
        state["expanded"] = set([k for k in state["expanded"] if k in nodes])
        self._restoring_tree = True
        try:
            model.setRoot(root)
            for node in expand:
                tree.expandPath(TreePath(node.getPath()))
            target = nodes.get(sel_key) if sel_key is not None else None
            if target is not None:
                tree.setSelectionPath(TreePath(target.getPath()))
        finally:
            self._restoring_tree = False
        state["next_ok"] = time.time() + min(5.0, (time.time() - started) * 8)
        return True

    def _refresh_feature_views(self):
        """
        Ask for the branch table, trees and report to be brought up to date.
        On the EDT (a user action) this happens now; from worker threads it is merged
        into the next UI tick.
        """
        self._mark(structure=True)
        if SwingUtilities.isEventDispatchThread():
            self._ui_tick(None)

    def _on_apply_3_boxes_hierarchy(self, event):
        self._on_apply_active_feature_name(event)

    def _on_apply_active_feature_name(self, event):
        act = self.active_feature()
        new_name = normalize_hierarchy_path(self.tf_feature_name.getText())
        if new_name:
            self.rename_feature(act.fid, new_name)

    def _on_next_feature(self, event):
        cur = self.active_feature()
        typed = u_text(self.tf_feature_name.getText()).strip() if getattr(self, "tf_feature_name", None) else ""
        if typed and normalize_hierarchy_path(typed) != cur.name:
            self.rename_feature(cur.fid, normalize_hierarchy_path(typed))
        parts = split_hierarchy_path(self.active_feature().name)
        next_num = len(self.features_list()) + 1
        if len(parts) > 1:
            default_next = " > ".join(parts[:-1] + ["action_%d" % next_num])
        else:
            default_next = "%s > action_%d" % (parts[0], next_num)
        name = JOptionPane.showInputDialog(
            self.main_panel,
            "Nhập đường dẫn phân cấp Group cho nhánh mới (tự do bao nhiêu cấp tùy ý, ngăn cách bởi '>'):\n"
            "Ví dụ: Toppage > menu > submenu > button \"Search\"",
            default_next)
        if name is None:
            return
        self.start_new_feature(normalize_hierarchy_path(name))

    def _on_group_mode_changed(self, event):
        if self.group_model is None or getattr(self, "cb_group_mode", None) is None:
            return
        idx = self.cb_group_mode.getSelectedIndex()
        if idx == 0:
            self.group_model.set_feature_filter(None)
            self.group_model.set_hierarchy_filter(None)
        else:
            prefix = self._selected_hierarchy_prefix()
            self.group_model.set_hierarchy_filter(prefix)

    def _on_audit_filter_changed(self, event):
        if self.group_model is None or getattr(self, "cb_audit_filter", None) is None:
            return
        idx = self.cb_audit_filter.getSelectedIndex()
        level = AUDIT_FILTER_OPTIONS[idx][1] if 0 <= idx < len(AUDIT_FILTER_OPTIONS) else AUDIT_FILTER_ALL
        self.group_model.set_audit_filter(level)
        if self.group_model.getRowCount() > 0:
            self.group_table.setRowSelectionInterval(0, 0)
        else:
            self.result_model.set_group(None)
            self._refresh_grouped_repeater_bar()
            self._show_result(None)

    def _on_show_all_features(self, event):
        if getattr(self, "cb_group_mode", None) is not None:
            self.cb_group_mode.setSelectedIndex(0)
        if self.feature_table is not None and self.feature_model.getRowCount() > 0:
            self.feature_table.setRowSelectionInterval(0, 0)
        if getattr(self, "cb_audit_filter", None) is not None:
            self.cb_audit_filter.setSelectedIndex(0)
        if self.group_model is not None:
            self.group_model.set_feature_filter(None)
            self.group_model.set_hierarchy_filter(None)
            self.group_model.set_audit_filter(AUDIT_FILTER_ALL)
        if getattr(self, "btn_replay_branch", None) is not None:
            self.btn_replay_branch.setText("▶▶ Gửi Nhánh")
            self.btn_replay_branch.setToolTipText("Gửi toàn bộ API trong Nhánh đang chọn")

    @staticmethod
    def _extract_node_kind_payload(node):
        if node is None:
            return None, None
        kind = getattr(node, "kind", None)
        if kind is not None:
            return kind, getattr(node, "payload", None)
        if isinstance(node, DefaultMutableTreeNode):
            obj = node.getUserObject()
            if hasattr(obj, "kind"):
                return obj.kind, obj.payload
        return None, None

    def _selected_left_tree_payload(self):
        """Selection of the tree the user last used: the small one in 'API Groups' or the full-tab one."""
        tree = getattr(self, "_menu_tree", None) or getattr(self, "left_hierarchy_tree", None)
        if tree is None:
            return None, None
        path = tree.getSelectionPath()
        if path is None:
            return None, None
        return self._extract_node_kind_payload(path.getLastPathComponent())

    def _selected_hierarchy_prefix(self):
        kind, payload = self._selected_left_tree_payload()
        if kind == "FOLDER":
            return payload
        if kind == "GROUP" and payload is not None:
            return getattr(payload, "feature_name", None)
        if kind in ("ROLE", "ORIG") and payload is not None:
            return getattr(payload[0], "feature_name", None)
        feat = self._selected_feature_from_table()
        return feat.name if feat is not None else None

    def _on_tree_used(self, tree):
        if self._restoring_tree:
            return
        self._menu_tree = tree
        self._on_left_hierarchy_tree_selected()
        # set after: selecting the matching table row above fires the table listener too
        self._scope_source = "tree"

    def _tree_popup_from(self, tree, event):
        self._menu_tree = tree
        self._scope_source = "tree"
        self._show_left_tree_popup(event)

    def _on_left_hierarchy_tree_selected(self):
        if self._restoring_tree:
            return
        kind, payload = self._selected_left_tree_payload()
        if kind == "ROOT":
            if getattr(self, "btn_replay_branch", None) is not None:
                self.btn_replay_branch.setText("▶▶ Gửi Tất cả (%d API)" % len(self.group_model.all_groups()))
                self.btn_replay_branch.setToolTipText("Gửi toàn bộ %d API đã bắt" % len(self.group_model.all_groups()))
            if getattr(self, "cb_group_mode", None) is not None and self.cb_group_mode.getSelectedIndex() == 1:
                self.group_model.set_hierarchy_filter(None)
            return
        if kind == "FOLDER":
            prefix = payload
            cnt = len(self.groups_for_hierarchy_prefix(prefix))
            leaf_name = split_hierarchy_path(prefix)[-1]
            if getattr(self, "btn_replay_branch", None) is not None:
                self.btn_replay_branch.setText("▶▶ Gửi \"%s\" (%d API)" % (leaf_name[:18], cnt))
                self.btn_replay_branch.setToolTipText("Gửi đệ quy toàn bộ nhánh: %s (%d API)" % (prefix, cnt))
            if getattr(self, "cb_group_mode", None) is not None and self.cb_group_mode.getSelectedIndex() == 1:
                self.group_model.set_hierarchy_filter(prefix)
            return
        if kind == "GROUP" and payload is not None:
            if getattr(self, "btn_replay_branch", None) is not None:
                self.btn_replay_branch.setText("▶▶ Gửi API #%d" % payload.gid)
            self._select_group_in_table(payload)
            return
        if kind in ("ROLE", "ORIG") and payload is not None:
            g, r = payload
            self._select_group_in_table(g, target_result=r)

    def _select_group_in_table(self, target_group, target_result=None):
        if target_group is None or self.group_model is None:
            return
        mr = self.group_model.row_of(target_group)
        if mr >= 0:
            vr = self.group_table.convertRowIndexToView(mr)
            if vr >= 0:
                self.group_table.setRowSelectionInterval(vr, vr)
                self.group_table.scrollRectToVisible(self.group_table.getCellRect(vr, 0, True))
        if target_result is not None and self.result_model is not None:
            for rmr in range(self.result_model.getRowCount()):
                if self.result_model.result_at(rmr) is target_result:
                    rvr = self.result_table.convertRowIndexToView(rmr)
                    if rvr >= 0:
                        self.result_table.setRowSelectionInterval(rvr, rvr)
                    break

    def _on_replay_selected_hierarchy_or_feature(self, event):
        kind, payload = self._selected_left_tree_payload()
        if kind == "ROOT":
            all_g = self.group_model.all_groups()
            for g in all_g:
                self.replay(g, self.default_targets(g))
            return
        if kind == "FOLDER" and payload:
            sent = self.replay_hierarchy_prefix(payload)
            if not sent:
                JOptionPane.showMessageDialog(
                    self.main_panel, "Nhánh '%s' chưa có API nào để gửi." % payload,
                    EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        if kind == "GROUP" and payload is not None:
            self.replay(payload, self.default_targets(payload))
            return
        if kind == "ROLE" and payload is not None:
            g, r = payload
            self.replay(g, [r])
            return
        feat = self._selected_feature_from_table()
        if feat is not None:
            sent = self.replay_hierarchy_prefix(feat.name)
            if not sent:
                JOptionPane.showMessageDialog(
                    self.main_panel, "Nhánh '%s' chưa có API nào để gửi." % feat.name,
                    EXT_NAME, JOptionPane.INFORMATION_MESSAGE)

    # ---- 'Copy STT + Path'
    def copy_label_for(self, group, assign=True):
        """
        'STT. path' line of an API: STT from its Excel row, else the chosen fallback (counter assigned
        on the first copy and kept, or the API number); path = its branch, e.g. / > contact > button.
        """
        cfg = self.config
        stt = group.target.stt if getattr(group, "target", None) is not None else None
        if stt is None or u_text(stt).strip() == "":
            mode = cfg.get("copy_stt_fallback", "none")
            if mode == "api":
                stt = group.gid
            elif mode == "counter":
                if group.copy_stt is None and assign:
                    with self._cfg_lock:
                        group.copy_stt = self.config.get("copy_counter", 1)
                        self.config["copy_counter"] = group.copy_stt + 1
                        snapshot = dict(self.config)
                    self.callbacks.saveExtensionSetting(SETTINGS_KEY_CONFIG, json.dumps(snapshot))
                stt = group.copy_stt
        return format_copy_line(cfg.get("copy_format"), stt, group.feature_name, group.method, group.url,
                                format_api_label(group.gid), "%s %s" % (group.method, strip_query(group.path)))

    def copy_groups(self, groups):
        """Copy one line per API to the clipboard and mark the APIs as copied (for counting later)."""
        lines = []
        for g in sorted(groups, key=lambda x: x.gid):
            label = self.copy_label_for(g)
            g.copied_label = label
            lines.append(label)
            self._notify_results(g, None)
        if not lines:
            return ""
        text = "\n".join(lines)
        self._copy_to_clipboard(text)
        for g, line in zip(sorted(groups, key=lambda x: x.gid), lines):
            self.log("Đã copy: %s" % line, gid=g.gid)
        self._mark(structure=True, status=True)
        if getattr(self, "lbl_copy_counter", None) is not None:
            ui_call(lambda: self._sync_settings_fields(self.get_config()))
        return text

    def _on_copy_scope(self, event=None):
        groups, label = self._groups_in_scope()
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chọn API (bảng) hoặc nhánh / API (cây) trước.",
                                          EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        text = self.copy_groups(groups)
        self._flash_status("📋 Đã copy %d dòng: %s" % (len(groups), text.split("\n")[0][:80]))

    def _on_copy_branch_path(self, event=None):
        prefix = self._selected_hierarchy_prefix()
        if prefix:
            self._copy_to_clipboard(prefix)
            self._flash_status("📋 Đã copy path nhánh: %s" % prefix)

    def _flash_status(self, text):
        label = getattr(self, "status_label", None)
        if label is not None:
            label.setText(text)

    def _on_reset_copy_counter(self, event):
        if JOptionPane.showConfirmDialog(
                self.main_panel, "Đặt lại bộ đếm STT tăng dần về 1?\nCác API đã được đánh số sẽ được đánh số lại "
                                 "ở lần copy tiếp theo.", EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        for g in self.group_model.all_groups():
            g.copy_stt = None
        cfg = self.get_config()
        cfg["copy_counter"] = 1
        self.apply_config(cfg)
        self._sync_settings_fields(self.get_config())

    def _install_copy_shortcut(self, component):
        component.getInputMap(JComponent.WHEN_FOCUSED).put(KeyStroke.getKeyStroke("ctrl shift C"), "tmoc-copy")
        component.getActionMap().put("tmoc-copy", _KeyAction(lambda: self._on_copy_from(component)))

    def _on_copy_from(self, component):
        if component is self.group_table:
            self._scope_source = "table"
        else:
            self._menu_tree = component
            self._scope_source = "tree"
        self._on_copy_scope()

    # ---- 'Đẩy / Gửi có chọn Role'
    def _groups_in_scope(self):
        """(groups, label): selected rows of the API table, else the selected tree node / branch."""
        groups = self._selected_groups() if self.group_table is not None else []
        if groups and getattr(self, "_scope_source", "table") == "table":
            return groups, ("%d API đang chọn" % len(groups)) if len(groups) > 1 else format_api_label(groups[0].gid)
        kind, payload = self._selected_left_tree_payload()
        if kind == "ROOT":
            return self.group_model.all_groups(), "Tất cả API"
        if kind == "FOLDER" and payload:
            return self.groups_for_hierarchy_prefix(payload), "Nhánh \"%s\"" % payload
        if kind == "GROUP" and payload is not None:
            return [payload], format_api_label(payload.gid)
        if kind in ("ROLE", "ORIG") and payload is not None:
            return [payload[0]], format_api_label(payload[0].gid)
        if groups:
            return groups, "%d API đang chọn" % len(groups)
        feat = self._selected_feature_from_table()
        if feat is not None:
            return self.groups_for_hierarchy_prefix(feat.name), "Nhánh \"%s\"" % feat.name
        return [], ""

    def _open_push_dialog(self, action="push", groups=None, label=None):
        if groups is None:
            groups, label = self._groups_in_scope()
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chọn API (bảng) hoặc nhánh / API (cây) trước.",
                                          EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        memory = getattr(self, "_push_memory", None) or {"orig": False, "unchecked": [], "compact": True}
        choice = PushTargetsDialog(self.main_panel, groups, label, memory, action).show()
        if choice is None:
            return
        self._push_memory = choice
        self.run_push_choice(groups, choice, label)

    def run_push_choice(self, groups, choice, label=""):
        total = 0
        apis = 0
        for g in groups:
            targets = select_push_targets(g, choice["orig"], choice["roles"], choice["only_flagged"])
            if not targets:
                continue
            apis += 1
            total += len(targets)
            if choice["action"] == "send":
                self.replay(g, targets)
            else:
                self.send_to_repeater(g, targets, compact=choice["compact"],
                                      copy_group_name=choice["compact"] and len(groups) == 1)
        what = "gửi %d request" % total if choice["action"] == "send" else "đẩy %d tab sang Repeater" % total
        parts = (["API gốc"] if choice["orig"] else []) + sorted(choice["roles"])
        self.log("%s: %s cho %d API (%s%s)." % (label or "Chọn Role", what, apis, ", ".join(parts) or "-",
                                                 ", chỉ role lỗi/lệch" if choice["only_flagged"] else ""))
        return total

    def _dispatch_group_with_selected_mode(self, group):
        if group is None:
            return
        mode_idx = self.cb_repeater_mode.getSelectedIndex() if getattr(self, "cb_repeater_mode", None) else 0
        if mode_idx == 1:
            # Only roles with INFO (error/diff) or WARN (bypass)
            interesting = [
                r for r in group.results
                if (getattr(r, "_audit_level", None) or evaluate_role_result(group, r)[0])
                in (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR)
            ]
            targets = interesting if interesting else self.default_targets(group)
            self.send_to_repeater(group, targets, compact=True, copy_group_name=True)
        elif mode_idx == 0:
            # Compact tab names (G01•01_Admin) + copy group title to clipboard
            self.send_to_repeater(group, self.default_targets(group), compact=True, copy_group_name=True)
        else:
            # Classic full tab names
            self.send_to_repeater(group, self.default_targets(group), compact=False, copy_group_name=False)

    def _on_send_selected_hierarchy_repeater(self, event):
        kind, payload = self._selected_left_tree_payload()
        if kind == "FOLDER" and payload:
            matched = self.groups_for_hierarchy_prefix(payload)
            if not matched:
                JOptionPane.showMessageDialog(
                    self.main_panel, "Nhánh '%s' chưa có API nào." % payload,
                    EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
                return
            for g in matched:
                self._dispatch_group_with_selected_mode(g)
            self._copy_to_clipboard(payload)
            return
        if kind == "GROUP" and payload is not None:
            self._dispatch_group_with_selected_mode(payload)
            return
        if kind in ("ROLE", "ORIG") and payload is not None:
            g, r = payload
            self.send_to_repeater(g, [r], compact=True, copy_group_name=True)
            return
        feat = self._selected_feature_from_table()
        if feat is not None:
            for g in self.groups_for_hierarchy_prefix(feat.name):
                self._dispatch_group_with_selected_mode(g)

    def _on_feature_filter_selected(self):
        if self.feature_table is None or self.group_model is None or self._restoring_feature_sel:
            return
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            self.group_model.set_feature_filter(None)
        else:
            feat = self.feature_model.feature_at_row(r)
            if feat is not None:
                if getattr(self, "btn_replay_branch", None) is not None:
                    leaf_name = split_hierarchy_path(feat.name)[-1]
                    self.btn_replay_branch.setText("▶▶ Gửi \"%s\"" % leaf_name[:18])
                    self.btn_replay_branch.setToolTipText("Gửi nhánh: %s" % feat.name)
                if getattr(self, "cb_group_mode", None) is not None and self.cb_group_mode.getSelectedIndex() == 1:
                    self.group_model.set_feature_filter(feat.fid)
                else:
                    self.group_model.set_feature_filter(None)
        if self.group_model.getRowCount() > 0 and self.group_table.getSelectedRow() < 0:
            self.group_table.setRowSelectionInterval(0, 0)

    def _selected_feature_from_table(self):
        if getattr(self, "feature_table", None) is None:
            return self.active_feature()
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            return self.active_feature()
        return self.feature_model.feature_at_row(r) or self.active_feature()

    def _on_set_selected_feature_active(self, event):
        kind, payload = self._selected_left_tree_payload()
        if kind == "FOLDER" and payload:
            feat = self.find_or_create_feature_by_path(payload, make_active=True)
            self.set_active_feature(feat.fid)
            self.log("Đặt nhánh '%s' làm nhánh đang bắt API hiện tại." % feat.name)
            return
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            JOptionPane.showMessageDialog(
                self.main_panel, "Chọn một nhánh trong Cây Sub-folder hoặc trong Bảng Nhánh bên trái.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        feat = self.feature_model.feature_at_row(r)
        if feat is not None:
            self.set_active_feature(feat.fid)
            self.log("Đặt %s làm nhánh đang bắt API hiện tại." % format_feature_label(feat.fid, feat.name))

    def _on_rename_selected_feature(self, event):
        kind, payload = self._selected_left_tree_payload()
        if kind == "FOLDER" and payload:
            new_prefix = JOptionPane.showInputDialog(
                self.main_panel,
                "Đổi tên nhánh Sub-folder '%s' (tự động cập nhật toàn bộ các sub-folder con bên dưới):" % payload,
                payload)
            if new_prefix is not None and u_text(new_prefix).strip():
                self.rename_hierarchy_prefix(payload, new_prefix)
            return
        feat = self._selected_feature_from_table()
        if feat is None:
            return
        new_name = JOptionPane.showInputDialog(
            self.main_panel,
            "Đổi đường dẫn phân cấp Group cho [#%d]:" % feat.fid,
            feat.name)
        if new_name is not None and new_name.strip():
            self.rename_feature(feat.fid, normalize_hierarchy_path(new_name))

    def _on_send_feature_repeater(self, event):
        self._on_send_selected_hierarchy_repeater(event)

    def _on_replay_feature(self, event):
        self._on_replay_selected_hierarchy_or_feature(event)

    def _on_move_groups_feature(self, event):
        groups = self._selected_groups()
        if not groups:
            self._require_group()
            return
        feats = self.features_list()
        options = [f.name for f in feats] + ["+ Nhập đường dẫn Sub-folder mới (N cấp tùy ý)..."]
        choice = JOptionPane.showInputDialog(
            self.main_panel,
            "Chọn đường dẫn Group cho %d API đang chọn (hoặc click đúp trực tiếp cột 'Group Path' trên bảng):"
            % len(groups),
            EXT_NAME, JOptionPane.PLAIN_MESSAGE, None, options, options[0])
        if choice is None:
            return
        if choice == options[-1]:
            name = JOptionPane.showInputDialog(
                self.main_panel, "Nhập đường dẫn Sub-folder mới (ngăn cách bởi '>'):",
                self.active_feature().name)
            if not name:
                return
            feat = self.find_or_create_feature_by_path(name)
            self.move_groups_to_feature(groups, feat.fid)
            return
        feat = self.find_or_create_feature_by_path(choice)
        self.move_groups_to_feature(groups, feat.fid)

    # ---- History Tree actions
    def _selected_tree_payload(self):
        if self.history_tree is None:
            return None, None
        path = self.history_tree.getSelectionPath()
        if path is None:
            return None, None
        return self._extract_node_kind_payload(path.getLastPathComponent())

    def _on_history_tree_selected(self):
        pass

    def _on_rename_tree_feature(self, event):
        kind, payload = self._selected_tree_payload()
        if kind == "FOLDER" and payload:
            new_prefix = JOptionPane.showInputDialog(
                self.main_panel,
                "Đổi tên nhánh Sub-folder '%s' (cập nhật cả các cấp con):" % payload,
                payload)
            if new_prefix is not None and u_text(new_prefix).strip():
                self.rename_hierarchy_prefix(payload, new_prefix)
            return
        feat = None
        if kind == "FEATURE":
            feat = payload
        elif kind == "GROUP":
            feat = self.get_feature(payload.fid)
        elif kind in ("ROLE", "ORIG"):
            feat = self.get_feature(payload[0].fid)
        else:
            feat = self.active_feature()
        if feat is None:
            return
        new_name = JOptionPane.showInputDialog(
            self.main_panel, "Đổi tên đường dẫn phân cấp cho [#%d]:" % feat.fid, feat.name)
        if new_name is not None and new_name.strip():
            self.rename_feature(feat.fid, normalize_hierarchy_path(new_name))

    def _on_send_tree_repeater(self, event):
        kind, payload = self._selected_tree_payload()
        if kind == "FOLDER" and payload:
            for g in self.groups_for_hierarchy_prefix(payload):
                self._dispatch_group_with_selected_mode(g)
        elif kind == "FEATURE":
            for g in self.group_model.groups_for_feature(payload.fid):
                self._dispatch_group_with_selected_mode(g)
        elif kind == "GROUP":
            self._dispatch_group_with_selected_mode(payload)
        elif kind in ("ROLE", "ORIG"):
            g, r = payload
            self.send_to_repeater(g, [r], compact=True, copy_group_name=True)
        else:
            JOptionPane.showMessageDialog(
                self.main_panel, "Hãy chọn một Nhánh, API hoặc Role trong cây.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)

    def _on_replay_tree_selection(self, event):
        kind, payload = self._selected_tree_payload()
        if kind == "FOLDER" and payload:
            self.replay_hierarchy_prefix(payload)
        elif kind == "FEATURE":
            for g in self.group_model.groups_for_feature(payload.fid):
                self.replay(g, self.default_targets(g))
        elif kind == "GROUP":
            self.replay(payload, self.default_targets(payload))
        elif kind == "ROLE":
            g, r = payload
            self.replay(g, [r])
        elif kind == "ORIG":
            g, _ = payload
            self.replay(g, self.default_targets(g))
        else:
            JOptionPane.showMessageDialog(
                self.main_panel, "Hãy chọn một Nhánh, API hoặc Role trong cây.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)

    def _on_jump_to_group_from_tree(self, event):
        kind, payload = self._selected_tree_payload()
        target_group = None
        if kind == "GROUP":
            target_group = payload
        elif kind in ("ROLE", "ORIG"):
            target_group = payload[0]
        elif kind == "FOLDER" and payload:
            groups = self.groups_for_hierarchy_prefix(payload)
            target_group = groups[0] if groups else None
        elif kind == "FEATURE":
            groups = self.group_model.groups_for_feature(payload.fid)
            target_group = groups[0] if groups else None
        if target_group is None:
            return
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        if self.feature_table.getRowCount() > 0:
            self.feature_table.setRowSelectionInterval(0, 0)
        self._select_group_in_table(target_group)
        self.tabs.setSelectedIndex(0)

    def _on_export_history_report(self, event):
        groups = self.group_model.all_groups()
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chưa có dữ liệu API nào để xuất báo cáo.",
                                          EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        chooser = JFileChooser()
        chooser.setSelectedFile(File("theMythOfCrawl_history_report.txt"))
        if chooser.showSaveDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        try:
            text = build_history_summary_text(self.features_list(), groups)
            data = String(text).getBytes("UTF-8")
            Files.write(f.toPath(), data)
            self.log("Exported feature & API history report to %s" % f.getAbsolutePath())
        except Throwable as t:
            JOptionPane.showMessageDialog(self.main_panel, "Export failed: %s" % t, EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)

    # ------------------------------------------------------ Built-in Grouped Repeater Bar
    def _refresh_grouped_repeater_bar(self):
        pill_btn = getattr(self, "btn_repeater_group_pill", None)
        tabs_panel = getattr(self, "repeater_role_tabs_panel", None)
        if pill_btn is None or tabs_panel is None:
            return
        g, cur_res = self.current_selection()
        tabs_panel.removeAll()
        if g is None:
            pill_btn.setText("📁 Chưa chọn API Group ▾")
            tabs_panel.revalidate()
            tabs_panel.repaint()
            return
        entries = g.all_entries()
        arrow = "▾" if getattr(self, "_repeater_group_Expanded", True) else "▸"
        pill_btn.setText("📁 %s: %s %s (%d) %s" % (
            format_group_id(g.gid), g.method, short_path(g.path, 26), len(entries), arrow))
        if getattr(self, "_repeater_group_Expanded", True):
            for idx, entry in enumerate(entries):
                is_orig = getattr(entry, "is_original", False)
                short_lbl = "📌 GỐC" if is_orig else entry.role_name
                if entry.status is not None:
                    short_lbl = "%s (%s)" % (short_lbl, entry.status)
                b = JButton(short_lbl)
                b.setMargin(Insets(2, 7, 2, 7))
                is_active = (entry is cur_res)
                b.setFont(Font("Dialog", Font.BOLD if is_active else Font.PLAIN, 11))
                lvl = getattr(entry, "_audit_level", AUDIT_NONE)
                if is_active:
                    b.setBackground(Color(255, 140, 60))
                    b.setForeground(Color(255, 255, 255))
                elif is_orig:
                    b.setBackground(Color(225, 238, 255))
                    b.setForeground(Color(15, 60, 145))
                elif lvl == AUDIT_WARN:
                    b.setBackground(AuditTableRenderer.BG_WARN)
                    b.setForeground(AuditTableRenderer.FG_WARN)
                elif lvl == AUDIT_INFO:
                    b.setBackground(AuditTableRenderer.BG_INFO)
                    b.setForeground(AuditTableRenderer.FG_INFO)
                elif lvl == AUDIT_OK:
                    b.setBackground(AuditTableRenderer.BG_OK)
                    b.setForeground(AuditTableRenderer.FG_OK)
                else:
                    b.setBackground(Color(244, 245, 248))
                    b.setForeground(Color(40, 40, 40))
                b.addActionListener(_Action(self._select_result_by_model_index, idx))
                tabs_panel.add(b)
        tabs_panel.revalidate()
        tabs_panel.repaint()

    def _select_result_by_model_index(self, model_row):
        if self.result_table is None or self.result_model is None:
            return
        if 0 <= model_row < self.result_model.getRowCount():
            vr = self.result_table.convertRowIndexToView(model_row)
            if vr >= 0:
                self.result_table.setRowSelectionInterval(vr, vr)

    def _on_toggle_or_switch_repeater_group(self, event):
        btn = getattr(self, "btn_repeater_group_pill", None)
        if btn is None or self.group_model is None:
            return
        menu = JPopupMenu()
        expanded = getattr(self, "_repeater_group_Expanded", True)

        def toggle_exp(e):
            self._repeater_group_Expanded = not getattr(self, "_repeater_group_Expanded", True)
            self._refresh_grouped_repeater_bar()

        menu.add(JMenuItem(
            "Thu gọn các Tab Role trong Group này" if expanded else "Mở rộng các Tab Role trong Group này",
            actionPerformed=toggle_exp))

        g, _ = self.current_selection()
        if g is not None:
            menu.add(JMenuItem("▶▶ Gửi (Send) toàn bộ %d Roles của %s" % (len(g.results), format_group_id(g.gid)),
                               actionPerformed=lambda e: self.replay(g, self.default_targets(g))))
            menu.add(JMenuItem("📤 Đẩy Group %s sang Burp Repeater (Tên gọn + Copy tên Group)"
                               % format_group_id(g.gid),
                               actionPerformed=lambda e: self._dispatch_group_with_selected_mode(g)))

        all_g = self.group_model.all_groups()
        if all_g:
            menu.addSeparator()
            for grp in all_g[-25:]:
                item = JMenuItem("📁 %s [%s]: %s %s (%d Roles)" % (
                    format_group_id(grp.gid), grp.feature_name, grp.method,
                    short_path(grp.path, 30), len(grp.results)))
                item.addActionListener(_Action(self._select_group_in_table, grp))
                menu.add(item)
        menu.show(btn, 0, btn.getHeight())

    def _on_inline_repeater_send_one(self, event):
        """Send the currently active Role/Original tab (including any edits made in req_viewer) right inside the group!"""
        g, res = self.current_selection()
        if g is None or res is None:
            self._require_group()
            return
        if self.req_viewer is not None and self.req_viewer.isMessageModified():
            # Only a hand-edited request is pinned as real bytes; untouched roles stay virtual.
            edited = self.req_viewer.getMessage()
            if edited is not None and len(edited) > 0:
                res.request = edited
        self.replay(g, [res])

    def _on_inline_repeater_reset_req(self, event):
        g, res = self.current_selection()
        if g is None or res is None:
            return
        res.request = None  # back to the captured original / the role's virtual request
        self._show_result(res)

    # ------------------------------------------------------ selection helpers
    def _selected_groups(self):
        out = []
        for vr in self.group_table.getSelectedRows():
            g = self.group_model.group_at(self.group_table.convertRowIndexToModel(vr))
            if g is not None:
                out.append(g)
        return out

    def _selected_results(self):
        out = []
        for vr in self.result_table.getSelectedRows():
            r = self.result_model.result_at(self.result_table.convertRowIndexToModel(vr))
            if r is not None and not getattr(r, "is_original", False):
                out.append(r)
        return out

    def current_selection(self):
        """(group, result) currently shown in the detail view (EDT only)."""
        if getattr(self, "result_model", None) is None:
            return None, None
        g = self.result_model.group()
        res = None
        vr = self.result_table.getSelectedRow()
        if vr >= 0:
            res = self.result_model.result_at(self.result_table.convertRowIndexToModel(vr))
        return g, res

    def _on_group_selected(self):
        self._scope_source = "table"
        groups = self._selected_groups()
        g = groups[0] if groups else None
        if g is not self.result_model.group():
            self.result_model.set_group(g)
            self._select_first_result()
        self._refresh_grouped_repeater_bar()
        self.update_status()

    def _select_first_result(self):
        if self.result_model.getRowCount() > 0:
            self.result_table.setRowSelectionInterval(0, 0)
        else:
            self._show_result(None)

    def _on_result_selected(self):
        _, res = self.current_selection()
        self._refresh_grouped_repeater_bar()
        self._show_result(res)

    def _show_result(self, res):
        empty = self.helpers.stringToBytes("")
        g, _ = self.current_selection()
        if res is None:
            if getattr(self, "lbl_req_header", None) is not None:
                self.lbl_req_header.setText(" Request (Chưa chọn Tab)")
            if getattr(self, "lbl_resp_header", None) is not None:
                self.lbl_resp_header.setText(" Response")
            self.req_viewer.setMessage(empty, True)
            self.resp_viewer.setMessage(empty, False)
            return
        if getattr(self, "lbl_req_header", None) is not None and g is not None:
            self.lbl_req_header.setText(" Request [%s | %s] (Có thể sửa trực tiếp & bấm '▶ Send Tab này')"
                                        % (format_group_id(g.gid), res.role_name))
        if getattr(self, "lbl_resp_header", None) is not None:
            st = res.status if res.status is not None else res.state
            ln = res.length if res.length is not None else "-"
            self.lbl_resp_header.setText(" Response [%s | Status: %s | Length: %s]" % (res.role_name, st, ln))
        request = res.request
        response = res.response
        self.req_viewer.setMessage(request if request is not None else empty, True)
        self.resp_viewer.setMessage(response if response is not None else empty, False)

    def _require_group(self):
        g = self.result_model.group()
        if g is None:
            JOptionPane.showMessageDialog(self.main_panel, "Select an API group first.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
        return g

    # ------------------------------------------------------- group actions
    def _on_send_group(self, event):
        groups = self._selected_groups()
        if not groups:
            self._require_group()
            return
        for g in groups:
            self._dispatch_group_with_selected_mode(g)

    def _on_send_role(self, event):
        g = self._require_group()
        if g is None:
            return
        _, cur_res = self.current_selection()
        mode_idx = self.cb_repeater_mode.getSelectedIndex() if getattr(self, "cb_repeater_mode", None) else 0
        use_compact = (mode_idx != 2)
        if cur_res is not None and getattr(cur_res, "is_original", False):
            self.send_to_repeater(g, [cur_res], compact=use_compact, copy_group_name=use_compact)
            return
        results = self._selected_results()
        if not results:
            JOptionPane.showMessageDialog(self.main_panel, "Select one or more role rows.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        self.send_to_repeater(g, results, compact=use_compact, copy_group_name=use_compact)

    def _on_replay_all(self, event):
        groups = self._selected_groups()
        if not groups:
            self._require_group()
            return
        for g in groups:
            self.replay(g, self.default_targets(g))
            self.log("Xếp hàng gửi %d role." % len(g.results), gid=g.gid)

    def _on_replay_selected(self, event):
        g = self._require_group()
        if g is None:
            return
        results = self._selected_results()
        if not results:
            # If user selected only the original row and clicked replay role, replay all roles for convenience
            _, cur_res = self.current_selection()
            if cur_res is not None and getattr(cur_res, "is_original", False):
                self.replay(g, self.default_targets(g))
                return
            JOptionPane.showMessageDialog(self.main_panel, "Hãy chọn ít nhất 1 dòng Role để gửi.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        self.replay(g, results)
        self.log("Xếp hàng gửi %d role đang chọn." % len(results), gid=g.gid)

    def _on_rebuild(self, event):
        for g in self._selected_groups():
            self.rebuild_group(g)

    def _on_show_original(self, event):
        g = self._require_group()
        if g is None:
            return
        if self.result_model.getRowCount() > 0:
            self.result_table.setRowSelectionInterval(0, 0)
        self._show_result(g.orig_result)

    def _on_export_matrix(self, event):
        groups = self.group_model.all_groups()
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "No captured API groups to export.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        chooser = JFileChooser()
        chooser.setSelectedFile(File("theMythOfCrawl_matrix.json"))
        chooser.setFileFilter(FileNameExtensionFilter("JSON files", "json"))
        if chooser.showSaveDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        if not f.getName().lower().endswith(".json"):
            f = File(f.getAbsolutePath() + ".json")
        if f.exists() and JOptionPane.showConfirmDialog(
                self.main_panel, "Overwrite %s?" % f.getName(), EXT_NAME,
                JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        try:
            data = String(groups_to_matrix_json(groups, self.features_list())).getBytes("UTF-8")
            Files.write(f.toPath(), data)
            self.log("Exported %d group(s) matrix to %s" % (len(groups), f.getAbsolutePath()))
        except Throwable as t:
            JOptionPane.showMessageDialog(self.main_panel, "Export failed: %s" % t, EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)

    def _on_delete_groups(self, event):
        groups = self._selected_groups()
        if not groups:
            return
        self.group_model.remove_groups(groups)
        self.forget_dedup(groups)
        if self.result_model.group() in groups:
            self.result_model.set_group(None)
            self._show_result(None)
        self._refresh_feature_views()
        self.update_status()

    def _on_clear_groups(self, event):
        if JOptionPane.showConfirmDialog(
                self.main_panel, "Xóa toàn bộ các API đã bắt, đặt lại danh sách Nhánh về mặc định và xóa Dedup cache?",
                EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.group_model.clear()
        self.result_model.set_group(None)
        self._show_result(None)
        with self._state_lock:
            self._seen_keys.clear()
            self._seen_gid.clear()
            self._skipped_count = 0
            self._last_skip_reason = ""
            self._next_gid = 1
            self._next_fid = 2
            self._active_fid = 1
            self._features = [FeatureGroup(1, DEFAULT_HIERARCHY_PATH)]
        with self._ui_lock:
            self._p_new = []
            self._p_dirty = {}
            self._p_done_res = set()
        self._tree_states = {"left": self._new_tree_state(), "history": self._new_tree_state(),
                             "log": self._new_tree_state(), "full": self._new_tree_state()}
        with self._log_lock:
            self._log_by_gid = {}
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self._refresh_feature_views()
        self.log("All captured APIs, hierarchy history, and dedup cache reset.")
        self.update_status()

    def forget_dedup(self, groups):
        """Deleted APIs are captured again the next time you pass by them (their dedup keys are dropped)."""
        n = 0
        with self._state_lock:
            for g in groups:
                key = getattr(g, "dedup_key", None)
                if key is not None and self._seen_gid.get(key) == g.gid:
                    self._seen_keys.discard(key)
                    del self._seen_gid[key]
                    n += 1
        if n:
            self.log("Đã xóa %d API: lần sau đi qua chúng sẽ được bắt lại." % n)
        return n

    def _on_reset_dedup(self, event):
        with self._state_lock:
            n = len(self._seen_keys)
            self._seen_keys.clear()
            self._seen_gid.clear()
            self._skipped_count = 0
            self._last_skip_reason = ""
        self.log("Dedup cache reset (%d endpoint key(s) forgotten)." % n)
        self.update_status()

    # -------------------------------------------------------- role actions
    def _roles_changed(self, select_index=None):
        self.save_roles()
        self.role_model.reload()
        if select_index is not None and 0 <= select_index < self.role_model.getRowCount():
            self.role_table.setRowSelectionInterval(select_index, select_index)
        self._on_role_row_selected()
        self.update_status()

    def _on_role_row_selected(self):
        if self.inline_role_editor is None or self.role_table is None:
            return
        idx = self.role_table.getSelectedRow()
        if idx < 0 and self._inline_target[0] == "orig":
            return  # the API gốc profile stays in the editor until a role row is picked
        self._inline_target = ("role", idx)
        self.inline_role_editor.set_original_mode(False)
        self.inline_role_editor.setBorder(BorderFactory.createTitledBorder(
            "Chỉnh sửa Profile đang chọn (Header / Cookie / Session / JWT - Bấm 'Save Profile Changes' để lưu)"))
        if 0 <= idx < self.roles.count():
            self.inline_role_editor.load_role(self.roles.get(idx))
        else:
            self.inline_role_editor.load_role(None)

    def _on_save_inline_role(self, updated_role):
        if self._inline_target[0] == "orig":
            self.save_original_profile(updated_role)
            self.log("Đã lưu profile API gốc (%d rule, %s)." % (
                len(self.original_profile.get("headers", [])),
                "đang áp dụng" if self.original_profile.get("enabled") else "đang tắt"))
            return
        idx = self.role_table.getSelectedRow()
        if idx < 0 or idx >= self.roles.count():
            idx = self.roles.add(updated_role)
        else:
            self.roles.update(idx, updated_role)
        self.save_roles()
        self.role_model.reload()
        if 0 <= idx < self.role_model.getRowCount():
            self.role_table.setRowSelectionInterval(idx, idx)
        self.update_status()
        self.log("Saved profile changes for role '%s' (%d rule(s))." %
                 (updated_role["name"], len(updated_role.get("headers", []))))

    def _selected_role_index(self):
        r = self.role_table.getSelectedRow()
        if r < 0:
            JOptionPane.showMessageDialog(self.main_panel, "Select a role first.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
        return r

    def _on_add_role(self, event):
        n = self.roles.count() + 1
        template = {"name": "%02d_Role" % n, "enabled": True,
                    "headers": [{"name": "Authorization", "value": "", "mode": MODE_REPLACE}]}
        role = RoleEditorDialog(self.main_panel, template, "Add Role").show()
        if role is not None:
            self._roles_changed(self.roles.add(role))

    def _on_edit_role(self, event):
        idx = self._selected_role_index()
        if idx < 0:
            return
        role = RoleEditorDialog(self.main_panel, self.roles.get(idx), "Edit Role").show()
        if role is not None:
            self.roles.update(idx, role)
            self._roles_changed(idx)

    def _on_duplicate_role(self, event):
        idx = self._selected_role_index()
        if idx < 0:
            return
        role = self.roles.get(idx)
        role["name"] = role["name"] + "_copy"
        self._roles_changed(self.roles.add(role))

    def _on_delete_roles(self, event):
        rows = list(self.role_table.getSelectedRows())
        if not rows:
            return
        if JOptionPane.showConfirmDialog(self.main_panel, "Delete %d role(s)?" % len(rows), EXT_NAME,
                                         JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.roles.remove(rows)
        self._roles_changed(min(rows[0], max(self.roles.count() - 1, 0)))

    def _on_move_role(self, delta):
        idx = self.role_table.getSelectedRow()
        if idx < 0:
            return
        self._roles_changed(self.roles.move(idx, delta))

    def _on_enable_all(self, enabled):
        """'Bật / Tắt tất cả' asks where: every API, some branches, or some APIs only."""
        self.open_role_scope_dialog(enabled, "global", roles=[r["name"] for r in self.roles.all()])

    def _on_import_roles(self, event):
        chooser = JFileChooser()
        chooser.setFileFilter(FileNameExtensionFilter("JSON files", "json"))
        if chooser.showOpenDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        try:
            text = String(Files.readAllBytes(f.toPath()), "UTF-8")
            imported = roles_from_json("%s" % text)
        except Throwable as t:
            JOptionPane.showMessageDialog(self.main_panel, "Import failed: %s" % t, EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)
            return
        except Exception as e:
            JOptionPane.showMessageDialog(self.main_panel, "Import failed: %s" % e, EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)
            return
        if not imported:
            JOptionPane.showMessageDialog(self.main_panel, "No roles found in file.", EXT_NAME,
                                          JOptionPane.WARNING_MESSAGE)
            return
        choice = 0
        if self.roles.count() > 0:
            choice = JOptionPane.showOptionDialog(
                self.main_panel, "Import %d role(s). Replace the existing %d role(s) or append?"
                % (len(imported), self.roles.count()), EXT_NAME, JOptionPane.DEFAULT_OPTION,
                JOptionPane.QUESTION_MESSAGE, None, ["Replace", "Append", "Cancel"], "Replace")
        if choice == 0:
            self.roles.set_all(imported)
        elif choice == 1:
            for r in imported:
                self.roles.add(r)
        else:
            return
        self._roles_changed(0)
        self.log("Imported %d role(s) from %s" % (len(imported), f.getAbsolutePath()))

    def _on_export_roles(self, event):
        chooser = JFileChooser()
        chooser.setSelectedFile(File("theMythOfCrawl_roles.json"))
        chooser.setFileFilter(FileNameExtensionFilter("JSON files", "json"))
        if chooser.showSaveDialog(self.main_panel) != JFileChooser.APPROVE_OPTION:
            return
        f = chooser.getSelectedFile()
        if not f.getName().lower().endswith(".json"):
            f = File(f.getAbsolutePath() + ".json")
        if f.exists() and JOptionPane.showConfirmDialog(
                self.main_panel, "Overwrite %s?" % f.getName(), EXT_NAME,
                JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        try:
            data = String(roles_to_json(self.roles.all())).getBytes("UTF-8")
            Files.write(f.toPath(), data)
            self.log("Exported %d role(s) to %s" % (self.roles.count(), f.getAbsolutePath()))
        except Throwable as t:
            JOptionPane.showMessageDialog(self.main_panel, "Export failed: %s" % t, EXT_NAME,
                                          JOptionPane.ERROR_MESSAGE)

    def _on_load_template(self, event):
        templates = default_role_templates()
        choice = 0
        if self.roles.count() > 0:
            choice = JOptionPane.showOptionDialog(
                self.main_panel, "Load 10 starter roles (01_Admin .. 10_Guest). Replace existing %d role(s) or append?"
                % self.roles.count(), EXT_NAME, JOptionPane.DEFAULT_OPTION,
                JOptionPane.QUESTION_MESSAGE, None, ["Replace", "Append", "Cancel"], "Replace")
        if choice == 0:
            self.roles.set_all(templates)
        elif choice == 1:
            for r in templates:
                self.roles.add(r)
        else:
            return
        self._roles_changed(0)
        self.log("Loaded 10 starter role profiles.")
