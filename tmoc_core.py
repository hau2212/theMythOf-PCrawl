# -*- coding: utf-8 -*-
from __future__ import unicode_literals
"""
theMythOfCrawl core: path / Excel matching, xlsx read & write, role rules, send dispatcher,
placement book, table models, renderers and dialogs.

Kept in its own module because Jython compiles one .py file into one Java class, and a
single class cannot exceed the JVM size limits. theMythOfCrawl.py (the file loaded in Burp)
imports everything from here.
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
                         BoxLayout, Box, JTree, JRadioButton, ButtonGroup, JFrame, JList, DefaultListModel)
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
EXT_VERSION = "1.11.0"
SETTINGS_KEY_ROLES = "tmoc.roles.v1"
SETTINGS_KEY_ORIGINAL = "tmoc.original_profile.v1"
SETTINGS_KEY_ROLE_SCOPES = "tmoc.role_scopes.v1"
SETTINGS_KEY_TARGET_HITS = "tmoc.target_hits.v1"
SETTINGS_KEY_PLACES = "tmoc.places.v1"
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
AUDIT_PENDING = "PENDING"    # Grey: captured, its place in the tree is not confirmed yet

AUDIT_FILTER_ALL = "ALL"
AUDIT_FILTER_OPTIONS = [
    ("Tất cả API (All)", AUDIT_FILTER_ALL),
    ("Vàng INFO: Có Role lỗi / Lệch quyền", AUDIT_INFO),
    ("Cam WARN: Nghi vấn Bypass (Guest 2xx)", AUDIT_WARN),
    ("Đỏ ERROR: Có lỗi 5xx / Mất kết nối", AUDIT_ERROR),
    ("Xanh OK: Tất cả Role 2xx", AUDIT_OK),
    ("Chưa Gửi / Chưa Replay (Pending)", AUDIT_NONE),
    ("Xám ⏳: Chờ xác nhận vị trí", AUDIT_PENDING),
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
    "confirm_new_apis": True,
    "restore_known_place": True,
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


def display_level(g):
    """Grey while the API's place is not confirmed, else its audit colour."""
    if getattr(g, "pending", False):
        return AUDIT_PENDING
    return _group_level(g)


def pending_label(g):
    if not getattr(g, "pending", False):
        return u""
    hint = getattr(g, "place_hint", None)
    if hint:
        return u"⏳ Chờ xác nhận · ↩ quay về chỗ cũ"
    return u"⏳ Chờ xác nhận vị trí"


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
    if getattr(g, "pending", False):
        text = u"⏳ " + text + u"   ·   " + pending_label(g)[2:]
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


PLACE_ACTIONS = {
    "capture": u"Bắt mới",
    "pending": u"⏳ Bắt mới · chờ xác nhận",
    "return": u"↩ Quay về chỗ cũ · chờ xác nhận",
    "confirm": u"✔ Xác nhận vị trí",
    "move": u"↪ Chuyển vị trí",
    "revert": u"↶ Hoàn tác vị trí",
    "delete": u"🗑 Xóa API (giữ chỗ)",
    "rename": u"✏ Đổi tên nhánh",
    "edit": u"✏ Sửa giữ chỗ",
    "forget": u"✖ Quên giữ chỗ",
    "manual": u"➕ Thêm giữ chỗ",
    "recapture": u"♻ Cho phép bắt lại",
}


class PlacementBook(object):
    """
    'Giữ chỗ': for every endpoint (method + host + path, the dedup identity) the branch it was
    last confirmed in, whether an API for it is alive, how often it was deleted / met / skipped as
    duplicate, and an audit log of every placement change (capture, confirm, move, revert,
    delete, rename, manual edits). Survives deleting APIs, 'Xóa toàn bộ' and dedup resets, so a
    deleted API that comes back returns to its old place.
    """
    MAX_LOG = 5000
    MAX_HISTORY = 30

    def __init__(self):
        self._lock = threading.RLock()
        self.entries = {}
        self.log = []
        self._seq = 0
        self.dirty = False

    def get(self, key):
        return self.entries.get(key)

    def ensure(self, key, method=u"", host=u"", path=u""):
        with self._lock:
            rec = self.entries.get(key)
            if rec is None:
                rec = {"key": key, "method": method, "host": host, "path": strip_query(u_text(path)),
                       "place": None, "gid": None, "pending": False, "deleted": 0, "deleted_at": None,
                       "seen": 0, "skipped": 0, "last_seen": None, "last_found_at": None, "history": []}
                self.entries[key] = rec
                self.dirty = True
            return rec

    def set_place(self, key, place):
        with self._lock:
            rec = self.entries.get(key)
            if rec is None:
                return
            if place and place != rec.get("place"):
                rec["history"].append({"time": time.strftime("%d/%m %H:%M:%S"), "place": place})
                del rec["history"][:-self.MAX_HISTORY]
            rec["place"] = place
            self.dirty = True

    def update(self, key, **fields):
        with self._lock:
            rec = self.entries.get(key)
            if rec is not None:
                rec.update(fields)
                self.dirty = True
            return rec

    def seen(self, key, found_at, skipped=False):
        with self._lock:
            rec = self.entries.get(key)
            if rec is None:
                return None
            rec["seen"] = rec.get("seen", 0) + 1
            if skipped:
                rec["skipped"] = rec.get("skipped", 0) + 1
            rec["last_seen"] = time.strftime("%d/%m %H:%M:%S")
            rec["last_found_at"] = found_at
            self.dirty = True
            return rec

    def deleted(self, key, gid):
        with self._lock:
            rec = self.entries.get(key)
            if rec is None or (rec.get("gid") is not None and rec.get("gid") != gid):
                return None
            rec["gid"] = None
            rec["pending"] = False
            rec["deleted"] = rec.get("deleted", 0) + 1
            rec["deleted_at"] = time.strftime("%d/%m %H:%M:%S")
            self.dirty = True
            return rec

    def forget(self, key):
        with self._lock:
            self.dirty = True
            return self.entries.pop(key, None)

    def rename_prefix(self, old, new):
        n = 0
        with self._lock:
            for rec in self.entries.values():
                place = rec.get("place")
                if place and hierarchy_matches_prefix(place, old):
                    rec["place"] = replace_hierarchy_prefix(place, old, new)
                    n += 1
            self.dirty = True
        return n

    def event(self, action, key=None, gid=None, method=u"", path=u"", src=None, dst=None, note=u""):
        with self._lock:
            self._seq += 1
            ev = {"id": self._seq, "time": time.strftime("%d/%m %H:%M:%S"), "action": action, "key": key,
                  "gid": gid, "method": method, "path": strip_query(u_text(path)), "src": src, "dst": dst,
                  "note": note}
            self.log.append(ev)
            del self.log[:-self.MAX_LOG]
            self.dirty = True
            return ev

    def events_for(self, key):
        return [e for e in self.log if e.get("key") == key]

    def deleted_under(self, prefix):
        """Remembered places of endpoints with no live API, inside `prefix`."""
        return [r for r in self.entries.values()
                if r.get("gid") is None and r.get("place") and hierarchy_matches_prefix(r["place"], prefix)]

    def to_json(self):
        with self._lock:
            self.dirty = False
            return json.dumps({"entries": self.entries, "log": self.log[-self.MAX_LOG:], "seq": self._seq})

    def load_json(self, raw):
        try:
            data = json.loads(raw) if raw else {}
        except Exception:
            data = {}
        with self._lock:
            self.entries = dict(data.get("entries") or {})
            for rec in self.entries.values():
                rec["gid"] = None          # captured APIs do not survive a reload: every place is a placeholder
                rec["pending"] = False
                rec.setdefault("history", [])
            self.log = list(data.get("log") or [])
            self._seq = int(data.get("seq") or len(self.log))
            self.dirty = False


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


def build_api_workbook(groups, targets=None, copy_format=None, position_as_copy=False, label_fn=None, hits=None,
                       places=None):
    api_rows, role_rows = api_export_rows(groups, label_fn)
    sheets = []
    if places is not None and places.entries:
        sheets.append((u"Vị trí API (giữ chỗ)", PLACE_COLS, [c for _, _, c in place_rows(places)],
                       [9, 48, 26, 44, 10, 18, 10, 9, 12, 16, 44, 12]))
    if places is not None and places.log:
        sheets.append((u"Nhật ký vị trí", PLACE_LOG_COLS, [c for _, c in place_log_rows(places)],
                       [6, 16, 28, 9, 9, 48, 40, 40, 50]))
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
        self.book_key = None      # endpoint identity in the placement book ('giữ chỗ')
        self.pending = False      # place in the tree not confirmed yet (grey)
        self.place_hint = None    # {'old', 'found', 'old_missing', 'deleted'} when it came back to its old place
        self.place_history = []   # previous branches, for 'về vị trí trước' 
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
            if self._filter_audit == AUDIT_PENDING:
                return bool(getattr(g, "pending", False))
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
        if getattr(g, "pending", False):
            return AUDIT_PENDING
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
            summary = g._audit_summary if g._audit_summary is not None else evaluate_group_audit(g)[1]
            if getattr(g, "pending", False):
                return pending_label(g) + u" · " + summary
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
        AUDIT_PENDING: (128, 128, 140),
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


PLACE_STATES = {"live": u"Đang có API", "pending": u"⏳ Chờ xác nhận", "deleted": u"👻 Đã xóa (giữ chỗ)",
                "none": u"Chưa có vị trí"}


def place_state(rec):
    if rec.get("gid") is not None:
        return "pending" if rec.get("pending") else "live"
    return "deleted" if rec.get("place") else "none"


def place_rows(book, view=0, text=u""):
    """Rows of the placement book for the 'Vị trí & Audit' tab; view 0 all, 1 live, 2 deleted, 3 pending."""
    wanted = {1: ("live",), 2: ("deleted", "none"), 3: ("pending",)}.get(view)
    text = u_text(text).strip().lower()
    out = []
    for rec in book.entries.values():
        st = place_state(rec)
        if wanted and st not in wanted:
            continue
        cells = [rec.get("method"), rec.get("path"), rec.get("host"), rec.get("place") or u"",
                 format_api_label(rec["gid"]) if rec.get("gid") is not None else u"", PLACE_STATES[st],
                 rec.get("deleted", 0), rec.get("seen", 0), rec.get("skipped", 0), rec.get("last_seen") or u"",
                 rec.get("last_found_at") or u"", max(len(rec.get("history") or []) - 1, 0)]
        if text and text not in u" ".join([u_text(c) for c in cells]).lower():
            continue
        out.append((rec, st, cells))
    out.sort(key=lambda x: ((x[0].get("place") or u"~").lower(), u_text(x[0].get("path")), x[0].get("method")))
    return out


def place_log_rows(book, key=None, text=u""):
    text = u_text(text).strip().lower()
    out = []
    for ev in reversed(book.log):
        if key is not None and ev.get("key") != key:
            continue
        cells = [ev.get("id"), ev.get("time"), PLACE_ACTIONS.get(ev.get("action"), ev.get("action")),
                 format_api_label(ev["gid"]) if ev.get("gid") is not None else u"", ev.get("method") or u"",
                 ev.get("path") or u"", ev.get("src") or u"", ev.get("dst") or u"", ev.get("note") or u""]
        if text and text not in u" ".join([u_text(c) for c in cells]).lower():
            continue
        out.append((ev, cells))
    return out


class _RowsModel(AbstractTableModel):
    """Read-only table over prepared rows: (payload, level, cells)."""

    def __init__(self, cols):
        self.COLS = cols
        self._rows = []

    def set_rows(self, rows):
        self._rows = rows
        self.fireTableDataChanged()

    def payload_at(self, r):
        return self._rows[r][0] if 0 <= r < len(self._rows) else None

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
        return self._rows[r][2][c]


PLACE_COLS = ["Method", "Path", "Host", "Vị trí giữ chỗ", "API hiện tại", "Trạng thái", "Đã xóa (lần)",
              "Lần gặp", "Bỏ qua do trùng", "Gặp lần cuối", "Gặp lần cuối tại (đích lúc đó)", "Đổi vị trí (lần)"]
PLACE_LOG_COLS = ["#", "Thời gian", "Hành động", "API #", "Method", "Path", "Từ", "Sang", "Ghi chú"]
PLACE_STATE_LEVEL = {"live": AUDIT_OK, "pending": AUDIT_PENDING, "deleted": AUDIT_NONE, "none": AUDIT_NONE}
PLACE_ACTION_LEVEL = {"pending": AUDIT_PENDING, "return": AUDIT_PENDING, "confirm": AUDIT_OK, "move": AUDIT_REDIRECT,
                      "revert": AUDIT_REDIRECT, "delete": AUDIT_ERROR, "forget": AUDIT_ERROR, "edit": AUDIT_INFO,
                      "manual": AUDIT_INFO, "rename": AUDIT_INFO, "recapture": AUDIT_INFO}


class PathPickerDialog(object):
    """Pick a branch: filterable list of every known branch, or type a new one ('/ > a > b')."""

    def __init__(self, parent, title, paths, initial=u"", hint=u""):
        self._result = None
        owner = SwingUtilities.getWindowAncestor(parent) if parent is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle(title)
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))
        self._paths = sorted(set([u_text(x) for x in paths if x]), key=lambda x: [q.lower() for q in split_hierarchy_path(x)])
        head = JPanel(BorderLayout(4, 4))
        head.setBorder(BorderFactory.createEmptyBorder(8, 10, 0, 10))
        if hint:
            head.add(JLabel(hint), BorderLayout.NORTH)
        row = JPanel(BorderLayout(4, 0))
        row.add(JLabel("Lọc:"), BorderLayout.WEST)
        self.filter = JTextField()
        self.filter.getDocument().addDocumentListener(_DocChange(self._refilter))
        row.add(self.filter, BorderLayout.CENTER)
        head.add(row, BorderLayout.SOUTH)
        self.dialog.add(head, BorderLayout.NORTH)
        self.model = DefaultListModel()
        self.list = JList(self.model)
        self.list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.list.addListSelectionListener(_ListPick(self._picked))
        self.list.addMouseListener(_DoubleClick(lambda: self._on_ok(None)))
        scroll = JScrollPane(self.list)
        scroll.setBorder(BorderFactory.createTitledBorder("Các đường dẫn đã có (click đúp để chọn)"))
        self.dialog.add(scroll, BorderLayout.CENTER)
        bottom = JPanel(BorderLayout(4, 4))
        bottom.setBorder(BorderFactory.createEmptyBorder(0, 10, 8, 10))
        new_row = JPanel(BorderLayout(4, 0))
        new_row.add(JLabel("Đường dẫn (sửa hoặc nhập mới, ngăn cách bởi '>'):"), BorderLayout.NORTH)
        self.field = JTextField(u_text(initial))
        self.field.addActionListener(_Action(self._on_ok))
        new_row.add(self.field, BorderLayout.CENTER)
        bottom.add(new_row, BorderLayout.NORTH)
        btns = JPanel(FlowLayout(FlowLayout.RIGHT, 6, 0))
        ok = JButton("Chọn", actionPerformed=self._on_ok)
        ok.setFont(ok.getFont().deriveFont(Font.BOLD))
        btns.add(ok)
        btns.add(JButton("Hủy", actionPerformed=lambda e: self.dialog.dispose()))
        bottom.add(btns, BorderLayout.SOUTH)
        self.dialog.add(bottom, BorderLayout.SOUTH)
        self._refilter()
        self.dialog.setSize(Dimension(640, 520))
        self.dialog.setLocationRelativeTo(owner)

    def _refilter(self):
        text = u_text(self.filter.getText()).strip().lower()
        self.model.clear()
        for x in self._paths:
            if not text or text in x.lower():
                self.model.addElement(x)

    def _picked(self):
        v = self.list.getSelectedValue()
        if v is not None:
            self.field.setText(u_text(v))

    def _on_ok(self, e):
        text = u_text(self.field.getText()).strip()
        if text:
            self._result = normalize_hierarchy_path(text) if ">" in text else text
            self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)
        return self._result


class _ListPick(ListSelectionListener):
    def __init__(self, fn):
        self._fn = fn

    def valueChanged(self, event):
        if not event.getValueIsAdjusting():
            self._fn()


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
            if row >= 0 and not self._tree.isRowSelected(row):
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


# Everything above is re-exported by theMythOfCrawl.py (underscore names included).
def _public_names():
    out = []
    for name in list(globals().keys()):
        # Jython leaves temporary '_[n_m]' entries from list comprehensions in globals
        if not name.startswith("__") and re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", name):
            out.append(name)
    return out


__all__ = _public_names()
