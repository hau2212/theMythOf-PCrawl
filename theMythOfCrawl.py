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
  * Every Swing mutation goes through SwingUtilities.invokeLater (ui_call()).
"""

import base64
import json
import re
import threading
import time
import traceback

from burp import IBurpExtender
from burp import ITab
from burp import IHttpListener
from burp import IContextMenuFactory
from burp import IExtensionStateListener
from burp import IMessageEditorController

from java.awt import (BorderLayout, FlowLayout, GridBagLayout, GridBagConstraints, GridLayout,
                      Insets, Dimension, Color, Font, Toolkit)
from java.awt.datatransfer import StringSelection
from java.awt.event import MouseAdapter, ActionListener
from java.lang import Runnable, Boolean, Integer, String, Throwable
from java.util import ArrayList, Arrays
from java.util.concurrent import Executors, TimeUnit
from java.io import File
from java.nio.file import Files
from javax.swing import (JPanel, JLabel, JButton, JCheckBox, JTextField, JTable, JScrollPane,
                         JSplitPane, JTabbedPane, JTextArea, JMenuItem, JPopupMenu, JOptionPane,
                         JFileChooser, JDialog, JComboBox, JSpinner, SpinnerNumberModel,
                         ListSelectionModel, SwingUtilities, BorderFactory, DefaultCellEditor,
                         BoxLayout, Box, JTree)
from javax.swing.event import ListSelectionListener, TreeSelectionListener, ChangeListener
from javax.swing.table import AbstractTableModel, DefaultTableCellRenderer
from javax.swing.tree import DefaultMutableTreeNode, DefaultTreeModel, DefaultTreeCellRenderer, TreeSelectionModel
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
EXT_VERSION = "1.5.0"
SETTINGS_KEY_ROLES = "tmoc.roles.v1"
SETTINGS_KEY_CONFIG = "tmoc.config.v2"

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
    "throttle_ms": 0,
    "short_path_len": 40,
}

STATE_ORIGIN = "GỐC (Proxy)"
STATE_NOT_SENT = "Not sent"
STATE_QUEUED = "Queued"
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
    if group is None or not getattr(group, "results", None):
        return AUDIT_NONE, "Chưa có Role"
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


def evaluate_feature_audit(feature_groups):
    """Summarize the audit status across all API groups belonging to a Feature/Hierarchy node."""
    f_groups = list(feature_groups or [])
    if not f_groups:
        return AUDIT_NONE, "-"
    info_count = 0
    ok_count = 0
    for g in f_groups:
        lvl = getattr(g, "_audit_level", None)
        if lvl is None:
            lvl, _ = evaluate_group_audit(g)
        if lvl in (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR):
            info_count += 1
        elif lvl == AUDIT_OK:
            ok_count += 1
    if info_count > 0:
        return AUDIT_INFO, "INFO: %d/%d API có Role lỗi/lệch" % (info_count, len(f_groups))
    if ok_count > 0:
        return AUDIT_OK, "OK: %d/%d API 2xx" % (ok_count, len(f_groups))
    return AUDIT_NONE, "Chưa Gửi (%d API)" % len(f_groups)


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
    cfg["throttle_ms"] = max(0, min(60000, cfg["throttle_ms"]))
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
            if self._log:
                self._log("Unhandled Java exception in task: %s" % t)
        except Exception:
            if self._log:
                self._log("Unhandled exception in task:\n%s" % traceback.format_exc())


def ui_call(fn):
    """Run fn on the Swing Event Dispatch Thread."""
    if SwingUtilities.isEventDispatchThread():
        fn()
    else:
        SwingUtilities.invokeLater(_Task(fn))


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


class RoleResult(object):
    def __init__(self, role_name, role_index, request_bytes, is_stripped_auth=False, is_original=False):
        self.role_name = u_text(role_name)
        self.role_index = role_index
        self.request = request_bytes
        self.is_stripped_auth = bool(is_stripped_auth)
        self.is_original = bool(is_original)
        self.response = None
        self.status = None
        self.length = None
        self.elapsed_ms = None
        self.state = STATE_ORIGIN if is_original else STATE_NOT_SENT
        self.error = ""
        self.sent_count = 0
        self.tab_name = ""
        self._audit_level = None
        self._audit_badge = None


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
        self.orig_request = orig_request
        self.orig_response = orig_response
        self.orig_status = None
        self.orig_length = None
        self.source = u_text(source)
        self.created = time.strftime("%H:%M:%S")
        self.orig_result = RoleResult(
            "[API GỐC] 00_Original (Acc Crawl)", -1, orig_request,
            is_stripped_auth=False, is_original=True
        )
        self.orig_result.response = orig_response
        self.orig_result.state = STATE_ORIGIN if orig_response is not None else STATE_NOT_SENT
        self.orig_result.tab_name = repeater_tab_name(gid, method, path, "00_Original_Crawl")
        self.results = []
        self._audit_level = None
        self._audit_summary = None

    def sync_original_meta(self, short_path_len=40, include_feature=False):
        self.orig_result.request = self.orig_request
        self.orig_result.response = self.orig_response
        self.orig_result.status = self.orig_status
        self.orig_result.length = self.orig_length
        self.orig_result.state = STATE_ORIGIN if self.orig_response is not None else STATE_NOT_SENT
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
    """
    COLS = ["#", "Tên chức năng", "Số API", "Trạng thái Role (Màu)", "Danh sách API"]

    def __init__(self, ext):
        self._ext = ext

    def getRowCount(self):
        return 1 + len(self._ext.features_list())

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
        if r <= 0:
            return None
        feats = self._ext.features_list()
        idx = r - 1
        return feats[idx] if 0 <= idx < len(feats) else None

    def audit_level_at(self, r):
        all_groups = self._ext.group_model.all_groups() if self._ext.group_model else []
        if r <= 0:
            lvl, _ = evaluate_feature_audit(all_groups)
            return lvl
        f = self.feature_at_row(r)
        if f is None:
            return AUDIT_NONE
        f_groups = [g for g in all_groups if g.fid == f.fid]
        lvl, _ = evaluate_feature_audit(f_groups)
        return lvl

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
        all_groups = self._ext.group_model.all_groups() if self._ext.group_model else []
        feats = self._ext.features_list()
        if r == 0:
            if c == 0:
                return "ALL"
            if c == 1:
                return "[Tất cả: %d chức năng]" % len(feats)
            if c == 2:
                return Integer(len(all_groups))
            if c == 3:
                _, summary = evaluate_feature_audit(all_groups)
                return summary
            if c == 4:
                if not all_groups:
                    return "-"
                return "%s .. %s" % (format_api_label(all_groups[0].gid),
                                     format_api_label(all_groups[-1].gid))
            return ""
        f = feats[r - 1]
        f_groups = [g for g in all_groups if g.fid == f.fid]
        if c == 0:
            active = (f.fid == self._ext.active_feature_id())
            return ("* #%d" % f.fid) if active else ("#%d" % f.fid)
        if c == 1:
            return format_feature_label(f.fid, f.name)
        if c == 2:
            return Integer(len(f_groups))
        if c == 3:
            _, summary = evaluate_feature_audit(f_groups)
            return summary
        if c == 4:
            if not f_groups:
                return "(chưa có API)"
            if len(f_groups) <= 3:
                return ", ".join([format_api_label(g.gid) for g in f_groups])
            return "%s .. %s (%d)" % (format_api_label(f_groups[0].gid),
                                      format_api_label(f_groups[-1].gid), len(f_groups))
        return ""


class GroupTableModel(AbstractTableModel):
    COLS = ["API #", "Group", "Group Path (Click đúp để chọn/đổi)", "Đánh giá / Màu (Info)", "Method", "Host", "Path",
            "Orig", "Orig Len", "1 Gốc + Roles", "Đã gửi", "Source", "Time"]

    def __init__(self, ext=None):
        self._ext = ext
        self._all_rows = []
        self._rows = []
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

    def set_feature_filter(self, fid):
        self._filter_fid = fid
        self._filter_prefix = None
        self._rebuild_view()
        self.fireTableDataChanged()

    def set_hierarchy_filter(self, prefix_path):
        self._filter_fid = None
        self._filter_prefix = u_text(prefix_path).strip() if prefix_path else None
        self._rebuild_view()
        self.fireTableDataChanged()

    def hierarchy_filter(self):
        return self._filter_prefix

    def feature_filter(self):
        return self._filter_fid

    def set_audit_filter(self, audit_level):
        self._filter_audit = audit_level or AUDIT_FILTER_ALL
        self._rebuild_view()
        self.fireTableDataChanged()

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
        self._all_rows.append(group)
        if self._matches(group):
            self._rows.append(group)
            n = len(self._rows) - 1
            self.fireTableRowsInserted(n, n)

    def remove_groups(self, groups):
        ids = set([id(g) for g in groups])
        self._all_rows = [g for g in self._all_rows if id(g) not in ids]
        self._rebuild_view()
        self.fireTableDataChanged()

    def clear(self):
        self._all_rows = []
        self._rows = []
        self.fireTableDataChanged()

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
        for i, g in enumerate(self._rows):
            if g is group:
                if self._matches(group):
                    self.fireTableRowsUpdated(i, i)
                    return
                break
        self._rebuild_view()
        self.fireTableDataChanged()

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
            return "1 Gốc + %d Role" % len(g.results)
        if c == 10:
            done = len([x for x in g.results if x.state in (STATE_DONE, STATE_ERROR)])
            return "%d/%d" % (done, len(g.results))
        if c == 11:
            return g.source
        if c == 12:
            return g.created
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
        self.fireTableDataChanged()

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


class AuditTableRenderer(DefaultTableCellRenderer):
    """
    Row & cell color renderer for FeatureTable, GroupTable, and ResultTable:
      - Yellow INFO (Color(255, 247, 195)): Any role call failed (401/403/4xx/5xx/Error) or permission diff
      - Green OK    (Color(228, 248, 232)): All roles 2xx OK
      - Orange WARN (Color(255, 230, 195)): Suspected auth bypass (Guest role got 2xx)
      - Red ERROR   (Color(255, 222, 222)): Server 5xx / timeout
      - Blue REDIR  (Color(225, 239, 255)): 3xx redirect
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

    def __init__(self, model, status_col=None, audit_col=None):
        DefaultTableCellRenderer.__init__(self)
        self._model = model
        self._status_col = status_col
        self._audit_col = audit_col

    def getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column):
        comp = DefaultTableCellRenderer.getTableCellRendererComponent(
            self, table, value, isSelected, hasFocus, row, column)
        if isSelected:
            return comp

        model_row = table.convertRowIndexToModel(row)
        model_col = table.convertColumnIndexToModel(column)
        lvl = self._model.audit_level_at(model_row) if hasattr(self._model, "audit_level_at") else AUDIT_NONE

        if lvl == AUDIT_INFO:
            comp.setBackground(self.BG_INFO)
        elif lvl == AUDIT_OK:
            comp.setBackground(self.BG_OK)
        elif lvl == AUDIT_WARN:
            comp.setBackground(self.BG_WARN)
        elif lvl == AUDIT_ERROR:
            comp.setBackground(self.BG_ERR)
        elif lvl == AUDIT_REDIRECT:
            comp.setBackground(self.BG_REDIR)
        else:
            comp.setBackground(self.BG_EVEN if (row % 2 == 0) else self.BG_ODD)

        comp.setForeground(self.FG_DEFAULT)

        if model_col == self._audit_col:
            if lvl == AUDIT_INFO:
                comp.setForeground(self.FG_INFO)
            elif lvl == AUDIT_OK:
                comp.setForeground(self.FG_OK)
            elif lvl == AUDIT_WARN:
                comp.setForeground(self.FG_WARN)
            elif lvl == AUDIT_ERROR:
                comp.setForeground(self.FG_ERR)
            elif lvl == AUDIT_REDIRECT:
                comp.setForeground(self.FG_REDIR)
        elif model_col == self._status_col and value is not None:
            try:
                code = int("%s" % value)
            except Exception:
                code = 0
            if 200 <= code < 300:
                comp.setForeground(self.FG_OK)
            elif 300 <= code < 400:
                comp.setForeground(self.FG_REDIR)
            elif 400 <= code < 500:
                comp.setForeground(self.FG_INFO)
            elif code >= 500:
                comp.setForeground(self.FG_ERR)
        return comp


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

    def __init__(self, kind, payload, label, audit_level=AUDIT_NONE):
        clean_label = u_text(label)
        self.kind = kind
        self.payload = payload
        self.label = clean_label
        self.audit_level = audit_level
        DefaultMutableTreeNode.__init__(self, clean_label)

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


class HierarchyTreeRenderer(DefaultTreeCellRenderer):
    """
    Custom JTree renderer that guarantees human-readable Vietnamese labels and
    applies color-coding (Yellow INFO, Orange WARN, Green OK, Red ERR) to Folder/API/Role nodes.
    """
    FONT_FOLDER = Font("Dialog", getattr(Font, "BOLD", 1), 12)
    FONT_API = Font("Dialog", getattr(Font, "BOLD", 1), 11)
    FONT_NORMAL = Font("Dialog", getattr(Font, "PLAIN", 0), 11)

    def __init__(self):
        DefaultTreeCellRenderer.__init__(self)

    def getTreeCellRendererComponent(self, tree, value, selected, expanded, leaf, row, hasFocus):
        comp = DefaultTreeCellRenderer.getTreeCellRendererComponent(
            self, tree, value, selected, expanded, leaf, row, hasFocus)
        try:
            kind = getattr(value, "kind", None)
            label = getattr(value, "label", None)
            audit_level = getattr(value, "audit_level", AUDIT_NONE)
            if kind is None and isinstance(value, DefaultMutableTreeNode):
                uobj = value.getUserObject()
                if hasattr(uobj, "label"):
                    kind = getattr(uobj, "kind", None)
                    label = getattr(uobj, "label", None)
                    audit_level = getattr(uobj, "audit_level", AUDIT_NONE)
                elif uobj is not None:
                    label = u_text(uobj)
            if label:
                comp.setText(u_text(label))

            if kind in ("ROOT", "FOLDER"):
                comp.setFont(self.FONT_FOLDER)
            elif kind in ("GROUP", "ORIG"):
                comp.setFont(self.FONT_API)
            else:
                comp.setFont(self.FONT_NORMAL)

            if not selected:
                if audit_level == AUDIT_WARN:
                    bg, fg = AuditTableRenderer.BG_WARN, AuditTableRenderer.FG_WARN
                elif audit_level == AUDIT_INFO:
                    bg, fg = AuditTableRenderer.BG_INFO, AuditTableRenderer.FG_INFO
                elif audit_level == AUDIT_ERROR:
                    bg, fg = AuditTableRenderer.BG_ERR, AuditTableRenderer.FG_ERR
                elif audit_level == AUDIT_OK:
                    bg, fg = AuditTableRenderer.BG_OK, AuditTableRenderer.FG_OK
                elif kind == "ORIG":
                    bg, fg = Color(232, 240, 254), Color(20, 65, 150)
                else:
                    bg, fg = None, AuditTableRenderer.FG_DEFAULT
                if hasattr(self, "setBackgroundNonSelectionColor"):
                    self.setBackgroundNonSelectionColor(bg)
                if hasattr(self, "setTextNonSelectionColor"):
                    self.setTextNonSelectionColor(fg)
                if bg is not None:
                    comp.setBackground(bg)
                comp.setForeground(fg)
        except Exception:
            pass
        return comp


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


# =============================================================================
# Role editor panel & dialog (supports Header, Cookie Key, and JWT/Bearer rules)
# =============================================================================


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
        self.table.setRowHeight(22)
        cm = self.table.getColumnModel()
        cm.getColumn(2).setCellEditor(DefaultCellEditor(JComboBox(HEADER_MODES)))
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
        center.add(JLabel(
            "<html><b>Modes:</b> REPLACE = ghi đè/thêm Header &nbsp;|&nbsp; "
            "ADD = nối thêm dòng Header &nbsp;|&nbsp; "
            "REMOVE (hoặc <b>[REMOVE]</b>) = xóa Header &nbsp;|&nbsp; "
            "<b>COOKIE_SET</b> = thêm/sửa 1 biến trong Cookie &nbsp;|&nbsp; "
            "<b>COOKIE_REMOVE</b> = xóa 1 biến khỏi Cookie</html>"), BorderLayout.SOUTH)
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

        self.config = merge_config(self._load_json_setting(SETTINGS_KEY_CONFIG, {}))
        regex_err = self._recompile_filters(self.config)
        try:
            stored_roles = self._load_json_setting(SETTINGS_KEY_ROLES, None)
            if isinstance(stored_roles, list) and len(stored_roles) > 0:
                self.roles.set_all([normalize_role(r, i) for i, r in enumerate(stored_roles)])
            else:
                self.roles.set_all(default_role_templates())
        except Exception as e:
            callbacks.printError("Could not load stored roles: %s" % e)

        self.capture_executor = Executors.newSingleThreadExecutor()
        self.send_executor = Executors.newFixedThreadPool(self.config["threads"])

        callbacks.registerExtensionStateListener(self)
        SwingUtilities.invokeLater(_Task(self._init_ui, self.log))
        if regex_err:
            self.log("Stored API regex is invalid: %s" % regex_err)

    def _init_ui(self):
        try:
            self._build_ui()
        except Throwable as t:
            tb = traceback.format_exc()
            self.callbacks.printError("Error building UI (Java): %s\n%s" % (t, tb))
            if self.main_panel is None:
                self.main_panel = JPanel(BorderLayout())
            self.main_panel.add(JScrollPane(JTextArea("Error building UI:\n%s\n%s" % (t, tb))), BorderLayout.CENTER)
        except Exception:
            tb = traceback.format_exc()
            self.callbacks.printError("Error building UI:\n%s" % tb)
            if self.main_panel is None:
                self.main_panel = JPanel(BorderLayout())
            self.main_panel.add(JScrollPane(JTextArea("Error building UI:\n%s" % tb)), BorderLayout.CENTER)
        self.callbacks.addSuiteTab(self)
        # Traffic hooks are registered only after the UI exists.
        self.callbacks.registerHttpListener(self)
        self.callbacks.registerContextMenuFactory(self)
        try:
            self.log("%s %s loaded - %d role(s) configured." % (EXT_NAME, EXT_VERSION, self.roles.count()))
            self._refresh_feature_views()
            self.update_status()
        except Throwable as t:
            self.callbacks.printError("Error initializing UI state (Java): %s\n%s" % (t, traceback.format_exc()))
        except Exception:
            self.callbacks.printError("Error initializing UI state:\n%s" % traceback.format_exc())

    def extensionUnloaded(self):
        self._unloaded = True
        try:
            self.capture_executor.shutdownNow()
            self.send_executor.shutdownNow()
            self.capture_executor.awaitTermination(2, TimeUnit.SECONDS)
            self.send_executor.awaitTermination(2, TimeUnit.SECONDS)
        except Throwable:
            pass
        self.callbacks.printOutput("%s unloaded." % EXT_NAME)

    # ------------------------------------------------------------------ ITab
    def getTabCaption(self):
        return EXT_NAME

    def getUiComponent(self):
        return self.main_panel

    # --------------------------------------------------------------- logging
    def log(self, msg):
        line = "[%s] %s" % (time.strftime("%H:%M:%S"), msg)
        try:
            self.callbacks.printOutput(line)
        except Throwable:
            pass

        def append():
            area = self.log_area
            if area is None:
                return
            area.append(line + "\n")
            doc = area.getDocument()
            if doc.getLength() > 300000:
                doc.remove(0, doc.getLength() - 200000)
            area.setCaretPosition(doc.getLength())
        ui_call(append)

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
            targets = ([g.orig_result] + list(g.results)) if include_original else list(g.results)
            self.replay(g, targets)
        if matched:
            self.log("Manual Send Hierarchy '%s': queued %d API group(s)." % (u_text(prefix_path), len(matched)))
        return matched

    def send_hierarchy_prefix_to_repeater(self, prefix_path, groups_override=None, include_original=False,
                                          compact=False, copy_group_name=False):
        """Send all APIs inside a hierarchical group prefix to Burp Repeater."""
        matched = self.groups_for_hierarchy_prefix(prefix_path, groups_override=groups_override)
        for g in matched:
            targets = ([g.orig_result] + list(g.results)) if include_original else list(g.results)
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
            self.config = new_cfg
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
    def _filter_reason(self, cfg, url, method, path):
        """None if the request passes every filter, otherwise the reason it was skipped."""
        if cfg["ignore_options_head"] and method in ("OPTIONS", "HEAD"):
            return "method %s ignored" % method
        if cfg["in_scope_only"] and not self.callbacks.isInScope(url):
            return "out of scope"
        with self._cfg_lock:
            exts = self._static_exts
            rx = self._api_regex
        if cfg["ignore_static"] and is_static_path(path, exts):
            return "static extension"
        if cfg["api_regex_enabled"] and rx is not None and not rx.search(strip_query(path)):
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

        if apply_filters:
            reason = self._filter_reason(cfg, url, method, path)
            if reason:
                with self._state_lock:
                    self._skipped_count += 1
                    self._last_skip_reason = reason
                if source == "Manual":
                    self.log("Skipped %s %s (%s)" % (method, url, reason))
                self.update_status()
                return
            if cfg["dedup"]:
                base_key = dedup_key(method, service.getProtocol(), service.getHost(), service.getPort(),
                                     path, cfg["dedup_normalize_ids"])
                key = ("F%d|%s" % (feat.fid, base_key)) if cfg.get("dedup_per_feature") else base_key
                with self._state_lock:
                    if key in self._seen_keys:
                        self._skipped_count += 1
                        self._last_skip_reason = "dedup"
                        if source == "Manual":
                            self.log("Skipped %s %s (duplicate endpoint)" % (method, url))
                        self.update_status()
                        return
                    self._seen_keys.add(key)

        roles = self.roles.enabled()
        if not roles:
            with self._state_lock:
                self._skipped_count += 1
                self._last_skip_reason = "0 roles"
            self.log("No enabled roles - skipped %s %s" % (method, url))
            self.update_status()
            return

        with self._state_lock:
            gid = self._next_gid
            self._next_gid += 1

        group = ApiGroup(gid, service, method, path, "%s" % url, req, resp, source,
                         feat.fid, feat.name)
        if resp is not None:
            try:
                rinfo = self.helpers.analyzeResponse(resp)
                group.orig_status = rinfo.getStatusCode()
                group.orig_length = len(resp) - rinfo.getBodyOffset()
            except Throwable:
                pass
        group.sync_original_meta(cfg["short_path_len"], cfg.get("include_feature_in_tab", False))
        group.results = self._clone_for_roles(group, info, roles, cfg)
        group.recalc_audit()

        ui_call(lambda: self._add_group_ui(group))
        self.log("%s (%s) [%s]: %s %s -> 1 API gốc + %d role clone(s) [%s]" %
                 (format_api_label(gid), format_group_id(gid),
                  format_feature_label(feat.fid, feat.name),
                  method, url, len(group.results), source))
        if cfg["auto_repeater"]:
            self._dispatch_repeater(group, group.results)
        if cfg["auto_send"]:
            self.replay(group, group.results)

    def _clone_for_roles(self, group, info, roles, cfg):
        """Build exactly one request per enabled role; method/URL/params/body preserved."""
        req = group.orig_request
        base_headers = [u_text(h) for h in info.getHeaders()]
        body = Arrays.copyOfRange(req, info.getBodyOffset(), len(req))
        results = []
        for idx, role in enumerate(roles):
            new_headers = apply_header_rules(base_headers, role["headers"])
            jlist = ArrayList()
            for h in new_headers:
                jlist.add(h)
            new_req = self.helpers.buildHttpMessage(jlist, body)
            display = display_role_name(role["name"], idx, cfg["number_roles_in_tab"])
            res = RoleResult(display, idx, new_req, is_stripped_auth=is_stripped_auth_role(role))
            res.tab_name = repeater_tab_name(group.gid, group.method, group.path, display,
                                             cfg["short_path_len"], group.fid,
                                             cfg.get("include_feature_in_tab", False))
            evaluate_role_result(group, res)
            results.append(res)
        return results

    def rebuild_group(self, group):
        """Re-clone a group's original request with the *current* enabled roles."""
        def work():
            roles = self.roles.enabled()
            if not roles:
                self.log("No enabled roles - cannot rebuild %s" % format_group_id(group.gid))
                return
            cfg = self.get_config()
            info = self.helpers.analyzeRequest(group.service, group.orig_request)
            new_results = self._clone_for_roles(group, info, roles, cfg)

            def apply():
                group.results = new_results
                group.sync_original_meta(cfg["short_path_len"], cfg.get("include_feature_in_tab", False))
                group.recalc_audit()
                self.group_model.refresh_group(group)
                if self.result_model.group() is group:
                    self.result_model.set_group(group)
                    self._select_first_result()
                self._refresh_feature_views()
            ui_call(apply)
            self.log("%s (%s) rebuilt with 1 API gốc + %d current role(s)." %
                     (format_api_label(group.gid), format_group_id(group.gid), len(new_results)))
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
                self.log("Repeater dispatch failed for %s: %s" % (res.tab_name, t))
        if copy_group_name:
            grp_title = "%s %s %s" % (format_group_id(group.gid), group.method,
                                      short_path(group.path, 28))
            self._copy_to_clipboard(grp_title)
            self.log("%s (%s): %d tab gọn đã gửi sang Burp Repeater (Đã copy tên Group '%s' vào Clipboard)." %
                     (format_api_label(group.gid), format_group_id(group.gid), len(results), grp_title))
        else:
            self.log("%s (%s): %d request(s) sent to Repeater." %
                     (format_api_label(group.gid), format_group_id(group.gid), len(results)))

    # ------------------------------------------------------ background replay
    def replay(self, group, results):
        """Queue each result for background sending; never blocks the caller."""
        results = list(results)
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
        for res in results:
            self.send_executor.execute(_Task(
                (lambda r=res: self._send_one(group, r)), self.log))

    def _send_one(self, group, res):
        if self._unloaded:
            return
        throttle = self.config.get("throttle_ms", 0)
        if throttle > 0:
            time.sleep(throttle / 1000.0)
        res.state = STATE_SENDING
        evaluate_role_result(group, res)
        started = time.time()
        try:
            rr = self.callbacks.makeHttpRequest(group.service, res.request)
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
                res.response = resp
                res.status = rinfo.getStatusCode()
                res.length = len(resp) - rinfo.getBodyOffset()
                res.state = STATE_DONE
                res.error = ""
                if getattr(res, "is_original", False):
                    group.orig_response = resp
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
        # Pre-calculate audit on the worker thread so the Swing EDT does 0 heavy work
        group.recalc_audit()
        with self._state_lock:
            self._active_sends = max(0, self._active_sends - 1)
            all_settled = (self._active_sends == 0)
        self._notify_results(group, res, finished_send=all_settled)

    def _notify_results(self, group, res, finished_send=False):
        # Coalesce rapid background updates (~100ms window) so 200 concurrent role
        # responses never flood the Swing Event Dispatch Thread.
        now = time.time()
        with self._state_lock:
            if not finished_send and self._ui_dirty and (now - self._last_ui_flush) < 0.10:
                return
            self._ui_dirty = True
            self._last_ui_flush = now

        def refresh():
            with self._state_lock:
                self._ui_dirty = False
            if self.group_model is None:
                return
            self.group_model.refresh_group(group)
            if self.feature_model is not None and self.feature_table is not None:
                sel_feat = self.feature_table.getSelectedRow()
                self.feature_model.fireTableDataChanged()
                if 0 <= sel_feat < self.feature_model.getRowCount():
                    self.feature_table.setRowSelectionInterval(sel_feat, sel_feat)
            if self.result_model.group() is group:
                self.result_model.fireTableDataChanged()
                self._refresh_grouped_repeater_bar()
                _, sel = self.current_selection()
                if sel is not None and (res is None or sel is res):
                    self._show_result(sel)
            if finished_send:
                self._refresh_feature_views()
            self.update_status()
        ui_call(refresh)

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
        self.tf_feature_name = JTextField(self.active_feature().name, 18,
                                          actionPerformed=self._on_apply_active_feature_name)
        self.tf_feature_name.setToolTipText(
            "Nhập đường dẫn N cấp ngăn cách bởi '>' rồi nhấn Enter (VD: Toppage > menu > button)")

        self.btn_path_menu = JButton("📁 Path / Nhánh ▾",
                                     actionPerformed=lambda e: self._show_path_actions_menu(self.btn_path_menu))
        self.btn_path_menu.setMargin(Insets(2, 8, 2, 8))
        self.btn_path_menu.setFont(Font("Dialog", Font.BOLD, 11))

        self.lbl_feature_counter = JLabel("(0 API)")
        left_header.add(self.cb_capture)
        left_header.add(self.btn_capture_opts)
        left_header.add(JLabel(" | "))
        left_header.add(self.lbl_active_feature)
        left_header.add(self.subfolder_chips_panel)
        left_header.add(self.tf_feature_name)
        left_header.add(self.btn_path_menu)
        left_header.add(self.lbl_feature_counter)

        right_header = JPanel(FlowLayout(FlowLayout.RIGHT, 4, 1))
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
        top_container.add(left_header, BorderLayout.WEST)
        top_container.add(right_header, BorderLayout.EAST)
        self.main_panel.add(top_container, BorderLayout.NORTH)

        self.tabs = JTabbedPane()
        self.tabs.addTab("API Groups & Repeater", self._build_groups_tab())
        self.tabs.addTab("Lịch sử & Báo cáo", self._build_history_tab())
        self.tabs.addTab("Roles (Profiles)", self._build_roles_tab())
        self.tabs.addTab("Cấu hình & Bộ lọc", self._build_settings_tab(cfg))
        self.log_area = JTextArea()
        self.log_area.setEditable(False)
        self.tabs.addTab("Log", JScrollPane(self.log_area))
        self.main_panel.add(self.tabs, BorderLayout.CENTER)
        self.callbacks.customizeUiComponent(self.main_panel)

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
        self.left_hierarchy_tree.setRowHeight(22)
        self.left_hierarchy_tree.setCellRenderer(HierarchyTreeRenderer())
        self.left_hierarchy_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.left_hierarchy_tree.addTreeSelectionListener(_TreeListener(self._on_left_hierarchy_tree_selected))
        self.left_hierarchy_tree.addMouseListener(
            _TreePopupListener(self.left_hierarchy_tree, self._show_left_tree_popup))

        self.feature_model = FeatureTableModel(self)
        self.feature_table = JTable(self.feature_model)
        self.feature_table.setRowHeight(22)
        self.feature_table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.feature_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_feature_filter_selected))
        self.feature_table.addMouseListener(
            _TablePopupListener(self.feature_table, self._show_feature_table_popup))
        feat_renderer = AuditTableRenderer(self.feature_model, status_col=None, audit_col=3)
        for col, width in ((0, 42), (1, 165), (2, 50), (3, 155), (4, 115)):
            column = self.feature_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(feat_renderer)

        left_tabs = JTabbedPane()
        left_tabs.addTab("Cây Sub-folder", JScrollPane(self.left_hierarchy_tree))
        left_tabs.addTab("Bảng Nhánh", JScrollPane(self.feature_table))
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
        self.group_table.setRowHeight(22)
        self.group_table.setAutoCreateRowSorter(True)
        self.group_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.group_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_group_selected))
        self.group_table.addMouseListener(
            _TablePopupListener(self.group_table, self._show_group_table_popup))
        grp_renderer = AuditTableRenderer(self.group_model, status_col=7, audit_col=3)
        for col, width in ((0, 55), (1, 46), (2, 210), (3, 185), (4, 55), (5, 130),
                           (6, 235), (7, 48), (8, 62), (9, 95), (10, 58), (11, 52), (12, 60)):
            column = self.group_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(grp_renderer)
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
        self.result_table.setRowHeight(22)
        self.result_table.setAutoCreateRowSorter(True)
        self.result_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.result_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_result_selected))
        self.result_table.addMouseListener(_DoubleClick(lambda: self._on_send_role(None)))
        self.result_table.addMouseListener(
            _TablePopupListener(self.result_table, self._show_result_table_popup))
        res_renderer = AuditTableRenderer(self.result_model, status_col=4, audit_col=2)
        for col, width in ((0, 52), (1, 185), (2, 210), (3, 80), (4, 55), (5, 75),
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
        top_bar.add(JButton("📄 Export Báo cáo (.txt/.md)...", actionPerformed=self._on_export_history_report))
        top_bar.add(JButton("↻ Refresh", actionPerformed=lambda e: self._refresh_feature_views()))
        panel.add(top_bar, BorderLayout.NORTH)

        root = HierarchyTreeNode("ROOT", "", "Lịch sử Chức năng & API")
        self.history_tree_model = DefaultTreeModel(root)
        self.history_tree = JTree(self.history_tree_model)
        self.history_tree.setRowHeight(22)
        self.history_tree.setCellRenderer(HierarchyTreeRenderer())
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
        self.role_table.setRowHeight(22)
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

        left_panel.add(role_top_bar, BorderLayout.NORTH)
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

    # ---- Settings tab
    def _build_settings_tab(self, cfg):
        panel = JPanel(GridBagLayout())
        panel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10))
        gc = GridBagConstraints()
        gc.insets = Insets(4, 4, 4, 4)
        gc.anchor = GridBagConstraints.WEST
        gc.fill = GridBagConstraints.HORIZONTAL
        row = [0]

        def add_row(left, right=None):
            gc.gridy = row[0]
            gc.gridx = 0
            gc.weightx = 0.0
            gc.gridwidth = 1 if right is not None else 2
            panel.add(left, gc)
            if right is not None:
                gc.gridx = 1
                gc.weightx = 1.0
                panel.add(right, gc)
            row[0] += 1

        on_change = self._on_settings_changed
        self.cb_scope = JCheckBox("In-Scope Only (Target > Scope)", cfg["in_scope_only"], actionPerformed=on_change)
        self.cb_static = JCheckBox("Ignore Static Extensions:", cfg["ignore_static"], actionPerformed=on_change)
        self.tf_static = JTextField(cfg["static_ext"], 60, actionPerformed=on_change)
        self.cb_regex = JCheckBox("API Path Regex (matched against path, no query):", cfg["api_regex_enabled"],
                                  actionPerformed=on_change)
        self.tf_regex = JTextField(cfg["api_regex"], 60, actionPerformed=on_change)
        self.cb_options = JCheckBox("Ignore OPTIONS / HEAD (CORS preflight)", cfg["ignore_options_head"],
                                    actionPerformed=on_change)
        self.cb_dedup = JCheckBox("Deduplicate (Method + Host + Path) - clone each endpoint only once",
                                  cfg["dedup"], actionPerformed=on_change)
        self.cb_dedup_ids = JCheckBox("Dedup: treat numeric / UUID / long-hex path segments as {id}",
                                      cfg["dedup_normalize_ids"], actionPerformed=on_change)
        self.cb_dedup_feature = JCheckBox(
            "Dedup riêng theo từng Chức năng (cho phép bắt lại cùng API khi chuyển sang Tên chức năng mới)",
            cfg.get("dedup_per_feature", False), actionPerformed=on_change)
        self.cb_number = JCheckBox("Prefix role index in tab names (01_, 02_ ...) unless the name already has one",
                                   cfg["number_roles_in_tab"], actionPerformed=on_change)
        self.cb_feat_tab = JCheckBox(
            "Gắn mã Chức năng vào tên tab Repeater ([F01-G01:POST /v1/...] thay vì [G01:POST /v1/...])",
            cfg.get("include_feature_in_tab", False), actionPerformed=on_change)
        self.sp_threads = JSpinner(SpinnerNumberModel(cfg["threads"], 1, 64, 1))
        self.sp_throttle = JSpinner(SpinnerNumberModel(cfg["throttle_ms"], 0, 60000, 50))
        self.sp_pathlen = JSpinner(SpinnerNumberModel(cfg["short_path_len"], 8, 200, 1))
        for sp in (self.sp_threads, self.sp_throttle, self.sp_pathlen):
            sp.addChangeListener(_Change(lambda e: self._on_settings_changed(None)))
        self.regex_error = JLabel(" ")
        self.regex_error.setForeground(Color(200, 0, 0))

        add_row(JLabel("<html><b>Proxy capture filters</b> (manual context-menu cloning bypasses them unless "
                       "you pick the 'apply capture filters' item)</html>"))
        add_row(self.cb_scope)
        add_row(self.cb_static, self.tf_static)
        add_row(self.cb_regex, self.tf_regex)
        add_row(JLabel(""), self.regex_error)
        add_row(self.cb_options)
        add_row(self.cb_dedup)
        add_row(self.cb_dedup_ids)
        add_row(self.cb_dedup_feature)
        add_row(JLabel("<html><br><b>Cloning, Repeater and replay</b></html>"))
        add_row(self.cb_number)
        add_row(self.cb_feat_tab)
        add_row(JLabel("Short path max length in tab names:"), self.sp_pathlen)
        add_row(JLabel("Replay worker threads:"), self.sp_threads)
        add_row(JLabel("Throttle per request (ms):"), self.sp_throttle)
        apply_btn = JButton("Apply Text Fields", actionPerformed=on_change)
        reset_btn = JButton("Restore Defaults", actionPerformed=self._on_restore_defaults)
        btns = JPanel(FlowLayout(FlowLayout.LEFT))
        btns.add(apply_btn)
        btns.add(reset_btn)
        add_row(btns)
        gc.gridy = row[0]
        gc.weighty = 1.0
        panel.add(JPanel(), gc)
        return JScrollPane(panel)

    def _collect_settings(self):
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
            "threads": int(self.sp_threads.getValue()),
            "throttle_ms": int(self.sp_throttle.getValue()),
            "short_path_len": int(self.sp_pathlen.getValue()),
        }

    def _on_top_filter_toggled(self, event):
        if getattr(self, "cb_scope", None) is not None and getattr(self, "cb_top_scope", None) is not None:
            self.cb_scope.setSelected(self.cb_top_scope.isSelected())
        if getattr(self, "cb_regex", None) is not None and getattr(self, "cb_top_regex", None) is not None:
            self.cb_regex.setSelected(self.cb_top_regex.isSelected())
        self._on_settings_changed(event)

    def _on_settings_changed(self, event):
        if getattr(self, "cb_top_scope", None) is not None and getattr(self, "cb_scope", None) is not None:
            self.cb_top_scope.setSelected(self.cb_scope.isSelected())
        if getattr(self, "cb_top_regex", None) is not None and getattr(self, "cb_regex", None) is not None:
            self.cb_top_regex.setSelected(self.cb_regex.isSelected())
        err = self.apply_config(self._collect_settings())
        if err and self.cb_regex.isSelected():
            self.regex_error.setText("Invalid regex - API filter inactive: %s" % err)
        else:
            self.regex_error.setText(" ")

    def _on_restore_defaults(self, event):
        d = merge_config({})
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
        self.sp_threads.setValue(Integer(d["threads"]))
        self.sp_throttle.setValue(Integer(d["throttle_ms"]))
        self.sp_pathlen.setValue(Integer(d["short_path_len"]))
        self._on_settings_changed(None)

    # ---- Dynamic N-Level Sub-Folder Chips & Dropdown Menus
    def _rebuild_subfolder_chips(self, path_text):
        panel = getattr(self, "subfolder_chips_panel", None)
        if panel is None:
            return
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
        menu.add(JMenuItem("▶ Gửi API đang chọn (Tất cả Roles)", actionPerformed=self._on_replay_all))
        menu.add(JMenuItem("▶ Gửi lại Role đang chọn", actionPerformed=self._on_replay_selected))
        menu.add(JMenuItem("▶▶ Gửi toàn bộ Nhánh đang chọn (Đệ quy tất cả cấp con)",
                           actionPerformed=self._on_replay_selected_hierarchy_or_feature))
        menu.addSeparator()
        menu.add(JMenuItem("▶▶ Gửi tất cả API đã bắt (%d API)" % len(self.group_model.all_groups()),
                           actionPerformed=lambda e: [self.replay(g, g.results) for g in self.group_model.all_groups()]))
        menu.show(btn, 0, btn.getHeight())

    def _show_repeater_dropdown_menu(self, btn):
        menu = JPopupMenu()
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
                menu.addSeparator()
                menu.add(JMenuItem("🗑 Xóa Nhánh \"%s\"..." % title,
                                   actionPerformed=self._on_delete_selected_tree_branch))
        elif kind in ("GROUP", "ORIG", "ROLE"):
            g = payload if kind == "GROUP" else payload[0]
            menu.add(JMenuItem("▶ Gửi API #%d (%d Roles)" % (g.gid, len(g.results)),
                               actionPerformed=lambda e: self.replay(g, g.results)))
            menu.add(JMenuItem("📤 Đẩy API #%d sang Burp Repeater (Gọn)" % g.gid,
                               actionPerformed=lambda e: self._dispatch_group_with_selected_mode(g)))
        menu.show(event.getComponent(), event.getX(), event.getY())

    def update_status(self):
        def refresh():
            if self.status_label is None or getattr(self, "btn_replay_all", None) is None:
                return
            cfg = self.get_config()
            all_groups = self.group_model.all_groups() if getattr(self, "group_model", None) is not None else []
            info_apis = len([g for g in all_groups if getattr(g, "_audit_level", None) == AUDIT_INFO])
            feats = self.features_list()
            act = self.active_feature()
            mode_str = "Auto" if cfg.get("auto_send") else "Manual"
            self.status_label.setText(
                "%s | Roles: %d/%d | Nhánh: %d | API: %d (Vàng: %d)"
                % (mode_str, self.roles.enabled_count(), self.roles.count(),
                   len(feats), len(all_groups), info_apis))
            if getattr(self, "lbl_active_feature", None) is not None:
                parts = split_hierarchy_path(act.name)
                self.lbl_active_feature.setText("Path [#%d | %d cấp]:" % (act.fid, len(parts)))
                if not self.tf_feature_name.hasFocus():
                    self.tf_feature_name.setText(act.name)
                self._rebuild_subfolder_chips(act.name)
                act_count = len([x for x in all_groups if x.fid == act.fid])
                self.lbl_feature_counter.setText("(%d API)" % act_count)
            n = self.roles.enabled_count()
            g, _ = self.current_selection()
            count = len(g.results) if g is not None else n
            self.btn_replay_all.setText("▶ Gửi API (%d Roles)" % count)
        ui_call(refresh)

    # ---------------------------------------- feature & history view helpers
    def _refresh_history_summary_only(self):
        if self.history_summary_area is None or self.group_model is None:
            return
        text = build_history_summary_text(self.features_list(), self.group_model.all_groups())
        self.history_summary_area.setText(text)
        self.history_summary_area.setCaretPosition(0)

    def _build_nested_hierarchy_root(self, feats, all_groups, root_label):
        """
        Build a nested HierarchyTreeNode hierarchy where N-level paths like
        'Toppage > menu > sub1 > button "Search"' expand cleanly with human-readable labels:
          📁 [Cấp 1] Toppage (11 API | ...)
            └── 📁 [Cấp 2] menu (11 API | ...)
                  └── 📁 [Cấp 3] button_3 (11 API | ...)
                        └── 📁 [Cấp 4] test (11 API | ...)
                              └── 🌐 API 1 [G01]: GET /path (1 Gốc + 10 Roles)
                                    ├── 📌 [API GỐC] 00_Original (Acc Crawl)
                                    └── 👤 01_Admin .. 10_Guest
        """
        root = HierarchyTreeNode("ROOT", "", root_label, audit_level=AUDIT_NONE)
        folder_nodes = {}  # prefix -> HierarchyTreeNode
        ordered_paths = []
        seen_paths = set()
        for f in feats:
            np = normalize_hierarchy_path(f.name)
            if np not in seen_paths:
                seen_paths.add(np)
                ordered_paths.append(np)
        for g in all_groups:
            np = normalize_hierarchy_path(getattr(g, "feature_name", "") or DEFAULT_HIERARCHY_PATH)
            if np not in seen_paths:
                seen_paths.add(np)
                ordered_paths.append(np)

        def ensure_folder_chain(full_path):
            parts = split_hierarchy_path(full_path)
            parent_node = root
            for idx in range(len(parts)):
                prefix = " > ".join(parts[:idx + 1])
                seg_name = parts[idx]
                node = folder_nodes.get(prefix)
                if node is None:
                    matching_groups = [
                        g for g in all_groups
                        if hierarchy_matches_prefix(getattr(g, "feature_name", ""), prefix)
                    ]
                    folder_lvl, folder_audit = evaluate_feature_audit(matching_groups)
                    label = "[Cấp %d] %s   (%d API | %s)" % (idx + 1, seg_name, len(matching_groups), folder_audit)
                    node = HierarchyTreeNode("FOLDER", prefix, label, audit_level=folder_lvl)
                    folder_nodes[prefix] = node
                    parent_node.add(node)
                parent_node = node
            return parent_node

        for path_str in ordered_paths:
            ensure_folder_chain(path_str)

        for g in all_groups:
            leaf_folder = ensure_folder_chain(getattr(g, "feature_name", "") or DEFAULT_HIERARCHY_PATH)
            g_lvl = getattr(g, "_audit_level", None) or evaluate_group_audit(g)[0]
            g_audit = getattr(g, "_audit_summary", None) or evaluate_group_audit(g)[1]
            g_node = HierarchyTreeNode(
                "GROUP", g,
                "%s [%s]: %s %s  (1 Gốc + %d Roles)  --> [%s]"
                % (format_api_label(g.gid), format_group_id(g.gid), g.method, short_path(g.path, 45),
                   len(g.results), g_audit),
                audit_level=g_lvl
            )
            # 1 API gốc first
            if getattr(g, "orig_result", None) is not None:
                or_res = g.orig_result
                or_lvl = getattr(or_res, "_audit_level", None) or evaluate_role_result(g, or_res)[0]
                or_badge = getattr(or_res, "_audit_badge", None) or evaluate_role_result(g, or_res)[1]
                orig_node = HierarchyTreeNode(
                    "ORIG", (g, or_res),
                    "%s  --> [%s] | Status: %s | Len: %s"
                    % (or_res.role_name, or_badge,
                       or_res.status if or_res.status is not None else "-",
                       or_res.length if or_res.length is not None else "-"),
                    audit_level=or_lvl
                )
                g_node.add(orig_node)
            # N API roles thêm
            for r in g.results:
                r_lvl = getattr(r, "_audit_level", None) or evaluate_role_result(g, r)[0]
                r_badge = getattr(r, "_audit_badge", None) or evaluate_role_result(g, r)[1]
                r_node = HierarchyTreeNode(
                    "ROLE", (g, r),
                    "%s  --> [%s] | Status: %s | Len: %s"
                    % (r.role_name,
                       r_badge,
                       r.status if r.status is not None else r.state,
                       r.length if r.length is not None else "-"),
                    audit_level=r_lvl
                )
                g_node.add(r_node)
            leaf_folder.add(g_node)
        return root, ordered_paths

    @staticmethod
    def _expand_folder_nodes_only(tree, expand_groups=False):
        """
        Expand only FOLDER (and optionally GROUP when small) nodes so JTree never lags
        with O(N^2) row expansions when hundreds of APIs are captured.
        """
        i = 0
        max_rows = 220
        while i < tree.getRowCount() and i < max_rows:
            path = tree.getPathForRow(i)
            if path is not None:
                node = path.getLastPathComponent()
                kind = getattr(node, "kind", None)
                if kind is None and isinstance(node, DefaultMutableTreeNode):
                    kind = getattr(node.getUserObject(), "kind", None)
                if kind in ("ROOT", "FOLDER") or (expand_groups and kind == "GROUP"):
                    tree.expandRow(i)
            i += 1

    def _refresh_feature_views(self):
        def refresh():
            if self.feature_model is not None:
                sel_row = self.feature_table.getSelectedRow()
                self.feature_model.fireTableDataChanged()
                if 0 <= sel_row < self.feature_model.getRowCount():
                    self.feature_table.setRowSelectionInterval(sel_row, sel_row)
                elif self.feature_model.getRowCount() > 0:
                    self.feature_table.setRowSelectionInterval(0, 0)
            if self.group_model is not None:
                all_groups = self.group_model.all_groups()
                feats = self.features_list()
                expand_api_nodes = (len(all_groups) <= 8)
                if getattr(self, "left_hierarchy_tree_model", None) is not None:
                    left_root, ordered_paths = self._build_nested_hierarchy_root(
                        feats, all_groups,
                        "Tất cả Group & API (%d Nhánh | %d API)" % (len(feats), len(all_groups))
                    )
                    self.left_hierarchy_tree_model.setRoot(left_root)
                    self.left_hierarchy_tree_model.reload()
                    self._expand_folder_nodes_only(self.left_hierarchy_tree, expand_groups=expand_api_nodes)
                    if getattr(self, "group_path_editor_combo", None) is not None:
                        self.group_path_editor_combo.removeAllItems()
                        for p in ordered_paths:
                            self.group_path_editor_combo.addItem(p)
                    if getattr(self, "cb_existing_paths", None) is not None:
                        self._updating_path_combos = True
                        try:
                            cur_act = self.active_feature().name
                            self.cb_existing_paths.removeAllItems()
                            for p in ordered_paths:
                                self.cb_existing_paths.addItem(p)
                            self.cb_existing_paths.setSelectedItem(cur_act)
                        finally:
                            self._updating_path_combos = False
                if getattr(self, "history_tree_model", None) is not None:
                    hist_root, _ = self._build_nested_hierarchy_root(
                        feats, all_groups,
                        "Tổng cộng: %d Nhánh Chức năng | %d API đã đi qua" % (len(feats), len(all_groups))
                    )
                    self.history_tree_model.setRoot(hist_root)
                    self.history_tree_model.reload()
                    self._expand_folder_nodes_only(self.history_tree, expand_groups=expand_api_nodes)
            self._refresh_history_summary_only()
        ui_call(refresh)

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
        if getattr(self, "left_hierarchy_tree", None) is None:
            return None, None
        path = self.left_hierarchy_tree.getSelectionPath()
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

    def _on_left_hierarchy_tree_selected(self):
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
        for mr in range(self.group_model.getRowCount()):
            if self.group_model.group_at(mr) is target_group:
                vr = self.group_table.convertRowIndexToView(mr)
                if vr >= 0:
                    self.group_table.setRowSelectionInterval(vr, vr)
                break
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
                self.replay(g, g.results)
            return
        if kind == "FOLDER" and payload:
            sent = self.replay_hierarchy_prefix(payload)
            if not sent:
                JOptionPane.showMessageDialog(
                    self.main_panel, "Nhánh '%s' chưa có API nào để gửi." % payload,
                    EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        if kind == "GROUP" and payload is not None:
            self.replay(payload, payload.results)
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
            targets = interesting if interesting else list(group.results)
            self.send_to_repeater(group, targets, compact=True, copy_group_name=True)
        elif mode_idx == 0:
            # Compact tab names (G01•01_Admin) + copy group title to clipboard
            self.send_to_repeater(group, group.results, compact=True, copy_group_name=True)
        else:
            # Classic full tab names
            self.send_to_repeater(group, group.results, compact=False, copy_group_name=False)

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
        if self.feature_table is None or self.group_model is None:
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
                self.replay(g, g.results)
        elif kind == "GROUP":
            self.replay(payload, payload.results)
        elif kind == "ROLE":
            g, r = payload
            self.replay(g, [r])
        elif kind == "ORIG":
            g, _ = payload
            self.replay(g, g.results)
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
                               actionPerformed=lambda e: self.replay(g, g.results)))
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
        if self.req_viewer is not None:
            edited = self.req_viewer.getMessage()
            if edited is not None and len(edited) > 0:
                res.request = edited
        self.replay(g, [res])

    def _on_inline_repeater_reset_req(self, event):
        g, res = self.current_selection()
        if g is None or res is None:
            return
        if getattr(res, "is_original", False):
            res.request = g.orig_request
            self._show_result(res)
        else:
            self.rebuild_group(g)

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

    def _add_group_ui(self, group):
        self.group_model.add(group)
        if self.group_table.getSelectedRow() < 0 and self.group_model.getRowCount() > 0:
            last = self.group_table.convertRowIndexToView(self.group_model.getRowCount() - 1)
            if last >= 0:
                self.group_table.setRowSelectionInterval(last, last)
        self._refresh_feature_views()
        self.update_status()

    def _on_group_selected(self):
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
        self.req_viewer.setMessage(res.request if res.request is not None else empty, True)
        self.resp_viewer.setMessage(res.response if res.response is not None else empty, False)

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
            self.replay(g, g.results)
            self.log("%s (%s): replaying %d role(s) to server." %
                     (format_api_label(g.gid), format_group_id(g.gid), len(g.results)))

    def _on_replay_selected(self, event):
        g = self._require_group()
        if g is None:
            return
        results = self._selected_results()
        if not results:
            # If user selected only the original row and clicked replay role, replay all roles for convenience
            _, cur_res = self.current_selection()
            if cur_res is not None and getattr(cur_res, "is_original", False):
                self.replay(g, g.results)
                return
            JOptionPane.showMessageDialog(self.main_panel, "Hãy chọn ít nhất 1 dòng Role để gửi.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        self.replay(g, results)
        self.log("%s (%s): replaying %d selected role(s)." %
                 (format_api_label(g.gid), format_group_id(g.gid), len(results)))

    def _on_rebuild(self, event):
        for g in self._selected_groups():
            self.rebuild_group(g)

    def _on_show_original(self, event):
        g = self._require_group()
        if g is None:
            return
        if self.result_model.getRowCount() > 0:
            self.result_table.setRowSelectionInterval(0, 0)
        empty = self.helpers.stringToBytes("")
        self.req_viewer.setMessage(g.orig_request if g.orig_request is not None else empty, True)
        self.resp_viewer.setMessage(g.orig_response if g.orig_response is not None else empty, False)

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
            self._skipped_count = 0
            self._last_skip_reason = ""
            self._next_gid = 1
            self._next_fid = 2
            self._active_fid = 1
            self._features = [FeatureGroup(1, DEFAULT_HIERARCHY_PATH)]
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self._refresh_feature_views()
        self.log("All captured APIs, hierarchy history, and dedup cache reset.")
        self.update_status()

    def _on_reset_dedup(self, event):
        with self._state_lock:
            n = len(self._seen_keys)
            self._seen_keys.clear()
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
        if 0 <= idx < self.roles.count():
            self.inline_role_editor.load_role(self.roles.get(idx))
        else:
            self.inline_role_editor.load_role(None)

    def _on_save_inline_role(self, updated_role):
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
        self.roles.set_all_enabled(enabled)
        self._roles_changed(self.role_table.getSelectedRow())

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
