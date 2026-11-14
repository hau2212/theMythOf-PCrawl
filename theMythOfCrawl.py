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
                      Insets, Dimension, Color, Font)
from java.awt.event import MouseAdapter
from java.lang import Runnable, Boolean, Integer, String, Throwable
from java.util import ArrayList, Arrays
from java.util.concurrent import Executors, TimeUnit
from java.io import File
from java.nio.file import Files
from javax.swing import (JPanel, JLabel, JButton, JCheckBox, JTextField, JTable, JScrollPane,
                         JSplitPane, JTabbedPane, JTextArea, JMenuItem, JOptionPane, JFileChooser,
                         JDialog, JComboBox, JSpinner, SpinnerNumberModel, ListSelectionModel,
                         SwingUtilities, BorderFactory, DefaultCellEditor, BoxLayout, Box, JTree)
from javax.swing.event import ListSelectionListener, TreeSelectionListener
from javax.swing.table import AbstractTableModel, DefaultTableCellRenderer
from javax.swing.tree import DefaultMutableTreeNode, DefaultTreeModel, TreeSelectionModel
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
EXT_VERSION = "1.2.0"
SETTINGS_KEY_ROLES = "tmoc.roles.v1"
SETTINGS_KEY_CONFIG = "tmoc.config.v1"

REMOVE_TOKEN = "[REMOVE]"
MODE_REPLACE = "REPLACE"              # overwrite first occurrence (drop duplicates) or add if missing
MODE_ADD = "ADD"                      # always append a new header line (allows duplicates)
MODE_REMOVE = "REMOVE"                # strip every occurrence of the header
MODE_COOKIE_SET = "COOKIE_SET"        # set/replace a single cookie key=value inside Cookie header
MODE_COOKIE_REMOVE = "COOKIE_REMOVE"  # remove a single cookie key from Cookie header
HEADER_MODES = [MODE_REPLACE, MODE_ADD, MODE_REMOVE, MODE_COOKIE_SET, MODE_COOKIE_REMOVE]

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
    ("Chưa Replay (Pending)", AUDIT_NONE),
]

DEFAULT_STATIC_EXT = ("js,mjs,css,map,png,jpg,jpeg,gif,bmp,ico,svg,webp,avif,tif,tiff,"
                      "woff,woff2,ttf,otf,eot,mp3,mp4,m4a,webm,wav,ogg,avi,mov,flv,swf")
DEFAULT_API_REGEX = r"(?i)(/api/|/v[0-9]+(/|$)|/graphql|/rest/|/rpc/|/services?/|\.json$)"

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
    "auto_repeater": True,
    "auto_send": False,
    "number_roles_in_tab": True,
    "include_feature_in_tab": False,
    "threads": 5,
    "throttle_ms": 0,
    "short_path_len": 40,
}

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
    Returns (audit_level, badge_text).
    """
    if res is None:
        return AUDIT_NONE, "-"
    if res.state == STATE_ERROR:
        err_msg = u_text(res.error or "Timeout / Connection Error")
        if len(err_msg) > 34:
            err_msg = err_msg[:31] + "..."
        return AUDIT_INFO, "INFO: Lỗi gọi API (%s)" % err_msg
    if res.status is None:
        return AUDIT_NONE, u_text(res.state)
    code = int(res.status)
    if code == 401:
        return AUDIT_INFO, "INFO: Chưa xác thực (401)"
    if code == 403:
        return AUDIT_INFO, "INFO: Không đủ quyền (403)"
    if 400 <= code < 500:
        return AUDIT_INFO, "INFO: Role gọi lỗi (%d)" % code
    if code >= 500:
        return AUDIT_INFO, "INFO: Lỗi Server (%d)" % code
    if 300 <= code < 400:
        return AUDIT_REDIRECT, "INFO: Chuyển hướng (%d)" % code
    if 200 <= code < 300:
        # Check if Guest/stripped-auth role got 2xx while another role in the same group was denied (401/403)
        results = getattr(group, "results", []) if group is not None else []
        any_denied = any(r.status in (401, 403) for r in results if r is not res and r.status is not None)
        if getattr(res, "is_stripped_auth", False) and any_denied:
            return AUDIT_WARN, "WARN: Guest trả về %d!" % code
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
            return AUDIT_INFO, "INFO: 2xx lệch Body (%+dB)" % delta
        return AUDIT_OK, "OK: Thành công (%d)" % code
    return AUDIT_INFO, "INFO: Status %d" % code


def evaluate_group_audit(group):
    """
    Evaluate all role results of an API Group to determine its row highlight color and summary:
      - If ANY role in the API failed (401/403/4xx/5xx/STATE_ERROR) or roles differ in status/length
        -> returns (AUDIT_INFO, "INFO: ...") for Yellow Info highlighting.
      - If a stripped-auth / Guest role got 2xx while another role got 401/403 -> also notes "[Guest 2xx!]".
      - If all replayed roles succeeded with 2xx -> returns (AUDIT_OK, "OK: ...").
      - If not replayed yet -> returns (AUDIT_NONE, "Chưa Replay").
    """
    if group is None or not getattr(group, "results", None):
        return AUDIT_NONE, "Chưa có Role"
    done = [r for r in group.results if r.status is not None or r.state == STATE_ERROR]
    if not done:
        return AUDIT_NONE, "Chưa Replay (%d role)" % len(group.results)
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
            return AUDIT_INFO, "INFO: %d OK / %d Lỗi (%s)" % (len(ok_list), len(err_list), codes_str)
        return AUDIT_INFO, "INFO: Cả %d Role lỗi (%s)" % (len(err_list), codes_str)

    if ok_list:
        lengths = set([r.length for r in ok_list if r.length is not None])
        if redir_list:
            return AUDIT_INFO, "INFO: %d OK / %d Redirect (3xx)" % (len(ok_list), len(redir_list))
        if len(lengths) > 1:
            return AUDIT_INFO, "INFO: Cả %d Role 2xx (Lệch Body)" % len(ok_list)
        return AUDIT_OK, "OK: Cả %d Role 2xx" % len(ok_list)

    if redir_list:
        return AUDIT_REDIRECT, "INFO: %d Role Redirect (3xx)" % len(redir_list)
    return AUDIT_NONE, "Đang xử lý"


def evaluate_feature_audit(feature_groups):
    """Summarize the audit status across all API groups belonging to a Feature."""
    f_groups = list(feature_groups or [])
    if not f_groups:
        return AUDIT_NONE, "-"
    info_count = 0
    ok_count = 0
    for g in f_groups:
        lvl, _ = evaluate_group_audit(g)
        if lvl in (AUDIT_INFO, AUDIT_WARN, AUDIT_ERROR):
            info_count += 1
        elif lvl == AUDIT_OK:
            ok_count += 1
    if info_count > 0:
        return AUDIT_INFO, "INFO: %d/%d API có Role lỗi/lệch" % (info_count, len(f_groups))
    if ok_count > 0:
        return AUDIT_OK, "OK: %d/%d API 2xx" % (ok_count, len(f_groups))
    return AUDIT_NONE, "Chưa Replay"


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
    """Represents a user-named feature / button click batch (e.g. Tên 1, Tên 2)."""

    def __init__(self, fid, name="", created=None):
        self.fid = fid
        clean = u_text(name).strip()
        self.name = clean if clean else ("Chức năng %d" % fid)
        self.created = created or time.strftime("%H:%M:%S")

    def label(self):
        return format_feature_label(self.fid, self.name)


class RoleResult(object):
    def __init__(self, role_name, role_index, request_bytes, is_stripped_auth=False):
        self.role_name = u_text(role_name)
        self.role_index = role_index
        self.request = request_bytes
        self.is_stripped_auth = bool(is_stripped_auth)
        self.response = None
        self.status = None
        self.length = None
        self.elapsed_ms = None
        self.state = STATE_NOT_SENT
        self.error = ""
        self.sent_count = 0
        self.tab_name = ""


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
        self.results = []

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
    COLS = ["API #", "Group", "Chức năng", "Đánh giá / Màu (Info)", "Method", "Host", "Path",
            "Orig", "Orig Len", "Roles", "Replayed", "Source", "Time"]

    def __init__(self):
        self._all_rows = []
        self._rows = []
        self._filter_fid = None
        self._filter_audit = AUDIT_FILTER_ALL

    def _matches(self, g):
        if self._filter_fid is not None and g.fid != self._filter_fid:
            return False
        if self._filter_audit and self._filter_audit != AUDIT_FILTER_ALL:
            lvl, _ = evaluate_group_audit(g)
            if self._filter_audit == AUDIT_ERROR:
                return any(r.state == STATE_ERROR or (r.status is not None and r.status >= 500)
                           for r in g.results)
            if self._filter_audit == AUDIT_WARN:
                return any(evaluate_role_result(g, r)[0] == AUDIT_WARN for r in g.results)
            if lvl != self._filter_audit:
                return False
        return True

    def _rebuild_view(self):
        self._rows = [g for g in self._all_rows if self._matches(g)]

    def set_feature_filter(self, fid):
        self._filter_fid = fid
        self._rebuild_view()
        self.fireTableDataChanged()

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
        lvl, _ = evaluate_group_audit(g)
        return lvl

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

    def refresh_group(self, group):
        self._rebuild_view()
        for i, g in enumerate(self._rows):
            if g is group:
                self.fireTableRowsUpdated(i, i)
                return
        self.fireTableDataChanged()

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (7, 8, 9):
            return Integer
        return String

    def getValueAt(self, r, c):
        g = self._rows[r]
        if c == 0:
            return format_api_label(g.gid)
        if c == 1:
            return format_group_id(g.gid)
        if c == 2:
            return format_feature_label(g.fid, g.feature_name)
        if c == 3:
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
            return Integer(len(g.results))
        if c == 10:
            done = len([x for x in g.results if x.state in (STATE_DONE, STATE_ERROR)])
            return "%d/%d" % (done, len(g.results))
        if c == 11:
            return g.source
        if c == 12:
            return g.created
        return ""


class ResultTableModel(AbstractTableModel):
    COLS = ["#", "Role", "Đánh giá Role (Màu)", "State", "Status", "Body Len",
            "Delta vs Orig", "Time (ms)", "Sends", "Repeater Tab / Error"]

    def __init__(self):
        self._group = None

    def set_group(self, group):
        self._group = group
        self.fireTableDataChanged()

    def group(self):
        return self._group

    def result_at(self, r):
        if self._group is not None and 0 <= r < len(self._group.results):
            return self._group.results[r]
        return None

    def audit_level_at(self, r):
        res = self.result_at(r)
        if res is None:
            return AUDIT_NONE
        lvl, _ = evaluate_role_result(self._group, res)
        return lvl

    def getRowCount(self):
        return len(self._group.results) if self._group is not None else 0

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (0, 4, 5, 6, 7, 8):
            return Integer
        return String

    def getValueAt(self, r, c):
        g = self._group
        res = g.results[r]
        if c == 0:
            return Integer(r + 1)
        if c == 1:
            return res.role_name
        if c == 2:
            _, badge = evaluate_role_result(g, res)
            return badge
        if c == 3:
            return res.state
        if c == 4:
            return None if res.status is None else Integer(res.status)
        if c == 5:
            return None if res.length is None else Integer(res.length)
        if c == 6:
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


class _TreeNodeItem(object):
    """User object for DefaultMutableTreeNode that renders a readable label in JTree."""

    def __init__(self, kind, payload, label):
        self.kind = kind
        self.payload = payload
        self.label = label

    def __str__(self):
        return self.label

    def toString(self):
        return self.label


class _DoubleClick(MouseAdapter):
    def __init__(self, fn):
        self._fn = fn

    def mouseClicked(self, event):
        if event.getClickCount() == 2 and SwingUtilities.isLeftMouseButton(event):
            self._fn()


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
        self._features = [FeatureGroup(1, "Chức năng 1")]
        self._seen_keys = set()
        self._unloaded = False
        self._api_regex = None
        self._static_exts = set()
        self.log_area = None
        self.main_panel = None
        self.status_label = None
        self.feature_model = None
        self.group_model = None
        self.result_model = None
        self.history_tree = None
        self.history_tree_model = None
        self.history_summary_area = None
        self.inline_role_editor = None
        self._updating_feature_bar = False

        self.config = merge_config(self._load_json_setting(SETTINGS_KEY_CONFIG, {}))
        regex_err = self._recompile_filters(self.config)
        try:
            stored_roles = self._load_json_setting(SETTINGS_KEY_ROLES, None)
            if isinstance(stored_roles, list):
                self.roles.set_all([normalize_role(r, i) for i, r in enumerate(stored_roles)])
        except Exception as e:
            callbacks.printError("Could not load stored roles: %s" % e)

        self.capture_executor = Executors.newSingleThreadExecutor()
        self.send_executor = Executors.newFixedThreadPool(self.config["threads"])

        callbacks.registerExtensionStateListener(self)
        SwingUtilities.invokeLater(_Task(self._init_ui, self.log))
        if regex_err:
            self.log("Stored API regex is invalid: %s" % regex_err)

    def _init_ui(self):
        self._build_ui()
        self.callbacks.addSuiteTab(self)
        # Traffic hooks are registered only after the UI exists.
        self.callbacks.registerHttpListener(self)
        self.callbacks.registerContextMenuFactory(self)
        self.log("%s %s loaded - %d role(s) configured." % (EXT_NAME, EXT_VERSION, self.roles.count()))
        self._refresh_feature_views()
        self.update_status()

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
            clean = ("%s" % (name or "")).strip() or ("Chức năng %d" % fid)
            feat = FeatureGroup(fid, clean)
            self._features.append(feat)
            self._active_fid = fid
        self.log("Chuyển sang %s - các API tiếp theo sẽ được gom vào chức năng này."
                 % format_feature_label(feat.fid, feat.name))
        self._refresh_feature_views()
        self.update_status()
        return feat

    def rename_feature(self, fid, new_name):
        clean = ("%s" % (new_name or "")).strip() or ("Chức năng %d" % fid)
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
            for r in g.results:
                r.tab_name = repeater_tab_name(g.gid, g.method, g.path, r.role_name,
                                               cfg["short_path_len"], g.fid, cfg["include_feature_in_tab"])
        if self.group_model is not None:
            self.group_model._rebuild_view()
            self.group_model.fireTableDataChanged()
        self._refresh_feature_views()
        self.update_status()

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
        # Capture on the response: the final (post-intercept) request and the
        # original response are both available. Only copies bytes here.
        if self._unloaded or messageIsRequest or toolFlag != self.callbacks.TOOL_PROXY:
            return
        if not self.get_config()["capture_enabled"]:
            return
        try:
            req = messageInfo.getRequest()
            if req is None:
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
                    next_num = len(self.features_list()) + 1
                    name = JOptionPane.showInputDialog(
                        self.main_panel,
                        "Nhập tên cho Chức năng mới (Tên %d):" % next_num,
                        "Chức năng %d" % next_num)
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
        items.add(JMenuItem("%s: Clone to NEW Feature (Tạo Tên chức năng mới...) (%d message(s))"
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
                if source == "Manual":
                    self.log("Skipped %s %s (%s)" % (method, url, reason))
                return
            if cfg["dedup"]:
                base_key = dedup_key(method, service.getProtocol(), service.getHost(), service.getPort(),
                                     path, cfg["dedup_normalize_ids"])
                key = ("F%d|%s" % (feat.fid, base_key)) if cfg.get("dedup_per_feature") else base_key
                with self._state_lock:
                    if key in self._seen_keys:
                        if source == "Manual":
                            self.log("Skipped %s %s (duplicate endpoint)" % (method, url))
                        return
                    self._seen_keys.add(key)

        roles = self.roles.enabled()
        if not roles:
            self.log("No enabled roles - skipped %s %s" % (method, url))
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
        group.results = self._clone_for_roles(group, info, roles, cfg)

        ui_call(lambda: self._add_group_ui(group))
        self.log("%s (%s) [%s]: %s %s -> %d role clone(s) [%s]" %
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
            results.append(res)
        return results

    def rebuild_group(self, group):
        """Re-clone a group's original request with the *current* enabled roles."""
        def work():
            roles = self.roles.enabled()
            if not roles:
                self.log("No enabled roles - cannot rebuild %s" % format_group_id(group.gid))
                return
            info = self.helpers.analyzeRequest(group.service, group.orig_request)
            new_results = self._clone_for_roles(group, info, roles, self.get_config())

            def apply():
                group.results = new_results
                self.group_model.refresh_group(group)
                if self.result_model.group() is group:
                    self.result_model.set_group(group)
                    self._select_first_result()
                self._refresh_feature_views()
            ui_call(apply)
            self.log("%s (%s) rebuilt with %d current role(s)." %
                     (format_api_label(group.gid), format_group_id(group.gid), len(new_results)))
        self.capture_executor.execute(_Task(work, self.log))

    # -------------------------------------------------------------- Repeater
    def send_to_repeater(self, group, results):
        """Public entry (EDT-safe): dispatch off the EDT, preserving order."""
        results = list(results)
        self.capture_executor.execute(_Task(lambda: self._dispatch_repeater(group, results), self.log))

    def _dispatch_repeater(self, group, results):
        for res in results:
            try:
                self.callbacks.sendToRepeater(group.host, group.port, group.use_https(),
                                              res.request, res.tab_name)
            except Throwable as t:
                self.log("Repeater dispatch failed for %s: %s" % (res.tab_name, t))
        self.log("%s (%s): %d request(s) sent to Repeater." %
                 (format_api_label(group.gid), format_group_id(group.gid), len(results)))

    # ------------------------------------------------------ background replay
    def replay(self, group, results):
        """Queue each result for background sending; never blocks the caller."""
        results = list(results)
        for res in results:
            res.state = STATE_QUEUED
            res.error = ""
        self._notify_results(group, None)
        for res in results:
            self.send_executor.execute(_Task(
                (lambda r=res: self._send_one(group, r)), self.log))

    def _send_one(self, group, res):
        if self._unloaded:
            return
        throttle = self.get_config()["throttle_ms"]
        if throttle > 0:
            time.sleep(throttle / 1000.0)
        res.state = STATE_SENDING
        self._notify_results(group, res)
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
        except Throwable as t:
            res.elapsed_ms = int((time.time() - started) * 1000)
            res.state = STATE_ERROR
            res.error = "%s" % t
        except Exception as e:
            res.elapsed_ms = int((time.time() - started) * 1000)
            res.state = STATE_ERROR
            res.error = "%s" % e
        self._notify_results(group, res)

    def _notify_results(self, group, res):
        def refresh():
            if self.group_model is None:
                return
            self.group_model.refresh_group(group)
            if self.feature_model is not None and self.feature_table is not None:
                sel_feat = self.feature_table.getSelectedRow()
                self.feature_model.fireTableDataChanged()
                if 0 <= sel_feat < self.feature_model.getRowCount():
                    self.feature_table.setRowSelectionInterval(sel_feat, sel_feat)
            if self.result_model.group() is group:
                if res is None:
                    self.result_model.fireTableRowsUpdated(0, max(len(group.results) - 1, 0))
                else:
                    for i, r in enumerate(group.results):
                        if r is res:
                            self.result_model.fireTableRowsUpdated(i, i)
                            break
                _, sel = self.current_selection()
                if sel is not None and (res is None or sel is res):
                    self._show_result(sel)
            if self.history_summary_area is not None:
                self._refresh_history_summary_only()
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

        # ---- top control bar (capture toggles + Active Feature switcher + Color Legend)
        top_container = JPanel(BorderLayout())
        bar1 = JPanel(FlowLayout(FlowLayout.LEFT, 8, 3))
        self.cb_capture = JCheckBox("Capture Proxy traffic", cfg["capture_enabled"],
                                    actionPerformed=self._on_settings_changed)
        self.cb_auto_repeater = JCheckBox("Auto-send new groups to Repeater", cfg["auto_repeater"],
                                          actionPerformed=self._on_settings_changed)
        self.cb_auto_send = JCheckBox("Auto-Send to Server & Record", cfg["auto_send"],
                                      actionPerformed=self._on_settings_changed)
        self.status_label = JLabel("")
        for comp in (self.cb_capture, self.cb_auto_repeater, self.cb_auto_send):
            bar1.add(comp)
        bar1.add(Box.createHorizontalStrut(12))
        bar1.add(self.status_label)

        bar2 = JPanel(FlowLayout(FlowLayout.LEFT, 6, 3))
        bar2.setBorder(BorderFactory.createTitledBorder(
            "Bộ gom Chức năng (Feature / Button Action Batching) & Chú thích Màu Audit"))
        self.lbl_active_feature = JLabel("Đang bắt vào Tên 1:")
        self.lbl_active_feature.setFont(Font("Dialog", Font.BOLD, 12))
        self.tf_feature_name = JTextField(self.active_feature().name, 18,
                                          actionPerformed=self._on_apply_active_feature_name)
        btn_rename_feat = JButton("Cập nhật Tên", actionPerformed=self._on_apply_active_feature_name)
        btn_next_feat = JButton("+ Qua Chức Năng Mới (Nút tiếp theo -> Tên mới)",
                                actionPerformed=self._on_next_feature)
        self.lbl_feature_counter = JLabel("")
        bar2.add(self.lbl_active_feature)
        bar2.add(self.tf_feature_name)
        bar2.add(btn_rename_feat)
        bar2.add(btn_next_feat)
        bar2.add(Box.createHorizontalStrut(6))
        bar2.add(self.lbl_feature_counter)
        bar2.add(Box.createHorizontalStrut(12))
        bar2.add(self._make_color_badge("Vàng INFO: Có Role lỗi / Lệch quyền",
                                        AuditTableRenderer.BG_INFO, AuditTableRenderer.FG_INFO))
        bar2.add(self._make_color_badge("Cam WARN: Nghi vấn Bypass",
                                        AuditTableRenderer.BG_WARN, AuditTableRenderer.FG_WARN))
        bar2.add(self._make_color_badge("Xanh OK: Cả N Role 2xx",
                                        AuditTableRenderer.BG_OK, AuditTableRenderer.FG_OK))
        bar2.add(self._make_color_badge("Đỏ ERR: Lỗi 5xx / Mạng",
                                        AuditTableRenderer.BG_ERR, AuditTableRenderer.FG_ERR))

        top_container.add(bar1, BorderLayout.NORTH)
        top_container.add(bar2, BorderLayout.CENTER)
        self.main_panel.add(top_container, BorderLayout.NORTH)

        self.tabs = JTabbedPane()
        self.tabs.addTab("API Groups (Master-Detail)", self._build_groups_tab())
        self.tabs.addTab("History & Features (Lịch sử Chức năng & API)", self._build_history_tab())
        self.tabs.addTab("Roles (Profiles)", self._build_roles_tab())
        self.tabs.addTab("Capture Filters & Options", self._build_settings_tab(cfg))
        self.log_area = JTextArea()
        self.log_area.setEditable(False)
        self.tabs.addTab("Log", JScrollPane(self.log_area))
        self.main_panel.add(self.tabs, BorderLayout.CENTER)
        self.callbacks.customizeUiComponent(self.main_panel)

    # ---- API Groups tab (Feature table + API Group table + Role results + Viewers)
    def _build_groups_tab(self):
        panel = JPanel(BorderLayout())

        # Two-row compact toolbar so no buttons are ever cut off on any screen width
        actions_container = JPanel(GridLayout(2, 1, 0, 1))
        row1 = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        self.btn_send_group = JButton("Send Entire Group to Repeater", actionPerformed=self._on_send_group)
        self.btn_send_role = JButton("Send Selected Role to Repeater", actionPerformed=self._on_send_role)
        self.btn_replay_all = JButton("Replay All Roles to Server", actionPerformed=self._on_replay_all)
        self.btn_replay_sel = JButton("Replay Selected Role(s)", actionPerformed=self._on_replay_selected)
        row1.add(self.btn_send_group)
        row1.add(self.btn_send_role)
        row1.add(self.btn_replay_all)
        row1.add(self.btn_replay_sel)
        row1.add(JButton("Show Original Req/Resp", actionPerformed=self._on_show_original))
        row1.add(JButton("Rebuild with Current Roles", actionPerformed=self._on_rebuild))

        row2 = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        row2.add(JLabel("Lọc màu Audit:"))
        self.cb_audit_filter = JComboBox([label for label, _ in AUDIT_FILTER_OPTIONS])
        self.cb_audit_filter.addActionListener(self._on_audit_filter_changed)
        row2.add(self.cb_audit_filter)
        row2.add(Box.createHorizontalStrut(6))
        row2.add(JButton("Chuyển API -> Chức năng...", actionPerformed=self._on_move_groups_feature))
        row2.add(JButton("Export Matrix JSON...", actionPerformed=self._on_export_matrix))
        row2.add(JButton("Delete Group(s)", actionPerformed=self._on_delete_groups))
        row2.add(JButton("Clear All", actionPerformed=self._on_clear_groups))
        row2.add(JButton("Reset Dedup Cache", actionPerformed=self._on_reset_dedup))

        actions_container.add(row1)
        actions_container.add(row2)
        panel.add(actions_container, BorderLayout.NORTH)

        # Left side of top master area: Feature (Chức năng) selector & batch actions
        self.feature_model = FeatureTableModel(self)
        self.feature_table = JTable(self.feature_model)
        self.feature_table.setRowHeight(22)
        self.feature_table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        self.feature_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_feature_filter_selected))
        feat_renderer = AuditTableRenderer(self.feature_model, status_col=None, audit_col=3)
        for col, width in ((0, 42), (1, 165), (2, 50), (3, 155), (4, 115)):
            column = self.feature_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(feat_renderer)

        feat_panel = JPanel(BorderLayout(2, 2))
        feat_panel.setBorder(BorderFactory.createTitledBorder(
            "Danh sách Chức năng (Click lọc API | Double-click cột Tên để sửa)"))
        feat_panel.add(JScrollPane(self.feature_table), BorderLayout.CENTER)
        feat_btns = JPanel(GridLayout(2, 3, 3, 3))
        feat_btns.add(JButton("+ Chức năng mới", actionPerformed=self._on_next_feature))
        feat_btns.add(JButton("Đặt đang bắt", actionPerformed=self._on_set_selected_feature_active))
        feat_btns.add(JButton("Đổi tên...", actionPerformed=self._on_rename_selected_feature))
        feat_btns.add(JButton("Gửi -> Repeater", actionPerformed=self._on_send_feature_repeater))
        feat_btns.add(JButton("Replay Chức năng", actionPerformed=self._on_replay_feature))
        feat_btns.add(JButton("Xem tất cả API", actionPerformed=self._on_show_all_features))
        feat_panel.add(feat_btns, BorderLayout.SOUTH)

        # Right side of top master area: Sequentially numbered API Groups table
        self.group_model = GroupTableModel()
        self.group_table = JTable(self.group_model)
        self.group_table.setRowHeight(22)
        self.group_table.setAutoCreateRowSorter(True)
        self.group_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.group_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_group_selected))
        self.group_table.addMouseListener(_DoubleClick(lambda: self._on_send_group(None)))
        grp_renderer = AuditTableRenderer(self.group_model, status_col=7, audit_col=3)
        for col, width in ((0, 58), (1, 48), (2, 135), (3, 195), (4, 58), (5, 140),
                           (6, 260), (7, 52), (8, 65), (9, 50), (10, 62), (11, 55), (12, 62)):
            column = self.group_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(grp_renderer)

        group_panel = JPanel(BorderLayout())
        group_panel.setBorder(BorderFactory.createTitledBorder(
            "Danh sách API đã đi qua (API 1, API 2... | Tô màu Vàng INFO khi có bất kỳ Role nào gọi lỗi / lệch quyền)"))
        group_panel.add(JScrollPane(self.group_table), BorderLayout.CENTER)

        top_master_split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, feat_panel, group_panel)
        top_master_split.setResizeWeight(0.30)

        # Bottom detail area: Role results table + Request/Response viewers
        self.result_model = ResultTableModel()
        self.result_table = JTable(self.result_model)
        self.result_table.setRowHeight(22)
        self.result_table.setAutoCreateRowSorter(True)
        self.result_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.result_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_result_selected))
        self.result_table.addMouseListener(_DoubleClick(lambda: self._on_send_role(None)))
        res_renderer = AuditTableRenderer(self.result_model, status_col=4, audit_col=2)
        for col, width in ((0, 35), (1, 145), (2, 210), (3, 70), (4, 55), (5, 75),
                           (6, 85), (7, 70), (8, 50), (9, 360)):
            column = self.result_table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(res_renderer)

        res_panel = JPanel(BorderLayout())
        res_panel.setBorder(BorderFactory.createTitledBorder(
            "Kết quả chi tiết từng Role trên API đang chọn (Màu Vàng INFO = Role bị chặn 401/403/4xx/5xx hoặc lệch Body)"))
        res_panel.add(JScrollPane(self.result_table), BorderLayout.CENTER)

        controller = _EditorController(self)
        self.req_viewer = self.callbacks.createMessageEditor(controller, False)
        self.resp_viewer = self.callbacks.createMessageEditor(controller, False)
        req_panel = JPanel(BorderLayout())
        req_panel.add(JLabel(" Role Request"), BorderLayout.NORTH)
        req_panel.add(self.req_viewer.getComponent(), BorderLayout.CENTER)
        resp_panel = JPanel(BorderLayout())
        resp_panel.add(JLabel(" Role Response"), BorderLayout.NORTH)
        resp_panel.add(self.resp_viewer.getComponent(), BorderLayout.CENTER)
        viewers = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, req_panel, resp_panel)
        viewers.setResizeWeight(0.5)

        detail_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, res_panel, viewers)
        detail_split.setResizeWeight(0.38)
        master_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, top_master_split, detail_split)
        master_split.setResizeWeight(0.40)
        panel.add(master_split, BorderLayout.CENTER)
        return panel

    # ---- History & Features tab (Tree view + formatted audit report)
    def _build_history_tab(self):
        panel = JPanel(BorderLayout(6, 6))
        top_bar = JPanel(FlowLayout(FlowLayout.LEFT, 6, 4))
        top_bar.add(JButton("+ Tạo Chức năng mới (Next Button)", actionPerformed=self._on_next_feature))
        top_bar.add(JButton("Đổi tên Chức năng đang chọn...", actionPerformed=self._on_rename_tree_feature))
        top_bar.add(JButton("Gửi mục đang chọn -> Repeater", actionPerformed=self._on_send_tree_repeater))
        top_bar.add(JButton("Replay mục đang chọn", actionPerformed=self._on_replay_tree_selection))
        top_bar.add(JButton("Xem trong tab API Groups", actionPerformed=self._on_jump_to_group_from_tree))
        top_bar.add(JButton("Export Báo cáo Lịch sử (.txt/.md)...", actionPerformed=self._on_export_history_report))
        top_bar.add(JButton("Refresh", actionPerformed=lambda e: self._refresh_feature_views()))
        panel.add(top_bar, BorderLayout.NORTH)

        root = DefaultMutableTreeNode("Lịch sử Chức năng & API")
        self.history_tree_model = DefaultTreeModel(root)
        self.history_tree = JTree(self.history_tree_model)
        self.history_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION)
        self.history_tree.addTreeSelectionListener(_TreeListener(self._on_history_tree_selected))

        tree_panel = JPanel(BorderLayout())
        tree_panel.setBorder(BorderFactory.createTitledBorder(
            "Cây Chức năng (Tên 1 -> API 1, API 2... | Tên 2 -> API 3, API 4...)"))
        tree_panel.add(JScrollPane(self.history_tree), BorderLayout.CENTER)

        self.history_summary_area = JTextArea()
        self.history_summary_area.setEditable(False)
        self.history_summary_area.setFont(Font("Monospaced", Font.PLAIN, 12))
        summary_panel = JPanel(BorderLayout())
        summary_panel.setBorder(BorderFactory.createTitledBorder(
            "Bản tổng hợp Audit (Tổng số Chức năng, danh sách API theo thứ tự & kết quả các Role)"))
        summary_panel.add(JScrollPane(self.history_summary_area), BorderLayout.CENTER)

        split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, tree_panel, summary_panel)
        split.setResizeWeight(0.42)
        panel.add(split, BorderLayout.CENTER)
        return panel

    # ---- Roles tab (Role table on left + Inline full RoleEditorPanel on right)
    def _build_roles_tab(self):
        panel = JPanel(BorderLayout(6, 6))
        self.role_model = RoleTableModel(self)
        self.role_table = JTable(self.role_model)
        self.role_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.role_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_role_row_selected))
        self.role_table.addMouseListener(_DoubleClick(lambda: self._on_edit_role(None)))
        for col, width in ((0, 35), (1, 55), (2, 160), (3, 360)):
            self.role_table.getColumnModel().getColumn(col).setPreferredWidth(width)
        self.role_model.reload()

        left_panel = JPanel(BorderLayout(4, 4))
        left_panel.setBorder(BorderFactory.createTitledBorder(
            "Danh sách Profile / Role (Click chọn để sửa ngay bên phải)"))
        left_panel.add(JScrollPane(self.role_table), BorderLayout.CENTER)

        side = JPanel()
        side.setLayout(BoxLayout(side, BoxLayout.Y_AXIS))
        side.setBorder(BorderFactory.createEmptyBorder(4, 4, 4, 4))
        buttons = [
            ("Add Role...", self._on_add_role),
            ("Edit in Dialog...", self._on_edit_role),
            ("Duplicate", self._on_duplicate_role),
            ("Delete", self._on_delete_roles),
            (None, None),
            ("Move Up", lambda e: self._on_move_role(-1)),
            ("Move Down", lambda e: self._on_move_role(1)),
            (None, None),
            ("Enable All", lambda e: self._on_enable_all(True)),
            ("Disable All", lambda e: self._on_enable_all(False)),
            (None, None),
            ("Import JSON...", self._on_import_roles),
            ("Export JSON...", self._on_export_roles),
            (None, None),
            ("Load 10-Role Template", self._on_load_template),
        ]
        for label, handler in buttons:
            if label is None:
                side.add(Box.createVerticalStrut(10))
                continue
            b = JButton(label, actionPerformed=handler)
            b.setMaximumSize(Dimension(165, 28))
            side.add(b)
            side.add(Box.createVerticalStrut(4))
        left_panel.add(side, BorderLayout.EAST)

        first_role = self.roles.get(0) if self.roles.count() > 0 else {
            "name": "01_Admin", "enabled": True, "headers": []
        }
        self.inline_role_editor = RoleEditorPanel(first_role, inline_save_fn=self._on_save_inline_role)
        self.inline_role_editor.setBorder(BorderFactory.createTitledBorder(
            "Chỉnh sửa chi tiết Profile đang chọn (Header / Cookie / Session / JWT - Bấm 'Save Profile Changes' để lưu)"))

        split = JSplitPane(JSplitPane.HORIZONTAL_SPLIT, left_panel, self.inline_role_editor)
        split.setResizeWeight(0.42)
        panel.add(split, BorderLayout.CENTER)
        panel.add(JLabel(" Mỗi Role đang bật (Enabled) sẽ sinh ra 1 request tương ứng cho mỗi API bắt được. "
                         "Hỗ trợ thêm/sửa/xóa từng HTTP Header, từng biến Cookie/Session riêng lẻ, và JWT/Bearer."),
                  BorderLayout.SOUTH)
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
            sp.addChangeListener(lambda e: self._on_settings_changed(None))
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

    def _on_settings_changed(self, event):
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
        self.sp_threads.setValue(Integer(d["threads"]))
        self.sp_throttle.setValue(Integer(d["throttle_ms"]))
        self.sp_pathlen.setValue(Integer(d["short_path_len"]))
        self._on_settings_changed(None)

    def update_status(self):
        def refresh():
            if self.status_label is None or getattr(self, "btn_replay_all", None) is None:
                return
            cfg = self.get_config()
            with self._state_lock:
                seen = len(self._seen_keys)
            all_groups = self.group_model.all_groups() if getattr(self, "group_model", None) is not None else []
            info_apis = len([g for g in all_groups if evaluate_group_audit(g)[0] == AUDIT_INFO])
            feats = self.features_list()
            act = self.active_feature()
            self.status_label.setText(
                "Capture: %s  |  Roles: %d/%d  |  Chức năng: %d  |  Tổng API: %d (Vàng INFO: %d)  |  Dedup: %d"
                % ("ON" if cfg["capture_enabled"] else "OFF", self.roles.enabled_count(),
                   self.roles.count(), len(feats), len(all_groups), info_apis, seen))
            if getattr(self, "lbl_active_feature", None) is not None:
                self.lbl_active_feature.setText("Đang bắt vào Tên %d:" % act.fid)
                if not self.tf_feature_name.hasFocus():
                    self.tf_feature_name.setText(act.name)
                act_count = len([x for x in all_groups if x.fid == act.fid])
                self.lbl_feature_counter.setText(
                    "(%d chức năng | %s: %d API)"
                    % (len(feats), format_feature_label(act.fid, act.name), act_count))
            n = self.roles.enabled_count()
            g, _ = self.current_selection()
            count = len(g.results) if g is not None else n
            self.btn_replay_all.setText("Replay All %d Roles to Server" % count)
        ui_call(refresh)

    # ---------------------------------------- feature & history view helpers
    def _refresh_history_summary_only(self):
        if self.history_summary_area is None or self.group_model is None:
            return
        text = build_history_summary_text(self.features_list(), self.group_model.all_groups())
        self.history_summary_area.setText(text)
        self.history_summary_area.setCaretPosition(0)

    def _refresh_feature_views(self):
        def refresh():
            if self.feature_model is not None:
                sel_row = self.feature_table.getSelectedRow()
                self.feature_model.fireTableDataChanged()
                if 0 <= sel_row < self.feature_model.getRowCount():
                    self.feature_table.setRowSelectionInterval(sel_row, sel_row)
                elif self.feature_model.getRowCount() > 0:
                    self.feature_table.setRowSelectionInterval(0, 0)
            if self.history_tree_model is not None and self.group_model is not None:
                all_groups = self.group_model.all_groups()
                feats = self.features_list()
                root = DefaultMutableTreeNode(
                    "Tổng cộng: %d Chức năng | %d API đã đi qua" % (len(feats), len(all_groups)))
                for f in feats:
                    f_groups = [g for g in all_groups if g.fid == f.fid]
                    _, f_audit = evaluate_feature_audit(f_groups)
                    f_node = DefaultMutableTreeNode(_TreeNodeItem(
                        "FEATURE", f,
                        "%s  (%d API | %s)" % (format_feature_label(f.fid, f.name), len(f_groups), f_audit)
                    ))
                    for g in f_groups:
                        _, g_audit = evaluate_group_audit(g)
                        g_node = DefaultMutableTreeNode(_TreeNodeItem(
                            "GROUP", g,
                            "%s [%s]: %s %s (Orig: %s) -> [%s]"
                            % (format_api_label(g.gid), format_group_id(g.gid), g.method, g.path,
                               g.orig_status if g.orig_status is not None else "-", g_audit)
                        ))
                        for r in g.results:
                            _, r_badge = evaluate_role_result(g, r)
                            r_node = DefaultMutableTreeNode(_TreeNodeItem(
                                "ROLE", (g, r),
                                "%s -> [%s] | Status: %s | Len: %s | Tab: %s"
                                % (r.role_name,
                                   r_badge,
                                   r.status if r.status is not None else r.state,
                                   r.length if r.length is not None else "-",
                                   r.tab_name)
                            ))
                            g_node.add(r_node)
                        f_node.add(g_node)
                    root.add(f_node)
                self.history_tree_model.setRoot(root)
                self.history_tree_model.reload()
                for i in range(self.history_tree.getRowCount()):
                    self.history_tree.expandRow(i)
            self._refresh_history_summary_only()
        ui_call(refresh)

    def _on_apply_active_feature_name(self, event):
        act = self.active_feature()
        new_name = u_text(self.tf_feature_name.getText()).strip()
        if new_name:
            self.rename_feature(act.fid, new_name)

    def _on_next_feature(self, event):
        # Save any pending name change on current active feature first if user edited the text box
        cur = self.active_feature()
        typed = u_text(self.tf_feature_name.getText()).strip() if getattr(self, "tf_feature_name", None) else ""
        if typed and typed != cur.name:
            self.rename_feature(cur.fid, typed)
        next_num = len(self.features_list()) + 1
        name = JOptionPane.showInputDialog(
            self.main_panel,
            "Nhập tên cho Chức năng tiếp theo (Tên %d):\n"
            "(Các API xuất hiện khi bạn bấm nút tiếp theo trên web sẽ tự động gom vào đây)" % next_num,
            "Chức năng %d" % next_num)
        if name is None:
            return
        self.start_new_feature(u_text(name))

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
            self._show_result(None)

    def _on_show_all_features(self, event):
        if self.feature_table is not None and self.feature_model.getRowCount() > 0:
            self.feature_table.setRowSelectionInterval(0, 0)
        if getattr(self, "cb_audit_filter", None) is not None:
            self.cb_audit_filter.setSelectedIndex(0)
        if self.group_model is not None:
            self.group_model.set_feature_filter(None)
            self.group_model.set_audit_filter(AUDIT_FILTER_ALL)

    def _on_feature_filter_selected(self):
        if self.feature_table is None or self.group_model is None:
            return
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            self.group_model.set_feature_filter(None)
        else:
            feat = self.feature_model.feature_at_row(r)
            if feat is not None:
                self.group_model.set_feature_filter(feat.fid)
        if self.group_model.getRowCount() > 0:
            self.group_table.setRowSelectionInterval(0, 0)
        else:
            self.result_model.set_group(None)
            self._show_result(None)

    def _selected_feature_from_table(self):
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            return self.active_feature()
        return self.feature_model.feature_at_row(r) or self.active_feature()

    def _on_set_selected_feature_active(self, event):
        r = self.feature_table.getSelectedRow()
        if r <= 0:
            JOptionPane.showMessageDialog(
                self.main_panel, "Chọn một dòng Chức năng cụ thể (Tên 1, Tên 2...) trong bảng bên trái.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
            return
        feat = self.feature_model.feature_at_row(r)
        if feat is not None:
            self.set_active_feature(feat.fid)
            self.log("Đặt %s làm chức năng đang bắt API hiện tại." % format_feature_label(feat.fid, feat.name))

    def _on_rename_selected_feature(self, event):
        feat = self._selected_feature_from_table()
        if feat is None:
            return
        new_name = JOptionPane.showInputDialog(
            self.main_panel, "Đổi tên cho Tên %d:" % feat.fid, feat.name)
        if new_name is not None and new_name.strip():
            self.rename_feature(feat.fid, new_name.strip())

    def _on_send_feature_repeater(self, event):
        feat = self._selected_feature_from_table()
        if feat is None:
            return
        groups = self.group_model.groups_for_feature(feat.fid)
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chức năng này chưa có API nào.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        for g in groups:
            self.send_to_repeater(g, g.results)

    def _on_replay_feature(self, event):
        feat = self._selected_feature_from_table()
        if feat is None:
            return
        groups = self.group_model.groups_for_feature(feat.fid)
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chức năng này chưa có API nào.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        for g in groups:
            self.replay(g, g.results)

    def _on_move_groups_feature(self, event):
        groups = self._selected_groups()
        if not groups:
            self._require_group()
            return
        feats = self.features_list()
        options = [format_feature_label(f.fid, f.name) for f in feats] + ["+ Tạo Chức năng mới..."]
        choice = JOptionPane.showInputDialog(
            self.main_panel, "Chuyển %d API đang chọn sang Chức năng:" % len(groups),
            EXT_NAME, JOptionPane.PLAIN_MESSAGE, None, options, options[-1])
        if choice is None:
            return
        if choice == options[-1]:
            next_num = len(feats) + 1
            name = JOptionPane.showInputDialog(
                self.main_panel, "Nhập tên Chức năng mới (Tên %d):" % next_num, "Chức năng %d" % next_num)
            if not name:
                return
            feat = self.start_new_feature(name)
            self.move_groups_to_feature(groups, feat.fid)
            return
        for f in feats:
            if format_feature_label(f.fid, f.name) == choice:
                self.move_groups_to_feature(groups, f.fid)
                break

    # ---- History Tree actions
    def _selected_tree_payload(self):
        if self.history_tree is None:
            return None, None
        path = self.history_tree.getSelectionPath()
        if path is None:
            return None, None
        node = path.getLastPathComponent()
        obj = node.getUserObject() if isinstance(node, DefaultMutableTreeNode) else None
        if isinstance(obj, _TreeNodeItem):
            return obj.kind, obj.payload
        return None, None

    def _on_history_tree_selected(self):
        # Tree nodes render custom labels via DefaultMutableTreeNode string or tuple
        pass

    def _on_rename_tree_feature(self, event):
        kind, payload = self._selected_tree_payload()
        feat = payload if kind == "FEATURE" else (
            self.get_feature(payload.fid) if kind == "GROUP" else (
                self.get_feature(payload[0].fid) if kind == "ROLE" else self.active_feature()))
        if feat is None:
            return
        new_name = JOptionPane.showInputDialog(
            self.main_panel, "Đổi tên cho Tên %d:" % feat.fid, feat.name)
        if new_name is not None and new_name.strip():
            self.rename_feature(feat.fid, new_name.strip())

    def _on_send_tree_repeater(self, event):
        kind, payload = self._selected_tree_payload()
        if kind == "FEATURE":
            for g in self.group_model.groups_for_feature(payload.fid):
                self.send_to_repeater(g, g.results)
        elif kind == "GROUP":
            self.send_to_repeater(payload, payload.results)
        elif kind == "ROLE":
            g, r = payload
            self.send_to_repeater(g, [r])
        else:
            JOptionPane.showMessageDialog(
                self.main_panel, "Hãy chọn một Chức năng, API hoặc Role trong cây bên trái.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)

    def _on_replay_tree_selection(self, event):
        kind, payload = self._selected_tree_payload()
        if kind == "FEATURE":
            for g in self.group_model.groups_for_feature(payload.fid):
                self.replay(g, g.results)
        elif kind == "GROUP":
            self.replay(payload, payload.results)
        elif kind == "ROLE":
            g, r = payload
            self.replay(g, [r])
        else:
            JOptionPane.showMessageDialog(
                self.main_panel, "Hãy chọn một Chức năng, API hoặc Role trong cây bên trái.",
                EXT_NAME, JOptionPane.INFORMATION_MESSAGE)

    def _on_jump_to_group_from_tree(self, event):
        kind, payload = self._selected_tree_payload()
        target_group = None
        if kind == "GROUP":
            target_group = payload
        elif kind == "ROLE":
            target_group = payload[0]
        elif kind == "FEATURE":
            groups = self.group_model.groups_for_feature(payload.fid)
            target_group = groups[0] if groups else None
        if target_group is None:
            return
        self.group_model.set_feature_filter(None)
        if self.feature_table.getRowCount() > 0:
            self.feature_table.setRowSelectionInterval(0, 0)
        for mr in range(self.group_model.getRowCount()):
            if self.group_model.group_at(mr) is target_group:
                vr = self.group_table.convertRowIndexToView(mr)
                if vr >= 0:
                    self.group_table.setRowSelectionInterval(vr, vr)
                break
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
            if r is not None:
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
        self.update_status()

    def _select_first_result(self):
        if self.result_model.getRowCount() > 0:
            self.result_table.setRowSelectionInterval(0, 0)
        else:
            self._show_result(None)

    def _on_result_selected(self):
        _, res = self.current_selection()
        self._show_result(res)

    def _show_result(self, res):
        empty = self.helpers.stringToBytes("")
        if res is None:
            self.req_viewer.setMessage(empty, True)
            self.resp_viewer.setMessage(empty, False)
            return
        self.req_viewer.setMessage(res.request, True)
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
            self.send_to_repeater(g, g.results)

    def _on_send_role(self, event):
        g = self._require_group()
        if g is None:
            return
        results = self._selected_results()
        if not results:
            JOptionPane.showMessageDialog(self.main_panel, "Select one or more role rows.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        self.send_to_repeater(g, results)

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
        if results:
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
                self.main_panel, "Xóa toàn bộ các API đã bắt, đặt lại danh sách Chức năng về Tên 1 và xóa Dedup cache?",
                EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.group_model.clear()
        self.result_model.set_group(None)
        self._show_result(None)
        with self._state_lock:
            self._seen_keys.clear()
            self._next_gid = 1
            self._next_fid = 2
            self._active_fid = 1
            self._features = [FeatureGroup(1, "Chức năng 1")]
        self.group_model.set_feature_filter(None)
        self._refresh_feature_views()
        self.log("All captured APIs, feature history, and dedup cache reset.")
        self.update_status()

    def _on_reset_dedup(self, event):
        with self._state_lock:
            n = len(self._seen_keys)
            self._seen_keys.clear()
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
