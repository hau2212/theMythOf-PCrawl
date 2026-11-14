# -*- coding: utf-8 -*-
"""
theMythOfCrawl - Burp Suite extension (Jython 2.7, legacy Extender API)

Multi-role API request cloning and grouped Repeater dispatching for
authorization / access-control testing of applications you are permitted to test.

  * N role profiles, each with header rules (REPLACE / ADD / REMOVE or value [REMOVE])
  * Proxy capture with scope, static-extension, API-regex, method and dedup filters
  * Manual trigger via context menu (Proxy, Target, Repeater, Logger, ...)
  * 1-to-N cloning: one request per enabled role, method/URL/params/body preserved
  * Optional background replay recording status, length, time and full req/resp
  * Grouped Repeater tabs: "[G01:POST /v1/transfer] 01_Admin"
  * Master/Detail grouped view with group and role actions

Threading model
  * Burp listener threads only copy bytes and enqueue work (never block).
  * One single-thread "capture" executor builds groups (deterministic IDs + dedup).
  * A resizable thread pool performs all network I/O (makeHttpRequest).
  * Every Swing mutation goes through SwingUtilities.invokeLater (ui_call()).
"""

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

from java.awt import BorderLayout, FlowLayout, GridBagLayout, GridBagConstraints, Insets, Dimension, Color
from java.awt.event import MouseAdapter
from java.lang import Runnable, Boolean, Integer, String, Throwable
from java.util import ArrayList, Arrays
from java.util.concurrent import Executors, TimeUnit
from java.io import File
from java.nio.file import Files
from javax.swing import (JPanel, JLabel, JButton, JCheckBox, JTextField, JTable, JScrollPane,
                         JSplitPane, JTabbedPane, JTextArea, JMenuItem, JOptionPane, JFileChooser,
                         JDialog, JComboBox, JSpinner, SpinnerNumberModel, ListSelectionModel,
                         SwingUtilities, BorderFactory, DefaultCellEditor, BoxLayout, Box)
from javax.swing.event import ListSelectionListener
from javax.swing.table import AbstractTableModel, DefaultTableCellRenderer
from javax.swing.filechooser import FileNameExtensionFilter

try:
    basestring
except NameError:  # CPython 3 (offline unit tests only)
    basestring = str

# =============================================================================
# Constants
# =============================================================================

EXT_NAME = "theMythOfCrawl"
EXT_VERSION = "1.0.0"
SETTINGS_KEY_ROLES = "tmoc.roles.v1"
SETTINGS_KEY_CONFIG = "tmoc.config.v1"

REMOVE_TOKEN = "[REMOVE]"
MODE_REPLACE = "REPLACE"  # overwrite first occurrence (drop duplicates) or add if missing
MODE_ADD = "ADD"          # always append a new header line (allows duplicates)
MODE_REMOVE = "REMOVE"    # strip every occurrence
HEADER_MODES = [MODE_REPLACE, MODE_ADD, MODE_REMOVE]

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
    "auto_repeater": True,
    "auto_send": False,
    "number_roles_in_tab": True,
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
    if value is not None and ("%s" % value).strip().upper() == REMOVE_TOKEN:
        return MODE_REMOVE
    m = ("%s" % (mode or "")).strip().upper()
    if m in HEADER_MODES:
        return m
    return MODE_REPLACE


def _header_name_of(line):
    idx = line.find(":")
    if idx <= 0:
        return None
    return line[:idx].strip().lower()


def apply_header_rules(header_lines, rules):
    """
    header_lines: list of str, index 0 is the request line ("GET /x HTTP/1.1").
    rules: list of {"name", "value", "mode"} applied in order.
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


def display_role_name(role_name, index, number_roles):
    name = role_name or ("role%d" % (index + 1))
    if number_roles and not _ROLE_NUM_PREFIX_RE.match(name):
        return "%02d_%s" % (index + 1, name)
    return name


def repeater_tab_name(gid, method, path, role_display, max_len=40):
    return "[%s:%s %s] %s" % (format_group_id(gid), (method or "").upper(),
                              short_path(path, max_len), role_display)


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
    name = ("%s" % (obj.get("name") or "")).strip() or ("Role_%02d" % (index + 1))
    enabled = _as_bool(obj.get("enabled", True), True)
    raw = obj.get("headers", [])
    if isinstance(raw, dict):
        raw = [{"name": k, "value": raw[k]} for k in raw]
    headers = []
    for h in raw or []:
        if isinstance(h, basestring):
            if ":" not in h:
                continue
            k, v = h.split(":", 1)
            h = {"name": k, "value": v}
        if not isinstance(h, dict):
            continue
        hn = sanitize_header_name(h.get("name"))
        if not hn:
            continue
        hv = h.get("value")
        hv = "" if hv is None else "%s" % hv
        headers.append({"name": hn, "value": sanitize_header_value(hv),
                        "mode": normalize_mode(h.get("mode"), hv)})
    return {"name": name, "enabled": enabled, "headers": headers}


def roles_from_json(text):
    data = json.loads(text)
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
        ("04_Support", [{"name": "Cookie", "value": "session=SUPPORT_SESSION", "mode": MODE_REPLACE},
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


def groups_to_matrix_json(groups):
    """Serialize captured API groups and per-role status/length metrics to JSON."""
    items = []
    for g in groups or []:
        roles_out = []
        for r in g.results:
            delta = (r.length - g.orig_length) if (r.length is not None and g.orig_length is not None) else None
            roles_out.append({
                "role": r.role_name,
                "state": r.state,
                "status": r.status,
                "length": r.length,
                "delta_vs_orig": delta,
                "elapsed_ms": r.elapsed_ms,
                "sends": r.sent_count,
                "repeater_tab": r.tab_name,
                "error": r.error or None,
            })
        items.append({
            "group_id": format_group_id(g.gid),
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
    return json.dumps({"extension": EXT_NAME, "version": 1, "groups": items}, indent=2)



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


class RoleResult(object):
    def __init__(self, role_name, role_index, request_bytes):
        self.role_name = role_name
        self.role_index = role_index
        self.request = request_bytes
        self.response = None
        self.status = None
        self.length = None
        self.elapsed_ms = None
        self.state = STATE_NOT_SENT
        self.error = ""
        self.sent_count = 0
        self.tab_name = ""


class ApiGroup(object):
    def __init__(self, gid, service, method, path, url, orig_request, orig_response, source):
        self.gid = gid
        self.service = service
        self.host = service.getHost()
        self.port = service.getPort()
        self.protocol = service.getProtocol()
        self.method = method
        self.path = path
        self.url = url
        self.orig_request = orig_request
        self.orig_response = orig_response
        self.orig_status = None
        self.orig_length = None
        self.source = source
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
        return {"name": r.get("name", ""), "enabled": bool(r.get("enabled", True)),
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
    COLS = ["#", "Enabled", "Role Name", "Header Rules (+ADD  -REMOVE)"]

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
            return role["name"]
        parts = []
        for h in role["headers"]:
            prefix = {MODE_REMOVE: "-", MODE_ADD: "+"}.get(h["mode"], "")
            parts.append(prefix + h["name"])
        return ", ".join(parts)


class GroupTableModel(AbstractTableModel):
    COLS = ["Group", "Source", "Time", "Method", "Host", "Path", "Orig Status", "Orig Len",
            "Role Count", "Replayed"]

    def __init__(self):
        self._rows = []

    def add(self, group):
        self._rows.append(group)
        n = len(self._rows) - 1
        self.fireTableRowsInserted(n, n)

    def remove_groups(self, groups):
        ids = set([id(g) for g in groups])
        self._rows = [g for g in self._rows if id(g) not in ids]
        self.fireTableDataChanged()

    def clear(self):
        self._rows = []
        self.fireTableDataChanged()

    def group_at(self, r):
        if 0 <= r < len(self._rows):
            return self._rows[r]
        return None

    def all_groups(self):
        return list(self._rows)

    def refresh_group(self, group):
        for i, g in enumerate(self._rows):
            if g is group:
                self.fireTableRowsUpdated(i, i)
                return

    def getRowCount(self):
        return len(self._rows)

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (6, 7, 8):
            return Integer
        return String

    def getValueAt(self, r, c):
        g = self._rows[r]
        if c == 0:
            return format_group_id(g.gid)
        if c == 1:
            return g.source
        if c == 2:
            return g.created
        if c == 3:
            return g.method
        if c == 4:
            default_port = ((g.protocol == "https" and g.port == 443) or
                            (g.protocol == "http" and g.port == 80))
            return g.host if default_port else "%s:%s" % (g.host, g.port)
        if c == 5:
            return g.path
        if c == 6:
            return None if g.orig_status is None else Integer(g.orig_status)
        if c == 7:
            return None if g.orig_length is None else Integer(g.orig_length)
        if c == 8:
            return Integer(len(g.results))
        if c == 9:
            done = len([x for x in g.results if x.state in (STATE_DONE, STATE_ERROR)])
            return "%d/%d" % (done, len(g.results))
        return ""


class ResultTableModel(AbstractTableModel):
    COLS = ["#", "Role", "State", "Status", "Body Len", "Delta vs Orig", "Time (ms)", "Sends",
            "Repeater Tab / Error"]

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

    def getRowCount(self):
        return len(self._group.results) if self._group is not None else 0

    def getColumnCount(self):
        return len(self.COLS)

    def getColumnName(self, c):
        return self.COLS[c]

    def getColumnClass(self, c):
        if c in (0, 3, 4, 5, 6, 7):
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
            return res.state
        if c == 3:
            return None if res.status is None else Integer(res.status)
        if c == 4:
            return None if res.length is None else Integer(res.length)
        if c == 5:
            if res.length is None or g.orig_length is None:
                return None
            return Integer(res.length - g.orig_length)
        if c == 6:
            return None if res.elapsed_ms is None else Integer(res.elapsed_ms)
        if c == 7:
            return Integer(res.sent_count)
        if c == 8:
            return res.error if res.error else res.tab_name
        return ""


class StatusRenderer(DefaultTableCellRenderer):
    """Colors HTTP status cells: 2xx green, 3xx blue, 4xx orange, 5xx red."""

    def getTableCellRendererComponent(self, table, value, isSelected, hasFocus, row, column):
        comp = DefaultTableCellRenderer.getTableCellRendererComponent(
            self, table, value, isSelected, hasFocus, row, column)
        if not isSelected:
            comp.setForeground(table.getForeground())
            try:
                code = int("%s" % value) if value is not None else 0
            except Exception:
                code = 0
            if 200 <= code < 300:
                comp.setForeground(Color(0, 140, 0))
            elif 300 <= code < 400:
                comp.setForeground(Color(0, 90, 200))
            elif 400 <= code < 500:
                comp.setForeground(Color(210, 110, 0))
            elif code >= 500:
                comp.setForeground(Color(200, 0, 0))
        return comp


class HeaderRuleTableModel(AbstractTableModel):
    COLS = ["Header Name", "Value (use [REMOVE] to strip)", "Mode"]

    def __init__(self, rules):
        self.rules = [dict(r) for r in rules]

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
            self.rules[r]["mode"] = MODE_REMOVE
        self.fireTableRowsUpdated(r, r)

    def add_rule(self, rule):
        self.rules.append(dict(rule))
        n = len(self.rules) - 1
        self.fireTableRowsInserted(n, n)

    def remove_rows(self, rows):
        for i in sorted(set(rows), reverse=True):
            if 0 <= i < len(self.rules):
                del self.rules[i]
        self.fireTableDataChanged()


# =============================================================================
# Swing listeners / controllers
# =============================================================================


class _SelectionListener(ListSelectionListener):
    def __init__(self, fn):
        self._fn = fn

    def valueChanged(self, event):
        if not event.getValueIsAdjusting():
            self._fn()


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
# Role editor dialog
# =============================================================================


class RoleEditorDialog(object):
    """Modal editor for one role. Call show() on the EDT; returns a role dict or None."""

    def __init__(self, parent, role, title):
        self._result = None
        owner = SwingUtilities.getWindowAncestor(parent) if parent is not None else None
        self.dialog = JDialog(owner) if owner is not None else JDialog()
        self.dialog.setTitle(title)
        self.dialog.setModal(True)
        self.dialog.setLayout(BorderLayout(6, 6))

        top = JPanel(GridBagLayout())
        top.setBorder(BorderFactory.createEmptyBorder(8, 8, 0, 8))
        gc = GridBagConstraints()
        gc.insets = Insets(3, 3, 3, 3)
        gc.anchor = GridBagConstraints.WEST
        gc.gridx = 0
        gc.gridy = 0
        top.add(JLabel("Role name:"), gc)
        gc.gridx = 1
        gc.fill = GridBagConstraints.HORIZONTAL
        gc.weightx = 1.0
        self.name_field = JTextField(role.get("name", ""), 30)
        top.add(self.name_field, gc)
        gc.gridx = 2
        gc.weightx = 0.0
        gc.fill = GridBagConstraints.NONE
        self.enabled_box = JCheckBox("Enabled", bool(role.get("enabled", True)))
        top.add(self.enabled_box, gc)
        self.dialog.add(top, BorderLayout.NORTH)

        self.model = HeaderRuleTableModel(role.get("headers", []))
        self.table = JTable(self.model)
        self.table.putClientProperty("terminateEditOnFocusLost", Boolean.TRUE)
        self.table.setRowHeight(22)
        cm = self.table.getColumnModel()
        cm.getColumn(2).setCellEditor(DefaultCellEditor(JComboBox(HEADER_MODES)))
        cm.getColumn(0).setPreferredWidth(170)
        cm.getColumn(1).setPreferredWidth(430)
        cm.getColumn(2).setPreferredWidth(90)

        center = JPanel(BorderLayout())
        center.setBorder(BorderFactory.createEmptyBorder(0, 8, 0, 8))
        center.add(JScrollPane(self.table), BorderLayout.CENTER)
        center.add(JLabel("<html>REPLACE = overwrite the existing header (added if absent) &nbsp;|&nbsp; "
                          "ADD = always append another line &nbsp;|&nbsp; "
                          "REMOVE or value <b>[REMOVE]</b> = strip the header</html>"), BorderLayout.SOUTH)
        self.dialog.add(center, BorderLayout.CENTER)

        btns = JPanel(FlowLayout(FlowLayout.LEFT))
        btns.add(JButton("Add Header", actionPerformed=self._on_add))
        btns.add(JButton("Remove Selected", actionPerformed=self._on_remove))
        btns.add(JButton("Bulk Paste Headers...", actionPerformed=self._on_bulk))
        btns.add(Box.createHorizontalStrut(30))
        btns.add(JButton("Save", actionPerformed=self._on_save))
        btns.add(JButton("Cancel", actionPerformed=self._on_cancel))
        self.dialog.add(btns, BorderLayout.SOUTH)

        self.dialog.setSize(Dimension(840, 420))
        self.dialog.setLocationRelativeTo(owner)

    def _stop_editing(self):
        if self.table.isEditing():
            self.table.getCellEditor().stopCellEditing()

    def _on_add(self, event):
        self._stop_editing()
        self.model.add_rule({"name": "X-Role", "value": "", "mode": MODE_REPLACE})
        r = self.model.getRowCount() - 1
        self.table.setRowSelectionInterval(r, r)
        self.table.editCellAt(r, 0)

    def _on_remove(self, event):
        self._stop_editing()
        self.model.remove_rows(list(self.table.getSelectedRows()))

    def _on_bulk(self, event):
        self._stop_editing()
        area = JTextArea(12, 60)
        res = JOptionPane.showConfirmDialog(self.dialog, JScrollPane(area),
                                            "Paste headers, one 'Name: value' per line",
                                            JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)
        if res == JOptionPane.OK_OPTION:
            for rule in parse_bulk_headers(area.getText()):
                self.model.add_rule(rule)

    def _on_save(self, event):
        self._stop_editing()
        name = self.name_field.getText().strip()
        if not name:
            JOptionPane.showMessageDialog(self.dialog, "Role name is required.", EXT_NAME,
                                          JOptionPane.WARNING_MESSAGE)
            return
        bad = [r.get("name", "") for r in self.model.rules if not sanitize_header_name(r.get("name"))]
        if bad:
            JOptionPane.showMessageDialog(
                self.dialog, "Invalid header name(s): %s\n(no spaces, colons or line breaks)"
                % ", ".join(["'%s'" % b for b in bad]), EXT_NAME, JOptionPane.WARNING_MESSAGE)
            return
        self._result = normalize_role({"name": name, "enabled": self.enabled_box.isSelected(),
                                       "headers": self.model.rules})
        self.dialog.dispose()

    def _on_cancel(self, event):
        self._result = None
        self.dialog.dispose()

    def show(self):
        self.dialog.setVisible(True)  # modal: blocks until disposed
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
        self._seen_keys = set()
        self._unloaded = False
        self._api_regex = None
        self._static_exts = set()
        self.log_area = None
        self.main_panel = None
        self.status_label = None
        self.group_model = None
        self.result_model = None

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
            self.capture_executor.execute(_Task(
                lambda: self._process_capture(service, req_copy, resp_copy, "Proxy", True), self.log))
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

        def make_handler(apply_filters):
            def handler(event):
                for svc, rq, rs in snapshot:
                    self.capture_executor.execute(_Task(
                        (lambda s=svc, a=rq, b=rs: self._process_capture(s, a, b, "Manual", apply_filters)),
                        self.log))
                self.log("Manual trigger: %d message(s) queued (%s)." %
                         (len(snapshot), "capture filters applied" if apply_filters else "filters bypassed"))
            return handler

        items = ArrayList()
        items.add(JMenuItem("%s: Clone to all enabled roles (%d message(s))" % (EXT_NAME, len(snapshot)),
                            actionPerformed=make_handler(False)))
        items.add(JMenuItem("%s: Clone to all enabled roles (apply capture filters + dedup)" % EXT_NAME,
                            actionPerformed=make_handler(True)))
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
    def _process_capture(self, service, req, resp, source, apply_filters):
        """Runs on the single capture thread (deterministic group IDs + dedup)."""
        if self._unloaded:
            return
        cfg = self.get_config()
        info = self.helpers.analyzeRequest(service, req)
        url = info.getUrl()
        method = ("%s" % (info.getMethod() or "GET")).upper()
        path = url.getFile() or "/"

        if apply_filters:
            reason = self._filter_reason(cfg, url, method, path)
            if reason:
                if source == "Manual":
                    self.log("Skipped %s %s (%s)" % (method, url, reason))
                return
            if cfg["dedup"]:
                key = dedup_key(method, service.getProtocol(), service.getHost(), service.getPort(),
                                path, cfg["dedup_normalize_ids"])
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

        group = ApiGroup(gid, service, method, path, "%s" % url, req, resp, source)
        if resp is not None:
            try:
                rinfo = self.helpers.analyzeResponse(resp)
                group.orig_status = rinfo.getStatusCode()
                group.orig_length = len(resp) - rinfo.getBodyOffset()
            except Throwable:
                pass
        group.results = self._clone_for_roles(group, info, roles, cfg)

        ui_call(lambda: self._add_group_ui(group))
        self.log("%s: %s %s -> %d role clone(s) [%s]" %
                 (format_group_id(gid), method, url, len(group.results), source))
        if cfg["auto_repeater"]:
            self._dispatch_repeater(group, group.results)
        if cfg["auto_send"]:
            self.replay(group, group.results)

    def _clone_for_roles(self, group, info, roles, cfg):
        """Build exactly one request per enabled role; method/URL/params/body preserved."""
        req = group.orig_request
        base_headers = [("%s" % h) for h in info.getHeaders()]
        body = Arrays.copyOfRange(req, info.getBodyOffset(), len(req))
        results = []
        for idx, role in enumerate(roles):
            new_headers = apply_header_rules(base_headers, role["headers"])
            jlist = ArrayList()
            for h in new_headers:
                jlist.add(h)
            new_req = self.helpers.buildHttpMessage(jlist, body)
            display = display_role_name(role["name"], idx, cfg["number_roles_in_tab"])
            res = RoleResult(display, idx, new_req)
            res.tab_name = repeater_tab_name(group.gid, group.method, group.path, display,
                                             cfg["short_path_len"])
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
            ui_call(apply)
            self.log("%s rebuilt with %d current role(s)." % (format_group_id(group.gid), len(new_results)))
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
        self.log("%s: %d request(s) sent to Repeater." % (format_group_id(group.gid), len(results)))

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
        ui_call(refresh)

    # ===================================================================== UI
    def _build_ui(self):
        self.main_panel = JPanel(BorderLayout())
        cfg = self.get_config()

        # ---- top control bar (most used toggles)
        bar = JPanel(FlowLayout(FlowLayout.LEFT, 8, 4))
        self.cb_capture = JCheckBox("Capture Proxy traffic", cfg["capture_enabled"],
                                    actionPerformed=self._on_settings_changed)
        self.cb_auto_repeater = JCheckBox("Auto-send new groups to Repeater", cfg["auto_repeater"],
                                          actionPerformed=self._on_settings_changed)
        self.cb_auto_send = JCheckBox("Auto-Send to Server & Record", cfg["auto_send"],
                                      actionPerformed=self._on_settings_changed)
        self.status_label = JLabel("")
        for comp in (self.cb_capture, self.cb_auto_repeater, self.cb_auto_send):
            bar.add(comp)
        bar.add(Box.createHorizontalStrut(20))
        bar.add(self.status_label)
        self.main_panel.add(bar, BorderLayout.NORTH)

        tabs = JTabbedPane()
        tabs.addTab("API Groups", self._build_groups_tab())
        tabs.addTab("Roles", self._build_roles_tab())
        tabs.addTab("Capture Filters & Options", self._build_settings_tab(cfg))
        self.log_area = JTextArea()
        self.log_area.setEditable(False)
        tabs.addTab("Log", JScrollPane(self.log_area))
        self.main_panel.add(tabs, BorderLayout.CENTER)
        self.callbacks.customizeUiComponent(self.main_panel)

    # ---- API Groups tab (master/detail)
    def _build_groups_tab(self):
        panel = JPanel(BorderLayout())

        actions = JPanel(FlowLayout(FlowLayout.LEFT, 4, 4))
        self.btn_send_group = JButton("Send Entire Group to Repeater", actionPerformed=self._on_send_group)
        self.btn_send_role = JButton("Send Selected Role to Repeater", actionPerformed=self._on_send_role)
        self.btn_replay_all = JButton("Replay All Roles to Server", actionPerformed=self._on_replay_all)
        self.btn_replay_sel = JButton("Replay Selected Role(s)", actionPerformed=self._on_replay_selected)
        actions.add(self.btn_send_group)
        actions.add(self.btn_send_role)
        actions.add(self.btn_replay_all)
        actions.add(self.btn_replay_sel)
        actions.add(JButton("Rebuild with Current Roles", actionPerformed=self._on_rebuild))
        actions.add(JButton("Show Original Req/Resp", actionPerformed=self._on_show_original))
        actions.add(JButton("Export Matrix JSON...", actionPerformed=self._on_export_matrix))
        actions.add(JButton("Delete Group(s)", actionPerformed=self._on_delete_groups))
        actions.add(JButton("Clear All", actionPerformed=self._on_clear_groups))
        actions.add(JButton("Reset Dedup Cache", actionPerformed=self._on_reset_dedup))
        panel.add(actions, BorderLayout.NORTH)

        status_renderer = StatusRenderer()

        self.group_model = GroupTableModel()
        self.group_table = JTable(self.group_model)
        self.group_table.setAutoCreateRowSorter(True)
        self.group_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.group_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_group_selected))
        self.group_table.addMouseListener(_DoubleClick(lambda: self._on_send_group(None)))
        self.group_table.getColumnModel().getColumn(6).setCellRenderer(status_renderer)
        for col, width in ((0, 60), (1, 60), (2, 70), (3, 70), (4, 200), (5, 420), (6, 80), (7, 80),
                           (8, 80), (9, 70)):
            self.group_table.getColumnModel().getColumn(col).setPreferredWidth(width)

        self.result_model = ResultTableModel()
        self.result_table = JTable(self.result_model)
        self.result_table.setAutoCreateRowSorter(True)
        self.result_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.result_table.getSelectionModel().addListSelectionListener(
            _SelectionListener(self._on_result_selected))
        self.result_table.addMouseListener(_DoubleClick(lambda: self._on_send_role(None)))
        self.result_table.getColumnModel().getColumn(3).setCellRenderer(status_renderer)
        for col, width in ((0, 35), (1, 160), (2, 80), (3, 60), (4, 80), (5, 90), (6, 75), (7, 50),
                           (8, 420)):
            self.result_table.getColumnModel().getColumn(col).setPreferredWidth(width)

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

        detail_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.result_table), viewers)
        detail_split.setResizeWeight(0.35)
        master_split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.group_table), detail_split)
        master_split.setResizeWeight(0.35)
        panel.add(master_split, BorderLayout.CENTER)
        return panel

    # ---- Roles tab
    def _build_roles_tab(self):
        panel = JPanel(BorderLayout())
        self.role_model = RoleTableModel(self)
        self.role_table = JTable(self.role_model)
        self.role_table.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION)
        self.role_table.addMouseListener(_DoubleClick(lambda: self._on_edit_role(None)))
        for col, width in ((0, 35), (1, 60), (2, 220), (3, 600)):
            self.role_table.getColumnModel().getColumn(col).setPreferredWidth(width)
        self.role_model.reload()
        panel.add(JScrollPane(self.role_table), BorderLayout.CENTER)

        side = JPanel()
        side.setLayout(BoxLayout(side, BoxLayout.Y_AXIS))
        side.setBorder(BorderFactory.createEmptyBorder(6, 6, 6, 6))
        buttons = [
            ("Add Role", self._on_add_role), ("Edit Role", self._on_edit_role),
            ("Duplicate", self._on_duplicate_role), ("Delete", self._on_delete_roles),
            (None, None),
            ("Move Up", lambda e: self._on_move_role(-1)), ("Move Down", lambda e: self._on_move_role(1)),
            (None, None),
            ("Enable All", lambda e: self._on_enable_all(True)),
            ("Disable All", lambda e: self._on_enable_all(False)),
            (None, None),
            ("Import JSON...", self._on_import_roles), ("Export JSON...", self._on_export_roles),
            (None, None),
            ("Load 10-Role Template", self._on_load_template),
        ]
        for label, handler in buttons:
            if label is None:
                side.add(Box.createVerticalStrut(12))
                continue
            b = JButton(label, actionPerformed=handler)
            b.setMaximumSize(Dimension(160, 28))
            side.add(b)
            side.add(Box.createVerticalStrut(4))
        panel.add(side, BorderLayout.EAST)
        panel.add(JLabel(" Each enabled role produces one cloned request per captured API. "
                         "Order here = order in groups/Repeater. Double-click to edit."), BorderLayout.SOUTH)
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
        self.cb_number = JCheckBox("Prefix role index in tab names (01_, 02_ ...) unless the name already has one",
                                   cfg["number_roles_in_tab"], actionPerformed=on_change)
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
        add_row(JLabel("<html><br><b>Cloning, Repeater and replay</b></html>"))
        add_row(self.cb_number)
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
            "number_roles_in_tab": self.cb_number.isSelected(),
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
        self.cb_number.setSelected(d["number_roles_in_tab"])
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
            groups = self.group_model.getRowCount() if getattr(self, "group_model", None) is not None else 0
            self.status_label.setText("Capture: %s  |  Roles enabled: %d/%d  |  Groups: %d  |  Dedup keys: %d"
                                      % ("ON" if cfg["capture_enabled"] else "OFF", self.roles.enabled_count(),
                                         self.roles.count(), groups, seen))
            n = self.roles.enabled_count()
            g, _ = self.current_selection()
            count = len(g.results) if g is not None else n
            self.btn_replay_all.setText("Replay All %d Roles to Server" % count)
        ui_call(refresh)

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
        if self.group_table.getSelectedRow() < 0:
            last = self.group_table.convertRowIndexToView(self.group_model.getRowCount() - 1)
            if last >= 0:
                self.group_table.setRowSelectionInterval(last, last)
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
            self.log("%s: replaying %d role(s) to server." % (format_group_id(g.gid), len(g.results)))

    def _on_replay_selected(self, event):
        g = self._require_group()
        if g is None:
            return
        results = self._selected_results()
        if results:
            self.replay(g, results)
            self.log("%s: replaying %d selected role(s)." % (format_group_id(g.gid), len(results)))

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
            data = String(groups_to_matrix_json(groups)).getBytes("UTF-8")
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
        self.update_status()

    def _on_clear_groups(self, event):
        if JOptionPane.showConfirmDialog(self.main_panel, "Clear all captured groups and the dedup cache?",
                                         EXT_NAME, JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.group_model.clear()
        self.result_model.set_group(None)
        self._show_result(None)
        with self._state_lock:
            self._seen_keys.clear()
        self.log("All groups cleared (group IDs continue incrementing to keep Repeater tab names unique).")
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
        self.update_status()

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
        self._roles_changed()

    def _on_move_role(self, delta):
        idx = self.role_table.getSelectedRow()
        if idx < 0:
            return
        self._roles_changed(self.roles.move(idx, delta))

    def _on_enable_all(self, enabled):
        self.roles.set_all_enabled(enabled)
        self._roles_changed()

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
        self._roles_changed()
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
        self._roles_changed()
        self.log("Loaded 10 starter role profiles.")
