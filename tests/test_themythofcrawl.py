# -*- coding: utf-8 -*-
"""
Offline tests for theMythOfCrawl under CPython 3 (no Burp / Jython needed).

Burp, java.* and javax.* modules are replaced by lightweight stubs so the pure
logic and the capture -> clone -> Repeater -> replay engine can be exercised.
Swing UI construction is not executed here (it requires a real JVM).

Run:  python -m unittest discover -s tests -v
"""

import importlib.abc
import importlib.machinery
import json
import os
import sys
import types
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ----------------------------------------------------------------------------- stubs


class _DummyMeta(type):
    def __getattr__(cls, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return lambda *a, **k: _dummy_class(n)()


def _dummy_class(name):
    def __init__(self, *a, **k):
        if name == "JComboBox" and "actionPerformed" in k:
            raise TypeError("readonly attribute")

    def __getattr__(self, n):
        if n.startswith("__"):
            raise AttributeError(n)
        return lambda *a, **k: _dummy_class(n)()
    return _DummyMeta(name, (object,), {"__init__": __init__, "__getattr__": __getattr__})


class _StubModule(types.ModuleType):
    def __getattr__(self, name):
        if name.startswith("__"):
            raise AttributeError(name)
        cls = _dummy_class(name)
        setattr(self, name, cls)
        return cls


class _StubFinder(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    PREFIXES = ("burp", "java", "javax")

    def find_spec(self, fullname, path, target=None):
        if fullname.split(".")[0] in self.PREFIXES:
            return importlib.machinery.ModuleSpec(fullname, self, is_package=True)
        return None

    def create_module(self, spec):
        mod = _StubModule(spec.name)
        mod.__path__ = []
        return mod

    def exec_module(self, module):
        pass


sys.meta_path.insert(0, _StubFinder())

import java.lang  # noqa: E402
import java.util  # noqa: E402
import java.util.concurrent  # noqa: E402
import javax.swing  # noqa: E402


class _Throwable(Exception):
    pass


class _ArrayList(list):
    def add(self, x):
        self.append(x)


class _Arrays(object):
    @staticmethod
    def copyOf(b, n):
        return bytes(b[:n])

    @staticmethod
    def copyOfRange(b, s, e):
        return bytes(b[s:e])


class _SyncExecutor(object):
    def __init__(self, n=1):
        self.n = n

    def execute(self, task):
        task.run()

    def shutdownNow(self):
        return []

    def awaitTermination(self, *a):
        return True

    def getMaximumPoolSize(self):
        return self.n

    def setMaximumPoolSize(self, n):
        self.n = n

    def setCorePoolSize(self, n):
        pass


class _RecordingScheduler(object):
    """Delayed tasks are only recorded; tests drive the clock and run them explicitly."""

    def __init__(self):
        self.tasks = []

    def schedule(self, task, delay, unit):
        self.tasks.append((delay, task))

    def shutdownNow(self):
        return []

    def awaitTermination(self, *a):
        return True


class _Executors(object):
    @staticmethod
    def newSingleThreadExecutor():
        return _SyncExecutor(1)

    @staticmethod
    def newSingleThreadScheduledExecutor():
        return _RecordingScheduler()

    @staticmethod
    def newFixedThreadPool(n):
        return _SyncExecutor(n)


class _SwingUtilities(object):
    queued = []

    @staticmethod
    def isEventDispatchThread():
        return False

    @staticmethod
    def invokeLater(task):
        _SwingUtilities.queued.append(task)  # UI work is not executed in tests


class _Color(object):
    """Just enough of java.awt.Color for the palette maths."""

    def __init__(self, r, g, b, *a):
        self.r, self.g, self.b = int(r), int(g), int(b)

    def getRed(self):
        return self.r

    def getGreen(self):
        return self.g

    def getBlue(self):
        return self.b

    def getRGB(self):
        return (self.r << 16) | (self.g << 8) | self.b


class _UIManager(object):
    @staticmethod
    def getColor(key):
        return None


import java.awt  # noqa: E402

java.awt.Color = _Color
javax.swing.UIManager = _UIManager
java.lang.Throwable = _Throwable
java.util.ArrayList = _ArrayList
java.util.Arrays = _Arrays
java.util.concurrent.Executors = _Executors
javax.swing.SwingUtilities = _SwingUtilities

sys.path.insert(0, ROOT)
import theMythOfCrawl as tm  # noqa: E402

# ----------------------------------------------------------------------------- fake Burp


class FakeService(object):
    def __init__(self, host="api.example.test", port=443, protocol="https"):
        self._h, self._p, self._proto = host, port, protocol

    def getHost(self):
        return self._h

    def getPort(self):
        return self._p

    def getProtocol(self):
        return self._proto


class FakeUrl(object):
    def __init__(self, service, file_):
        self.service, self.file = service, file_

    def getFile(self):
        return self.file

    def __str__(self):
        return "%s://%s%s" % (self.service.getProtocol(), self.service.getHost(), self.file)


def _split(msg):
    idx = msg.find(b"\r\n\r\n")
    head = msg[:idx].decode("latin-1")
    return head.split("\r\n"), idx + 4


class FakeReqInfo(object):
    def __init__(self, service, req):
        self.lines, self.offset = _split(req)
        self.service = service

    def getHeaders(self):
        return list(self.lines)

    def getBodyOffset(self):
        return self.offset

    def getMethod(self):
        return self.lines[0].split(" ")[0]

    def getUrl(self):
        return FakeUrl(self.service, self.lines[0].split(" ")[1])


class FakeRespInfo(object):
    def __init__(self, resp):
        self.lines, self.offset = _split(resp)

    def getStatusCode(self):
        return int(self.lines[0].split(" ")[1])

    def getHeaders(self):
        return list(self.lines)

    def getBodyOffset(self):
        return self.offset


class FakeHelpers(object):
    def analyzeRequest(self, service, req):
        return FakeReqInfo(service, req)

    def analyzeResponse(self, resp):
        return FakeRespInfo(resp)

    def buildHttpMessage(self, headers, body):
        hs = [h for h in headers if not h.lower().startswith("content-length:")]
        if body:
            hs.append("Content-Length: %d" % len(body))
        return ("\r\n".join(hs) + "\r\n\r\n").encode("latin-1") + bytes(body)

    def stringToBytes(self, s):
        return s.encode("latin-1")


class FakeRR(object):
    def __init__(self, resp):
        self._r = resp

    def getResponse(self):
        return self._r


class FakeCallbacks(object):
    TOOL_PROXY = 4
    TOOL_REPEATER = 64

    def __init__(self):
        self.settings = {}
        self.repeater = []
        self.sent = []
        self.in_scope = True
        self.out = []

    def getHelpers(self):
        return FakeHelpers()

    def setExtensionName(self, n):
        self.name = n

    def loadExtensionSetting(self, k):
        return self.settings.get(k)

    def saveExtensionSetting(self, k, v):
        self.settings[k] = v

    def registerExtensionStateListener(self, l):
        pass

    def registerHttpListener(self, l):
        pass

    def registerContextMenuFactory(self, f):
        pass

    def addSuiteTab(self, tab):
        self.tab = tab

    def customizeUiComponent(self, comp):
        pass

    def createMessageEditor(self, ctrl, editable):
        return _dummy_class("FakeEditor")()

    def printOutput(self, s):
        self.out.append(s)

    def printError(self, s):
        self.out.append("ERROR: " + str(s))

    def isInScope(self, url):
        return self.in_scope

    def sendToRepeater(self, host, port, https, req, caption):
        self.repeater.append((host, port, https, req, caption))

    def makeHttpRequest(self, service, req):
        self.sent.append(req)
        lines, _ = _split(req)
        auth = [l for l in lines if l.lower().startswith("authorization:")]
        if not auth:
            return FakeRR(b"HTTP/1.1 401 Unauthorized\r\n\r\nno")
        if "admin" in auth[0]:
            return FakeRR(b"HTTP/1.1 200 OK\r\n\r\n{\"ok\":true,\"admin\":1}")
        return FakeRR(b"HTTP/1.1 403 Forbidden\r\n\r\ndenied")


# ----------------------------------------------------------------------------- tests

BASE_REQ = (b"POST /v1/transfer?x=1 HTTP/1.1\r\nHost: api.example.test\r\n"
            b"Authorization: Bearer original\r\nCookie: sid=orig\r\nX-Debug: 1\r\n"
            b"Content-Type: application/json\r\nContent-Length: 13\r\n\r\n{\"amount\":10}")
BASE_RESP = b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"ok\":true}"


class HeaderRuleTests(unittest.TestCase):
    LINES = ["GET /a HTTP/1.1", "Host: h", "Authorization: old", "Cookie: a=1", "cookie: b=2"]

    def test_replace_existing_and_drop_duplicates(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "Cookie", "value": "z=9", "mode": "REPLACE"}])
        self.assertEqual(out, ["GET /a HTTP/1.1", "Host: h", "Authorization: old", "Cookie: z=9"])

    def test_add_missing(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "X-Role", "value": "admin"}])
        self.assertEqual(out[-1], "X-Role: admin")

    def test_add_mode_appends_duplicate(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "Cookie", "value": "c=3", "mode": "ADD"}])
        self.assertEqual(len([l for l in out if l.lower().startswith("cookie")]), 3)

    def test_remove_token_strips_all_case_insensitive(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "COOKIE", "value": "[REMOVE]", "mode": "REPLACE"}])
        self.assertFalse([l for l in out if l.lower().startswith("cookie")])

    def test_request_line_untouched_and_crlf_sanitized(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "X-A", "value": "v\r\nInjected: 1"}])
        self.assertEqual(out[0], "GET /a HTTP/1.1")
        self.assertIn("X-A: vInjected: 1", out)

    def test_invalid_header_names_ignored(self):
        out = tm.apply_header_rules(self.LINES, [{"name": "Bad Name", "value": "x"}, {"name": "a:b", "value": "x"}])
        self.assertEqual(out, self.LINES)

    def test_cookie_set_and_cookie_remove_granular(self):
        lines = ["GET /a HTTP/1.1", "Host: h", "Cookie: theme=dark; JSESSIONID=old_sess; lang=vi"]
        # Overwrite JSESSIONID and add tenant_id while keeping theme=dark and lang=vi
        out = tm.apply_header_rules(lines, [
            {"name": "JSESSIONID", "value": "new_role_sess", "mode": "COOKIE_SET"},
            {"name": "tenant_id", "value": "t42", "mode": "COOKIE_SET"},
        ])
        self.assertEqual(
            out,
            ["GET /a HTTP/1.1", "Host: h", "Cookie: theme=dark; JSESSIONID=new_role_sess; lang=vi; tenant_id=t42"]
        )
        # Strip JSESSIONID only while keeping theme, lang, tenant_id
        out2 = tm.apply_header_rules(out, [
            {"name": "JSESSIONID", "value": "[REMOVE]", "mode": "COOKIE_REMOVE"},
        ])
        self.assertEqual(
            out2,
            ["GET /a HTTP/1.1", "Host: h", "Cookie: theme=dark; lang=vi; tenant_id=t42"]
        )
        # Stripping all cookies removes the Cookie header completely
        out3 = tm.apply_header_rules(["GET /a HTTP/1.1", "Host: h", "Cookie: sid=123"], [
            {"name": "sid", "value": "[REMOVE]", "mode": "COOKIE_SET"},
        ])
        self.assertEqual(out3, ["GET /a HTTP/1.1", "Host: h"])

    def test_jwt_bearer_and_decoder(self):
        self.assertEqual(tm.format_jwt_bearer("abc.def.ghi", "Bearer"), "Bearer abc.def.ghi")
        self.assertEqual(tm.format_jwt_bearer("Bearer abc.def.ghi", "Bearer"), "Bearer abc.def.ghi")
        self.assertEqual(tm.format_jwt_bearer("rawtoken", ""), "rawtoken")
        self.assertEqual(tm.format_jwt_bearer("[remove]", "Bearer"), "[REMOVE]")
        # Sample JWT: {"alg":"HS256"} . {"sub":"u1","role":"admin"}
        jwt_tok = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiJ1MSIsInJvbGUiOiJhZG1pbiJ9.sig"
        decoded = tm.decode_jwt_preview("Authorization: Bearer " + jwt_tok)
        self.assertIn('"role": "admin"', decoded)
        self.assertIn('"sub": "u1"', decoded)

    def test_parse_bulk_cookies(self):
        rules = tm.parse_bulk_cookies("Cookie: sid=abc; csrf=xyz\ntheme=[REMOVE]")
        self.assertEqual(
            [(r["name"], r["value"], r["mode"]) for r in rules],
            [("sid", "abc", "COOKIE_SET"), ("csrf", "xyz", "COOKIE_SET"), ("theme", "[REMOVE]", "COOKIE_REMOVE")]
        )


class FilterAndNamingTests(unittest.TestCase):
    def test_static(self):
        exts = tm.parse_static_extensions(".JS, css woff2;png")
        self.assertTrue(tm.is_static_path("/static/app.min.js?v=3", exts))
        self.assertTrue(tm.is_static_path("/f/x.WOFF2", exts))
        self.assertFalse(tm.is_static_path("/api/v1/users", exts))
        self.assertFalse(tm.is_static_path("/api/v1.2/users", exts))

    def test_default_regex(self):
        rx, err = tm.compile_api_regex(tm.DEFAULT_API_REGEX)
        self.assertIsNone(err)
        for p in ("/api/users", "/v1/transfer", "/graphql", "/x/data.json"):
            self.assertTrue(rx.search(p), p)
        self.assertFalse(rx.search("/index.html"))
        self.assertEqual(tm.compile_api_regex("([")[0], None)

    def test_dedup_key(self):
        a = tm.dedup_key("post", "HTTPS", "API.example.test", 443, "/v1/u/123?a=1")
        b = tm.dedup_key("POST", "https", "api.example.test", 443, "/v1/u/123?b=2")
        self.assertEqual(a, b)
        n1 = tm.dedup_key("GET", "https", "h", 443, "/u/123", True)
        n2 = tm.dedup_key("GET", "https", "h", 443, "/u/9f1c2a7e-1111-2222-3333-444455556666", True)
        self.assertEqual(n1, n2)

    def test_tab_name(self):
        self.assertEqual(tm.repeater_tab_name(1, "post", "/v1/transfer?x=1", "01_Admin"),
                         "[G01:POST /v1/transfer] 01_Admin")
        self.assertEqual(tm.display_role_name("Admin", 0, True), "01_Admin")
        self.assertEqual(tm.display_role_name("10_Guest", 9, True), "10_Guest")
        self.assertEqual(tm.display_role_name("Guest", 9, False), "Guest")
        long_name = tm.repeater_tab_name(123, "GET", "/" + "a" * 100, "R", 20)
        self.assertTrue(long_name.startswith("[G123:GET ..."))


class RoleJsonTests(unittest.TestCase):
    def test_round_trip_and_flexible_shapes(self):
        text = json.dumps([
            {"name": "01_Admin", "headers": [{"name": "Authorization", "value": "Bearer a"}]},
            {"name": "02_User", "enabled": "false", "headers": {"Cookie": "s=1", "X-Debug": "[REMOVE]"}},
            {"headers": ["X-Role: guest", "garbage"]},
        ])
        roles = tm.roles_from_json(text)
        self.assertEqual([r["name"] for r in roles], ["01_Admin", "02_User", "Role_03"])
        self.assertFalse(roles[1]["enabled"])
        modes = dict((h["name"], h["mode"]) for h in roles[1]["headers"])
        self.assertEqual(modes["X-Debug"], "REMOVE")
        again = tm.roles_from_json(tm.roles_to_json(roles))
        self.assertEqual(again, roles)

    def test_example_file_loads(self):
        with open(os.path.join(ROOT, "roles.example.json"), "r") as f:
            roles = tm.roles_from_json(f.read())
        self.assertEqual(len(roles), 10)
        templates = tm.default_role_templates()
        self.assertEqual(len(templates), 10)
        self.assertEqual(templates[0]["name"], "01_Admin")
        self.assertEqual(templates[-1]["name"], "10_Guest")

    def test_bulk_and_config(self):
        rules = tm.parse_bulk_headers("Authorization: Bearer x\nnot a header\nX-Old: [REMOVE]\n")
        self.assertEqual([(r["name"], r["mode"]) for r in rules],
                         [("Authorization", "REPLACE"), ("X-Old", "REMOVE")])
        cfg = tm.merge_config({"threads": "999", "dedup": "no", "unknown": 1})
        self.assertEqual(cfg["threads"], 64)
        self.assertFalse(cfg["dedup"])
        self.assertNotIn("unknown", cfg)


class EngineTests(unittest.TestCase):
    def setUp(self):
        self.cb = FakeCallbacks()
        roles = [{"name": "Admin", "enabled": True,
                  "headers": [{"name": "Authorization", "value": "Bearer admin-token"}]}]
        roles += [{"name": "User%d" % i, "enabled": True,
                   "headers": [{"name": "Authorization", "value": "Bearer user%d" % i},
                               {"name": "Cookie", "value": "sid=u%d" % i}]} for i in range(2, 10)]
        roles += [{"name": "Guest", "enabled": True,
                   "headers": [{"name": "Authorization", "value": "[REMOVE]"},
                               {"name": "Cookie", "value": "[REMOVE]"}]}]
        roles += [{"name": "Disabled", "enabled": False, "headers": []}]
        self.cb.settings[tm.SETTINGS_KEY_ROLES] = json.dumps(roles)
        self.cb.settings[tm.SETTINGS_KEY_CONFIG] = json.dumps({
            "capture_enabled": True,
            "auto_send": True,
            "auto_repeater": True,
            "send_profile": "CUSTOM",
            "send_delay_ms": 0,
            "send_jitter_pct": 0,
        })
        self.ext = tm.BurpExtender()
        self.ext.registerExtenderCallbacks(self.cb)
        self.svc = FakeService()

    def capture(self, req=BASE_REQ, source="Proxy", filters=True):
        self.ext._process_capture(self.svc, req, BASE_RESP, source, filters)

    def test_one_to_n_clone_repeater_and_replay(self):
        self.capture()
        self.assertEqual(len(self.cb.repeater), 10)
        names = [r[4] for r in self.cb.repeater]
        self.assertEqual(names[0], "[G01:POST /v1/transfer] 01_Admin")
        self.assertEqual(names[-1], "[G01:POST /v1/transfer] 10_Guest")
        for host, port, https, req, _ in self.cb.repeater:
            self.assertEqual((host, port, https), ("api.example.test", 443, True))
            lines, off = _split(req)
            self.assertEqual(lines[0], "POST /v1/transfer?x=1 HTTP/1.1")
            self.assertEqual(req[off:], b"{\"amount\":10}")
            self.assertIn("X-Debug: 1", lines)
            self.assertEqual(len([l for l in lines if l.lower().startswith("authorization")]) <= 1, True)
        guest_lines, _ = _split(self.cb.repeater[-1][3])
        self.assertFalse([l for l in guest_lines if l.lower().split(":")[0] in ("authorization", "cookie")])
        admin_lines, _ = _split(self.cb.repeater[0][3])
        self.assertIn("Authorization: Bearer admin-token", admin_lines)
        self.assertIn("Cookie: sid=orig", admin_lines)

        self.assertEqual(len(self.cb.sent), 10)  # auto-send dispatched every role clone
        self.assertTrue(_SwingUtilities.queued)   # UI updates were marshalled via invokeLater

    def test_replay_records_results(self):
        captured = []
        orig = self.ext._clone_for_roles

        def spy(group, info, roles, cfg):
            res = orig(group, info, roles, cfg)
            captured.append(group)
            return res
        self.ext._clone_for_roles = spy
        self.capture()
        g = captured[0]
        self.assertEqual(g.orig_status, 200)
        statuses = [r.status for r in g.results]
        self.assertEqual(statuses[0], 200)
        self.assertEqual(statuses[1:9], [403] * 8)
        self.assertEqual(statuses[9], 401)
        self.assertTrue(all(r.state == tm.STATE_DONE and r.sent_count == 1 for r in g.results))
        self.assertTrue(all(r.response is not None and r.elapsed_ms is not None for r in g.results))
        self.ext.replay(g, g.results[:2])
        self.assertEqual([r.sent_count for r in g.results[:3]], [2, 2, 1])
        matrix = json.loads(tm.groups_to_matrix_json([g]))
        self.assertEqual(matrix["groups"][0]["group_id"], "G01")
        self.assertEqual(matrix["groups"][0]["role_count"], 10)
        self.assertEqual(matrix["groups"][0]["roles"][0]["status"], 200)

    def test_dedup_and_filters(self):
        self.capture()
        self.capture(BASE_REQ.replace(b"?x=1", b"?x=2"))
        self.assertEqual(len(self.cb.repeater), 10)  # same endpoint deduplicated
        self.capture(source="Manual", filters=False)
        self.assertEqual(len(self.cb.repeater), 20)  # manual bypass
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/static/app.js"))
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/index.html"))
        self.capture(BASE_REQ.replace(b"POST /v1/transfer", b"OPTIONS /v1/other"))
        self.assertEqual(len(self.cb.repeater), 20)
        self.cb.in_scope = False
        self.capture(BASE_REQ.replace(b"/v1/transfer", b"/v1/accounts"))
        self.assertEqual(len(self.cb.repeater), 20)
        self.cb.in_scope = True
        self.capture(BASE_REQ.replace(b"/v1/transfer", b"/v1/accounts"))
        self.assertEqual(len(self.cb.repeater), 30)
        self.assertTrue(self.cb.repeater[-1][4].startswith("[G03:POST /v1/accounts]"))

    def test_listener_only_proxy_responses(self):
        class Msg(object):
            def __init__(s, svc):
                s.svc = svc

            def getRequest(s):
                return BASE_REQ

            def getResponse(s):
                return BASE_RESP

            def getHttpService(s):
                return s.svc
        self.ext.processHttpMessage(self.cb.TOOL_PROXY, True, Msg(self.svc))
        self.ext.processHttpMessage(self.cb.TOOL_REPEATER, False, Msg(self.svc))
        self.assertEqual(len(self.cb.repeater), 0)
        self.ext.processHttpMessage(self.cb.TOOL_PROXY, False, Msg(self.svc))
        self.assertEqual(len(self.cb.repeater), 10)

    def test_capture_disabled_and_no_roles(self):
        cfg = self.ext.get_config()
        cfg["capture_enabled"] = False
        self.ext.apply_config(cfg)

        class Msg(object):
            def getRequest(s):
                return BASE_REQ

            def getResponse(s):
                return BASE_RESP

            def getHttpService(s):
                return FakeService()
        self.ext.processHttpMessage(self.cb.TOOL_PROXY, False, Msg())
        self.assertEqual(len(self.cb.repeater), 0)
        self.ext.roles.set_all_enabled(False)
        self.capture(source="Manual", filters=False)
        self.assertEqual(len(self.cb.repeater), 0)

    def test_feature_batching_and_sequential_api_history(self):
        captured = []
        orig = self.ext._clone_for_roles

        def spy(group, info, roles, cfg):
            res = orig(group, info, roles, cfg)
            captured.append(group)
            return res
        self.ext._clone_for_roles = spy

        # Button 1: User names feature 1 "Đăng nhập & Lấy ví" -> API 1 and API 2 pass through Proxy
        self.ext.rename_feature(1, "Đăng nhập & Lấy ví")
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/login"))
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/wallet"))

        # Button 2: User switches to next feature "Chuyển tiền" -> API 3 and API 4 pass through Proxy
        f2 = self.ext.start_new_feature("Chuyển tiền")
        self.assertEqual(f2.fid, 2)
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/transfer/check"))
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/transfer/confirm"))

        self.assertEqual(len(captured), 4)
        self.assertEqual([g.gid for g in captured], [1, 2, 3, 4])
        self.assertEqual([tm.format_api_label(g.gid) for g in captured], ["API 1", "API 2", "API 3", "API 4"])
        self.assertEqual([g.fid for g in captured], [1, 1, 2, 2])
        self.assertEqual(captured[0].feature_name, "Đăng nhập & Lấy ví")
        self.assertEqual(captured[2].feature_name, "Chuyển tiền")

        # Verify formatted summary text & JSON matrix include both features and sequential APIs
        summary = tm.build_history_summary_text(self.ext.features_list(), captured)
        self.assertIn("Tổng số chức năng (Features): 2", summary)
        self.assertIn("Tổng số API đã đi qua: 4", summary)
        self.assertIn("Tên 1: Đăng nhập & Lấy ví", summary)
        self.assertIn("API 1 [G01]", summary)
        self.assertIn("API 2 [G02]", summary)
        self.assertIn("Tên 2: Chuyển tiền", summary)
        self.assertIn("API 3 [G03]", summary)
        self.assertIn("API 4 [G04]", summary)

        matrix = json.loads(tm.groups_to_matrix_json(captured, self.ext.features_list()))
        self.assertEqual(matrix["feature_count"], 2)
        self.assertEqual(matrix["features"][0]["apis"], ["API 1", "API 2"])
        self.assertEqual(matrix["features"][1]["apis"], ["API 3", "API 4"])

    def test_dedup_per_feature_and_feature_in_tab_name(self):
        cfg = self.ext.get_config()
        cfg["dedup"] = True
        cfg["dedup_per_feature"] = True
        cfg["include_feature_in_tab"] = True
        self.ext.apply_config(cfg)

        # Same endpoint in Feature 1 is deduplicated on second hit
        self.capture(BASE_REQ)
        self.capture(BASE_REQ)
        self.assertEqual(len(self.cb.repeater), 10)
        self.assertEqual(self.cb.repeater[0][4], "[F01-G01:POST /v1/transfer] 01_Admin")

        # Switching to Feature 2 allows the same endpoint to be captured again as API 2 (G02) under F02
        self.ext.start_new_feature("Nút bấm thứ 2")
        self.capture(BASE_REQ)
        self.assertEqual(len(self.cb.repeater), 20)
        self.assertEqual(self.cb.repeater[10][4], "[F02-G02:POST /v1/transfer] 01_Admin")

    def test_unicode_mojibake_healing(self):
        # Simulate UTF-8 bytes decoded as Latin-1 (as happened in Jython when str was passed to Java String)
        garbled = "Chức năng 1".encode("utf-8").decode("latin-1")
        self.assertEqual(tm.u_text(garbled), "Chức năng 1")
        self.assertEqual(tm.u_text("Đang bắt vào Tên 1:"), "Đang bắt vào Tên 1:")

    def test_role_audit_color_highlighting(self):
        captured = []
        orig = self.ext._clone_for_roles

        def spy(group, info, roles, cfg):
            res = orig(group, info, roles, cfg)
            captured.append(group)
            return res
        self.ext._clone_for_roles = spy

        # Capture & auto-replay: Admin gets 200, User2..User9 get 403, Guest gets 401
        self.capture(BASE_REQ)
        g = captured[0]

        # Because roles 2..10 failed (403/401) while Admin succeeded (200), group must be AUDIT_INFO (Yellow Info)
        g_lvl, g_sum = tm.evaluate_group_audit(g)
        self.assertEqual(g_lvl, tm.AUDIT_INFO)
        self.assertIn("INFO: 1 OK / 9 Lỗi", g_sum)

        # Check individual role assessments
        r0_lvl, r0_badge = tm.evaluate_role_result(g, g.results[0])
        self.assertEqual(r0_lvl, tm.AUDIT_OK)
        self.assertIn("OK: Thành công (200)", r0_badge)

        r1_lvl, r1_badge = tm.evaluate_role_result(g, g.results[1])
        self.assertEqual(r1_lvl, tm.AUDIT_INFO)
        self.assertIn("INFO: Không đủ quyền (403)", r1_badge)

        r9_lvl, r9_badge = tm.evaluate_role_result(g, g.results[9])
        self.assertEqual(r9_lvl, tm.AUDIT_INFO)
        self.assertIn("INFO: Chưa xác thực (401)", r9_badge)

        # If Guest unexpectedly gets 200 OK while User2..9 get 403 -> Guest row is flagged AUDIT_WARN
        g.results[9].status = 200
        g.results[9].length = g.orig_length
        rw_lvl, rw_badge = tm.evaluate_role_result(g, g.results[9])
        self.assertEqual(rw_lvl, tm.AUDIT_WARN)
        self.assertIn("WARN: Guest trả về 200!", rw_badge)

        # If all roles get 200 OK with the same length -> group is AUDIT_OK (Green)
        for r in g.results:
            r.status = 200
            r.length = 21
            r.state = tm.STATE_DONE
        g_ok_lvl, g_ok_sum = tm.evaluate_group_audit(g)
        self.assertEqual(g_ok_lvl, tm.AUDIT_OK)
        self.assertIn("OK: Cả 10 Role 2xx", g_ok_sum)

    def test_hierarchy_grouping_per_api_and_manual_recursive_send(self):
        # 1. Verify DEFAULT_CONFIG has strict manual sending by default (no auto-send, no auto-repeater)
        self.assertFalse(tm.DEFAULT_CONFIG["auto_send"])
        self.assertFalse(tm.DEFAULT_CONFIG["auto_repeater"])

        # Switch extender to default manual mode
        cfg = self.ext.get_config()
        cfg["auto_send"] = False
        cfg["auto_repeater"] = False
        self.ext.apply_config(cfg)

        # Hook group_model so captured groups are registered in headless test mode
        self.ext.group_model = tm.GroupTableModel(self.ext)
        self.ext.result_model = tm.ResultTableModel()
        orig_clone = self.ext._clone_for_roles

        def spy_clone(group, info, roles, cfg_arg):
            res = orig_clone(group, info, roles, cfg_arg)
            self.ext.group_model.add(group)
            return res

        self.ext._clone_for_roles = spy_clone

        # 2. Fast pre-filter helper extracts method & path without full request parsing
        m, p = tm.fast_extract_method_and_path(BASE_REQ)
        self.assertEqual((m, p), ("POST", "/v1/transfer?x=1"))

        # 3. Capture API 1 under "Toppage > menu > button \"Search\""
        self.ext.rename_feature(1, "Toppage > menu > button \"Search\"")
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/search?q=abc"))

        # Capture API 2 under "Toppage > menu > button \"Export\""
        self.ext.start_new_feature("Toppage > menu > button \"Export\"")
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/export"))

        # Capture API 3 under "Settings > Profile > button \"Save\""
        self.ext.start_new_feature("Settings > Profile > button \"Save\"")
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/profile/save"))

        all_groups = self.ext.group_model.all_groups()
        self.assertEqual(len(all_groups), 3)

        # Verify manual mode did NOT send any HTTP requests or Repeater tabs automatically
        self.assertEqual(len(self.cb.sent), 0)
        self.assertEqual(len(self.cb.repeater), 0)

        # 4. Verify each API group contains 1 API gốc + N (10) API roles thêm
        g1, g2, g3 = all_groups
        self.assertTrue(g1.orig_result.is_original)
        self.assertEqual(g1.orig_result.status, 200)
        self.assertEqual(len(g1.results), 10)
        self.assertEqual(len(g1.all_entries()), 11)

        self.ext.result_model.set_group(g1)
        self.assertEqual(self.ext.result_model.getRowCount(), 11)
        self.assertEqual(self.ext.result_model.getValueAt(0, 0), "GỐC")
        self.assertIn("[API GỐC]", self.ext.result_model.getValueAt(0, 1))
        self.assertEqual(self.ext.result_model.getValueAt(1, 0), "Role 1")

        # 5. Per-API Group Selection: change g3's group path via assign_group_to_path, then back
        self.ext.assign_group_to_path(g3, "Toppage > submenu > button \"QuickSave\"")
        self.assertEqual(g3.feature_name, "Toppage > submenu > button \"QuickSave\"")
        self.ext.assign_group_to_path(g3, "Settings > Profile > button \"Save\"")
        self.assertEqual(g3.feature_name, "Settings > Profile > button \"Save\"")

        # 6. Manual Recursive Send on parent group "Toppage" sends BOTH g1 and g2 (20 role requests)
        # while leaving g3 ("Settings > Profile > button \"Save\"") unsent!
        sent_groups = self.ext.replay_hierarchy_prefix("Toppage")
        self.assertEqual([g.gid for g in sent_groups], [1, 2])
        self.assertEqual(len(self.cb.sent), 20)
        self.assertTrue(all(r.state == tm.STATE_DONE for r in g1.results))
        self.assertTrue(all(r.state == tm.STATE_DONE for r in g2.results))
        self.assertTrue(all(r.state == tm.STATE_NOT_SENT for r in g3.results))

    def test_dynamic_n_level_subfolders_tree_nodes_and_compact_repeater(self):
        # 1. N-level dynamic sub-folder manipulation (1..6+ levels, not limited to 3)
        p = "Toppage"
        p = tm.append_hierarchy_segment(p, "Menu")
        p = tm.append_hierarchy_segment(p, "SubMenu > Tab 1 > Modal > Button Save")
        self.assertEqual(len(tm.split_hierarchy_path(p)), 6)
        self.assertEqual(p, "Toppage > Menu > SubMenu > Tab 1 > Modal > Button Save")

        p = tm.insert_hierarchy_segment_after(p, 1, "SubMenu_Before")
        self.assertEqual(p, "Toppage > Menu > SubMenu_Before > SubMenu > Tab 1 > Modal > Button Save")

        p = tm.replace_hierarchy_segment_at(p, 2, "RenamedSub")
        self.assertEqual(p, "Toppage > Menu > RenamedSub > SubMenu > Tab 1 > Modal > Button Save")

        p = tm.delete_hierarchy_segment_at(p, 2)
        self.assertEqual(p, "Toppage > Menu > SubMenu > Tab 1 > Modal > Button Save")

        p = tm.pop_hierarchy_segment(p)
        self.assertEqual(p, "Toppage > Menu > SubMenu > Tab 1 > Modal")

        # Prefix rename preserves all deeper sub-folders
        renamed = tm.replace_hierarchy_prefix(p, "Toppage > Menu", "Portal > Nav")
        self.assertEqual(renamed, "Portal > Nav > SubMenu > Tab 1 > Modal")

        # 2. Verify HierarchyTreeNode str/repr/toString never renders '<_TreeNodeItem object at 0x...>'
        node = tm.HierarchyTreeNode("FOLDER", "Toppage > Menu", "[Cấp 2] Menu (5 API)")
        self.assertEqual(str(node), "[Cấp 2] Menu (5 API)")
        self.assertEqual(repr(node), "[Cấp 2] Menu (5 API)")
        self.assertEqual(node.toString(), "[Cấp 2] Menu (5 API)")
        self.assertEqual(tm.BurpExtender._extract_node_kind_payload(node), ("FOLDER", "Toppage > Menu"))

        # 3. Verify compact Repeater tab naming & dispatch
        self.assertEqual(tm.compact_repeater_tab_name(1, "01_Admin"), "G01•01_Admin")
        self.assertEqual(tm.compact_repeater_tab_name(1, "01_Admin", fid=2, include_feature=True), "F02•G01•01_Admin")

        cfg = self.ext.get_config()
        cfg["auto_send"] = False
        cfg["auto_repeater"] = False
        self.ext.apply_config(cfg)

        captured = []
        orig_clone = self.ext._clone_for_roles

        def spy_clone(group, info, roles, cfg_arg):
            res = orig_clone(group, info, roles, cfg_arg)
            captured.append(group)
            return res

        self.ext._clone_for_roles = spy_clone
        self.capture(BASE_REQ)
        g = captured[0]
        self.ext.send_to_repeater(g, g.results, compact=True, copy_group_name=False)
        self.assertEqual(len(self.cb.repeater), 10)
        self.assertEqual(self.cb.repeater[0][4], "G01•01_Admin")
        self.assertEqual(self.cb.repeater[-1][4], "G01•10_Guest")

    def test_init_ui_builds_cleanly(self):
        self.ext._init_ui()
        errors = [x for x in self.cb.out if str(x).startswith("ERROR:")]
        self.assertEqual(errors, [])
        self.assertIs(getattr(self.cb, "tab", None), self.ext)
        self.assertIsNotNone(self.ext.getUiComponent())
        self.assertEqual(self.ext.getTabCaption(), "theMythOfCrawl")

    def test_init_ui_registers_fallback_tab_when_build_ui_fails(self):
        def broken_build():
            raise RuntimeError("Lỗi UI: Đường dẫn Nhánh 1 > Nhánh 2")

        self.ext._build_ui = broken_build
        self.cb.tab = None
        self.ext._init_ui()
        self.assertIs(getattr(self.cb, "tab", None), self.ext)
        self.assertIsNotNone(self.ext.getUiComponent())
        errors = [x for x in self.cb.out if str(x).startswith("ERROR:")]
        self.assertTrue(any("Error building UI:" in str(e) for e in errors))

    def test_init_ui_survives_customize_ui_component_failure(self):
        orig = self.cb.customizeUiComponent

        def broken_theme(comp):
            raise RuntimeError("FlatLaf customize failure")

        self.cb.customizeUiComponent = broken_theme
        try:
            self.ext._init_ui()
        finally:
            self.cb.customizeUiComponent = orig
        self.assertIs(getattr(self.cb, "tab", None), self.ext)
        self.assertIsNotNone(self.ext.getUiComponent())

    def test_task_handles_utf8_and_bytes_exceptions(self):
        def broken_task():
            raise RuntimeError("Lỗi tiếng Việt trong task: Chế độ & Lọc")

        logs = []
        tm._Task(broken_task, log_fn=logs.append).run()
        self.assertEqual(len(logs), 1)
        self.assertIn("Unhandled exception in task:", logs[0])
        self.assertIn("RuntimeError", logs[0])

    def test_swing_constructors_avoid_jython_unsafe_listener_kwargs(self):
        import ast
        src_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), "theMythOfCrawl.py")
        with open(src_path, "rb") as fh:
            tree = ast.parse(fh.read().decode("utf-8"))
        unsafe = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                fname = node.func.id
                kw_names = {kw.arg for kw in node.keywords if kw.arg}
                if fname == "JComboBox" and "actionPerformed" in kw_names:
                    unsafe.append((node.lineno, fname, "actionPerformed"))
                if fname == "JTextField" and "actionPerformed" in kw_names:
                    unsafe.append((node.lineno, fname, "actionPerformed"))
                if fname == "JSpinner" and "stateChanged" in kw_names:
                    unsafe.append((node.lineno, fname, "stateChanged"))
        self.assertEqual(unsafe, [])

    def test_hierarchy_tree_node_and_renderer_safety(self):
        node = tm.HierarchyTreeNode("ROOT", "", "Tất cả Group & API", audit_level=tm.AUDIT_NONE)
        self.assertEqual(node.label, "Tất cả Group & API")
        self.assertEqual(node.toString(), "Tất cả Group & API")
        renderer = tm.HierarchyTreeRenderer()
        non_sel_bg_calls = []
        renderer.setBackgroundNonSelectionColor = lambda c: non_sel_bg_calls.append(c)
        renderer.setTextNonSelectionColor = lambda c: None
        mock_tree = type("MockTree", (object,), {"getBackground": lambda self: None})()
        comp = renderer.getTreeCellRendererComponent(mock_tree, node, False, False, False, 0, False)
        self.assertIsNotNone(comp)
        self.assertEqual(non_sel_bg_calls, [])



class _ManualExecutor(object):
    def __init__(self):
        self.tasks = []

    def execute(self, task):
        self.tasks.append(task)


class _Grp(object):
    def __init__(self, host="a.test"):
        self.protocol, self.host, self.port = "https", host, 443


class DispatcherTests(unittest.TestCase):
    """Per-host pacing, 429 / Retry-After handling, retries and cancellation (fake clock)."""

    def setUp(self):
        self.now = [100.0]
        self.cfg = {"send_delay_ms": 1000, "send_jitter_pct": 0, "host_concurrency": 1, "max_retries": 2}
        self.ran = []
        self.ex = _ManualExecutor()
        self.sched = _RecordingScheduler()
        self.d = tm.SendDispatcher(self.ran.append, self.ex, self.sched, lambda: dict(self.cfg),
                                   clock=lambda: self.now[0], rand=lambda: 0.5)

    def jobs(self, n, host="a.test"):
        g = _Grp(host)
        return [tm._SendJob(g, object()) for _ in range(n)]

    def run_dispatched(self):
        tasks, self.ex.tasks = self.ex.tasks, []
        for t in tasks:
            t.run()
        out, self.ran[:] = list(self.ran), []
        return out

    def fire_scheduled(self):
        tasks, self.sched.tasks = self.sched.tasks, []
        for _, t in tasks:
            t.run()

    def test_one_at_a_time_with_human_gap(self):
        jobs = self.jobs(3)
        self.d.submit(jobs)
        self.assertEqual(self.run_dispatched(), [jobs[0]])
        self.now[0] = 100.3
        self.assertTrue(self.d.done(jobs[0], 200))
        self.assertEqual(self.run_dispatched(), [])      # gap counted from the answer
        self.assertEqual(len(self.sched.tasks), 1)
        self.assertAlmostEqual(self.sched.tasks[0][0], 1001, delta=2)
        self.now[0] = 101.31
        self.fire_scheduled()
        self.assertEqual(self.run_dispatched(), [jobs[1]])

    def test_hosts_are_independent(self):
        a = self.jobs(1, "a.test")
        b = self.jobs(1, "b.test")
        self.d.submit(a + b)
        self.assertEqual(self.run_dispatched(), a + b)

    def test_429_pauses_host_honours_retry_after_and_retries(self):
        jobs = self.jobs(2)
        self.d.submit(jobs)
        self.run_dispatched()
        self.assertTrue(self.d.will_retry(jobs[0], 429))
        self.assertFalse(self.d.done(jobs[0], 429, retry_after=5.0))
        queued, inflight, penalty, wait = self.d.snapshot()
        self.assertEqual((queued, inflight, penalty), (2, 0, 2.0))
        self.assertAlmostEqual(wait, 5.0, delta=0.01)
        self.now[0] = 104.0
        self.fire_scheduled()
        self.assertEqual(self.run_dispatched(), [])      # still paused
        self.now[0] = 105.01
        self.fire_scheduled()
        self.assertEqual(self.run_dispatched(), [jobs[0]])  # retried first, before the next request
        self.assertEqual(jobs[0].retries, 1)

    def test_backoff_without_retry_after_and_retry_limit(self):
        job = self.jobs(1)[0]
        self.d.submit([job])
        for attempt in range(3):
            self.run_dispatched()
            finished = self.d.done(job, 503)
            self.now[0] += 100
            self.fire_scheduled()
        self.assertTrue(finished)                        # gave up after max_retries
        self.assertEqual(job.retries, 2)
        self.assertEqual(self.d.snapshot()[2], 8.0)       # 3 x 503 -> 8x slower

    def test_recovers_speed_after_successes(self):
        jobs = self.jobs(1 + tm.SendDispatcher.RECOVER_AFTER)
        self.d.submit(jobs)
        self.run_dispatched()
        self.d.done(jobs[0], 429, retry_after=0.0)
        for j in range(tm.SendDispatcher.RECOVER_AFTER + 1):
            self.now[0] += 60
            self.fire_scheduled()
            for job in self.run_dispatched():
                self.d.done(job, 200)
        self.assertEqual(self.d.snapshot()[2], 1.0)

    def test_cancel_all_drops_only_queued(self):
        jobs = self.jobs(4)
        self.d.submit(jobs)
        self.run_dispatched()
        dropped = self.d.cancel_all()
        self.assertEqual(dropped, jobs[1:])
        self.assertEqual(self.d.snapshot()[:2], (0, 1))

    def test_parse_retry_after(self):
        self.assertEqual(tm.parse_retry_after(["HTTP/1.1 429 Too Many", "Retry-After: 7"]), 7.0)
        self.assertEqual(tm.parse_retry_after(["retry-after:  99999"]), 300.0)
        self.assertIsNone(tm.parse_retry_after(["X-Other: 1"]))
        now = 1700000000.0
        self.assertAlmostEqual(tm.parse_retry_after(["Retry-After: Tue, 14 Nov 2023 22:13:30 GMT"], now=now),
                               10.0, delta=1.0)


class SendModeAndExportTests(unittest.TestCase):
    setUp = EngineTests.setUp
    capture = EngineTests.capture

    def test_stop_sending_cancels_queue_and_keeps_crawling(self):
        cfg = self.ext.get_config()
        cfg.update({"send_profile": "CUSTOM", "send_delay_ms": 5000, "auto_repeater": False})
        self.ext.apply_config(cfg)
        groups = []
        orig = self.ext._clone_for_roles
        self.ext._clone_for_roles = lambda g, i, r, c: (groups.append(g), orig(g, i, r, c))[1]
        self.capture()
        g = groups[0]
        self.assertEqual(g.results[0].state, tm.STATE_DONE)            # first request went out
        self.assertEqual([r.state for r in g.results[1:]], [tm.STATE_QUEUED] * 9)  # rest paced
        cfg = self.ext.get_config()
        cfg["auto_send"] = False
        self.ext.apply_config(cfg)                                   # STOP
        self.assertEqual([r.state for r in g.results[1:]], [tm.STATE_NOT_SENT] * 9)
        self.assertEqual(self.ext.dispatcher.snapshot()[0], 0)
        self.capture(BASE_REQ.replace(b"/v1/transfer", b"/v1/other"))  # still crawls ...
        self.assertEqual(len(groups), 2)
        self.assertTrue(all(r.state == tm.STATE_NOT_SENT for r in groups[1].results))  # ... but sends nothing
        self.assertEqual(len(self.cb.sent), 1)

    def test_429_marks_retry_and_resends(self):
        calls = []
        real = self.cb.makeHttpRequest

        def limited(service, req):
            calls.append(req)
            if len(calls) == 1:
                return FakeRR(b"HTTP/1.1 429 Too Many Requests\r\nRetry-After: 3\r\n\r\nslow down")
            return real(service, req)
        self.cb.makeHttpRequest = limited
        clock = [1000.0]
        self.ext.dispatcher._clock = lambda: clock[0]
        groups = []
        orig = self.ext._clone_for_roles
        self.ext._clone_for_roles = lambda g, i, r, c: (groups.append(g), orig(g, i, r, c))[1]
        self.capture()
        admin = groups[0].results[0]
        self.assertEqual(admin.state, tm.STATE_RETRY)
        self.assertEqual(admin.status, 429)
        self.assertEqual(len(calls), 1)                               # whole host paused
        clock[0] += 3.1
        for _, task in list(self.ext.send_scheduler.tasks):
            task.run()
        self.assertEqual(admin.state, tm.STATE_DONE)
        self.assertEqual(admin.status, 200)
        self.assertEqual(len(calls), 11)                              # 1 x 429 + 10 roles

    def test_excel_export_is_valid_xlsx(self):
        import io as _io
        import zipfile
        import xml.etree.ElementTree as ET
        groups = []
        orig = self.ext._clone_for_roles
        self.ext._clone_for_roles = lambda g, i, r, c: (groups.append(g), orig(g, i, r, c))[1]
        self.ext.rename_feature(1, '/ > contact > button "a"')
        self.capture()
        data = tm.build_api_workbook(groups)
        z = zipfile.ZipFile(_io.BytesIO(data))
        names = set(z.namelist())
        for part in ("[Content_Types].xml", "_rels/.rels", "xl/workbook.xml", "xl/_rels/workbook.xml.rels",
                     "xl/styles.xml", "xl/worksheets/sheet1.xml", "xl/worksheets/sheet2.xml"):
            self.assertIn(part, names)
        ns = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}

        def rows(part):
            root = ET.fromstring(z.read(part))
            out = []
            for row in root.findall(".//m:sheetData/m:row", ns):
                vals = []
                for c in row.findall("m:c", ns):
                    t = c.find(".//m:t", ns)
                    v = c.find("m:v", ns)
                    vals.append(t.text if t is not None else (v.text if v is not None else None))
                out.append(vals)
            return out
        api = rows("xl/worksheets/sheet1.xml")
        self.assertEqual(api[0][:4], ["STT", "Method", "Path", "Vị trí tìm thấy"])
        self.assertEqual(api[1][:4], ["1", "POST", "/v1/transfer", '/ > contact > button "a"'])
        roles = rows("xl/worksheets/sheet2.xml")
        self.assertEqual(len(roles), 11)
        self.assertEqual(roles[1][5], "01_Admin")
        wb = ET.fromstring(z.read("xl/workbook.xml"))
        self.assertEqual([s.get("name") for s in wb.findall(".//m:sheet", ns)], ["API", "Kết quả Role"])

    def test_log_lines_are_filed_per_api(self):
        self.ext._flush_log([("10:00:00", "Bắt từ Proxy", 7), ("10:00:01", "Chế độ gửi", None)])
        self.assertEqual(self.ext._log_by_gid[7], [("10:00:00", "Bắt từ Proxy")])
        self.assertEqual(list(self.ext._log_system)[-1], ("10:00:01", "Chế độ gửi"))


def _xlsx_with_shared_strings(rows):
    """Workbook laid out like Excel writes it (shared strings + numeric cells), for reader tests."""
    import io as _io
    import zipfile
    strings = []
    xml_rows = []
    for r, row in enumerate(rows, 1):
        cells = []
        for c, v in enumerate(row):
            ref = "%s%d" % (chr(65 + c), r)
            if v is None:
                continue
            if isinstance(v, int):
                cells.append('<c r="%s"><v>%d</v></c>' % (ref, v))
            else:
                strings.append(v)
                cells.append('<c r="%s" t="s"><v>%d</v></c>' % (ref, len(strings) - 1))
        xml_rows.append('<row r="%d">%s</row>' % (r, "".join(cells)))
    ns = 'xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"'
    rel = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
    buf = _io.BytesIO()
    z = zipfile.ZipFile(buf, "w")
    z.writestr("xl/workbook.xml", '<workbook %s xmlns:r="%s"><sheets><sheet name="APIs" sheetId="1" r:id="rId9"/>'
               '</sheets></workbook>' % (ns, rel))
    z.writestr("xl/_rels/workbook.xml.rels",
               '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
               '<Relationship Id="rId9" Type="%s/worksheet" Target="worksheets/data.xml"/></Relationships>' % rel)
    z.writestr("xl/sharedStrings.xml", ('<sst %s>' % ns) + "".join(
        ['<si><t>%s</t></si>' % s.replace("&", "&amp;").replace("<", "&lt;") for s in strings]) + '</sst>')
    z.writestr("xl/worksheets/data.xml", '<worksheet %s><sheetData>%s</sheetData></worksheet>' % (ns, "".join(xml_rows)))
    z.close()
    return buf.getvalue()


class ExcelTargetTests(unittest.TestCase):
    DEMO = [["STT", "PROTOCOL", "PATH", "POSITION"],
            [1, "GET", "/apt/test"], [2, "POST", "/apt/test"],
            [5, "GET", "/apt/test/{id}/me/{session}"], [6, "post", "/apt/test/[id]/me/(sid)"],
            [7, "", "https://x.test/files/<f>.json?v=1", 'Toppage > contact > button "search"']]

    def write(self, rows):
        import tempfile
        fd, path = tempfile.mkstemp(suffix=".xlsx")
        os.write(fd, _xlsx_with_shared_strings(rows))
        os.close(fd)
        self.addCleanup(os.remove, path)
        return path

    def test_reads_shared_strings_and_detects_columns(self):
        path = self.write(self.DEMO)
        self.assertEqual(tm.xlsx_sheet_names(path), ["APIs"])
        sheet, rows = tm.read_xlsx_rows(path)
        self.assertEqual(sheet, "APIs")
        tl = tm.build_target_list(rows, "demo.xlsx", sheet)
        self.assertEqual(tl.headers, ["STT", "PROTOCOL", "PATH", "POSITION"])
        self.assertEqual([e.stt for e in tl.entries], [1, 2, 5, 6, 7])
        self.assertEqual(tl.entries[3].methods, ["POST"])
        self.assertEqual(tl.entries[4].methods, ["ANY"])
        self.assertEqual(tl.entries[4].position, 'Toppage > contact > button "search"')

    def test_vietnamese_headers_and_headerless_files(self):
        tl = tm.build_target_list([["Số thứ tự", "Phương thức", "Đường dẫn", "Vị trí"], [1, "GET, PUT", "/a/b"]])
        self.assertEqual(tl.entries[0].methods, ["GET", "PUT"])
        tl = tm.build_target_list([[1, "DELETE", "/x/{id}", "/ > c"], [2, "GET", "/y"]])
        self.assertEqual([e.path for e in tl.entries], ["/x/{id}", "/y"])
        self.assertEqual(tl.entries[0].position, "/ > c")

    def test_any_bracket_style_is_a_wildcard_segment(self):
        tl = tm.build_target_list(self.DEMO)
        self.assertEqual(tl.match("GET", "/apt/test/").stt, 1)
        self.assertEqual(tl.match("GET", "/apt/test/42/me/s3ss10n?x=1").stt, 5)
        self.assertEqual(tl.match("POST", "/APT/TEST/42/me/abc").stt, 6)
        self.assertEqual(tl.match("PATCH", "/files/report.json").stt, 7)
        self.assertIsNone(tl.match("PATCH", "/apt/test"))
        self.assertIsNone(tl.match("GET", "/apt/test/42/me"))
        self.assertIsNone(tl.match("GET", "/api/v1/apt/test"))
        self.assertEqual(tl.match("GET", "/api/v1/apt/test", allow_prefix=True).stt, 1)
        tl2 = tm.TargetList.from_json(tl.to_json())
        self.assertEqual(tl2.match("GET", "/apt/test/1/me/2").stt, 5)

    def test_literal_rows_beat_templates(self):
        tl = tm.build_target_list([["STT", "METHOD", "PATH"], [1, "GET", "/u/{id}"], [2, "GET", "/u/me"]])
        self.assertEqual(tl.match("GET", "/u/me").stt, 2)
        self.assertEqual(tl.match("GET", "/u/42").stt, 1)

    def test_rejects_xml_with_doctype(self):
        import io as _io
        import zipfile
        buf = _io.BytesIO()
        z = zipfile.ZipFile(buf, "w")
        z.writestr("xl/workbook.xml", '<?xml version="1.0"?><!DOCTYPE x [<!ENTITY a "b">]><workbook/>')
        z.close()
        path = self.write([])
        with open(path, "wb") as fh:
            fh.write(buf.getvalue())
        with self.assertRaises(ValueError):
            tm.read_xlsx_rows(path)


class TargetCaptureTests(unittest.TestCase):
    setUp = EngineTests.setUp
    capture = EngineTests.capture

    def groups(self):
        out = []
        orig = self.ext._clone_for_roles
        self.ext._clone_for_roles = lambda g, i, r, c: (out.append(g), orig(g, i, r, c))[1]
        return out

    def test_target_only_mode_skips_unlisted_and_files_by_position(self):
        tl = tm.build_target_list([["STT", "PROTOCOL", "PATH", "POSITION"],
                                   [1, "POST", "/v1/transfer/{id}", '/ > contact > button "search"'],
                                   [2, "GET", "/v1/other"]])
        self.ext.targets = tl
        cfg = self.ext.get_config()
        cfg.update({"target_only": True, "api_regex_enabled": True, "api_regex": "^/never$"})
        self.ext.apply_config(cfg)
        groups = self.groups()
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/transfer/77?x=1"))
        self.capture(BASE_REQ.replace(b"/v1/transfer?x=1", b"/v1/unlisted"))
        self.assertEqual(len(groups), 1)                       # regex ignored, unlisted skipped
        self.assertIs(groups[0].target, tl.entries[0])
        self.assertEqual(groups[0].feature_name, '/ > contact > button "search"')
        rows = tm.coverage_export_rows(tl, groups)
        self.assertEqual(rows[0][:5], [1, "POST", "/v1/transfer/{id}", '/ > contact > button "search"', "Đã bắt"])
        self.assertEqual(rows[1][4], "Chưa bắt")

    def test_list_without_target_mode_only_tags(self):
        tl = tm.build_target_list([["STT", "METHOD", "PATH"], [3, "POST", "/v1/transfer"]])
        self.ext.targets = tl
        groups = self.groups()
        self.capture()
        self.capture(BASE_REQ.replace(b"/v1/transfer", b"/v1/elsewhere"))
        self.assertEqual(len(groups), 2)
        self.assertIs(groups[0].target, tl.entries[0])
        self.assertIsNone(groups[1].target)
        rows = tm.coverage_export_rows(tl, groups)
        self.assertEqual(rows[0][2], "/v1/transfer")
        self.assertEqual(rows[0][3], tm.DEFAULT_HIERARCHY_PATH)  # empty POSITION filled with where it was found

if __name__ == "__main__":
    unittest.main()
