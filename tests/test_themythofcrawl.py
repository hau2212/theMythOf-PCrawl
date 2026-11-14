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


class _Executors(object):
    @staticmethod
    def newSingleThreadExecutor():
        return _SyncExecutor(1)

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
        self.assertIsNotNone(self.ext.getUiComponent())
        self.assertEqual(self.ext.getTabCaption(), "theMythOfCrawl")


if __name__ == "__main__":
    unittest.main()
