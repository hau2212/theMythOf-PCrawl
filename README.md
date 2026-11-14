# theMythOfCrawl

A Burp Suite Professional extension for **multi-role API request cloning** and **grouped Repeater dispatching**. It's built for authorization and access-control testing (BOLA/IDOR, privilege escalation, tenant isolation) on applications you are authorized to test.

For every API endpoint it matches, the extension makes **one copy of the request per enabled role**. Each copy gets that role's headers. The copies are kept together as a group in the extension's own UI and in Burp Repeater. They can also be replayed in the background so you can compare status codes and response lengths side by side.

- Language: Python (Jython 2.7), legacy Extender API (`IBurpExtender`, `ITab`, `IHttpListener`, `IContextMenuFactory`, `IExtensionStateListener`, `IMessageEditorController`)
- Single file: [`theMythOfCrawl.py`](theMythOfCrawl.py). No build step.

---

## 1. Setup

1. **Get Jython standalone.** Download `jython-standalone-2.7.3.jar` (or newer 2.7.x) from https://www.jython.org/download.
2. **Point Burp at Jython.** Go to Burp → **Extensions → Extensions settings** (older builds: *Extender → Options*) → **Python environment** → *Location of Jython standalone JAR file* → select the jar.
3. **Load the extension.** Go to **Extensions → Installed → Add**:
   - Extension type: **Python**
   - Extension file: `theMythOfCrawl.py`
4. A new top-level tab, **theMythOfCrawl**, appears. The *Output* tab of the extension should show `theMythOfCrawl 1.0.0 loaded`.
5. Your roles and settings are saved automatically with `saveExtensionSetting` and come back when you reload the extension or restart Burp.

> Proxy capture is **OFF by default**. Turn on **Capture Proxy traffic** in the top bar once your roles are configured.

---

## 2. Workflow

### 2.1 Configure roles (tab **Roles**)

| Action | Description |
|---|---|
| Add / Edit / Duplicate / Delete | Manage any number of roles (double-click a row to edit) |
| Enabled checkbox | Only enabled roles are cloned. Toggle directly in the table |
| Move Up / Down | The order sets the clone order, the `01_`, `02_` … numbers, and the Repeater tab order |
| Enable All / Disable All | Bulk toggle |
| Import JSON / Export JSON | Import lets you **Replace** or **Append** |

Each role holds a list of **header rules**, applied in order:

| Mode | Behavior |
|---|---|
| `REPLACE` (default) | Overwrites the header if it exists (duplicates with the same name are collapsed into one), otherwise adds it |
| `ADD` | Always appends a new header line, even if the header already exists |
| `REMOVE`, or a value of `[REMOVE]` | Removes **every** occurrence of the header (name matching ignores case) |

The editor's **Bulk Paste Headers…** button accepts raw `Name: value` lines, for example lines copied from a logged-in request. CR/LF characters are removed from values, and header names with spaces or colons are rejected.

JSON format (see [`roles.example.json`](roles.example.json) for a 10-role template):

```json
{
  "extension": "theMythOfCrawl",
  "version": 1,
  "roles": [
    {"name": "01_Admin", "enabled": true, "headers": [
      {"name": "Authorization", "value": "Bearer eyJ...", "mode": "REPLACE"},
      {"name": "X-Role", "value": "admin", "mode": "REPLACE"}]},
    {"name": "10_Guest", "enabled": true, "headers": [
      {"name": "Authorization", "value": "[REMOVE]", "mode": "REMOVE"}]}
  ]
}
```

Import also accepts a bare list of roles. In that case `headers` can be a list of objects, a `{"Header": "value"}` map, or a list of `"Header: value"` strings.

### 2.2 Capture filters (tab **Capture Filters & Options**)

Filters apply to **Proxy** traffic. Each request is captured when its response arrives, so the request is in its final state after any interception edits, and the original response is recorded as the baseline:

- **In-Scope Only**: uses Burp's Target → Scope.
- **Ignore Static Extensions**: comma-separated list you can edit (`js, css, png, woff2, …`).
- **API Path Regex**: Python regex searched against the path without the query string. The default matches `/api/`, `/vN/`, `/graphql`, `/rest/`, `/rpc/`, `/service(s)/` and `*.json`. If the regex is invalid, a red warning appears and the regex filter is turned off until you fix it.
- **Ignore OPTIONS / HEAD**: skips CORS preflight requests.
- **Deduplicate (Method + Host + Path)**: each endpoint is cloned only once per session. The key is `METHOD|scheme://host:port|path` and ignores the query string. You can also have numeric, UUID and long-hex path segments treated as `{id}` (so `/users/1` and `/users/2` count as the same endpoint). Use **Reset Dedup Cache** on the API Groups tab to start over.

Text fields take effect when you press **Enter** or click **Apply Text Fields**. Checkboxes and spinners take effect immediately.

**Manual trigger:** right-click one or more messages anywhere Burp offers a message context menu (Proxy history, Target site map, Repeater, Logger, …):
- `theMythOfCrawl: Clone to all enabled roles`: **skips** all filters and dedup.
- `theMythOfCrawl: Clone to all enabled roles (apply capture filters + dedup)`: applies the filters and dedup.

### 2.3 Cloning, Repeater, replay

For each matched request with N enabled roles, the extension builds exactly N requests. The method, request line (path and query), body and all other headers stay the same. Content-Length is recalculated by Burp's `buildHttpMessage`.

Top bar toggles:
- **Auto-send new groups to Repeater** (on by default): every new group is sent to Repeater as N tabs named
  `[G<GroupID>:<METHOD> <ShortPath>] <RoleName>`, for example `[G01:POST /v1/transfer] 01_Admin` … `[G01:POST /v1/transfer] 10_Guest`.
  - If a role name doesn't already start with a number prefix, the extension adds `NN_` (you can turn this off).
  - Long paths are shortened from the left (`.../deep/path`). The maximum length is configurable.
  - Group IDs keep counting up even after **Clear All**, so tab names never collide.
- **Auto-Send to Server & Record**: all N requests are sent on background worker threads. For each role the extension records the state, HTTP status, response body length, the difference from the original response's length, time in ms, how many times it was sent, and the full request/response.

Tuning: **Replay worker threads** (1–64, resized live) and **Throttle per request (ms)**.

> With auto-Repeater on during a large crawl, Repeater fills up quickly (endpoints × roles tabs). Keep dedup on, narrow the regex and scope, or turn auto-Repeater off and send groups manually.

### 2.4 Master-Detail view (tab **API Groups**)

- **Top table (groups):** Group ID, source (Proxy/Manual), time, method, host, path, original status and length, **Role Count**, replay progress. Columns can be sorted, and you can select several rows.
- **Middle table (roles of the selected group):** role, state, status (color-coded), body length, Δ vs original, time, sends, and the Repeater tab name or error.
- **Bottom:** read-only Burp request/response viewers for the selected role.

| Button | Effect |
|---|---|
| **Send Entire Group to Repeater** | All role requests of each selected group (or double-click a group) |
| **Send Selected Role to Repeater** | The selected role row(s) (or double-click a role) |
| **Replay All N Roles to Server** | Re-sends every role of each selected group in the background and updates the results |
| Replay Selected Role(s) | Re-sends only the selected rows |
| Rebuild with Current Roles | Re-clones the group's original request using the roles as they are now (after you edit tokens) |
| Delete Group(s) / Clear All / Reset Dedup Cache | Housekeeping |

How to read results: a low-privilege role that gets a `2xx` with a body length close to the admin's (small Δ) on a privileged endpoint is a candidate authorization flaw. Check it by hand in the Repeater tab group.

---

## 3. Threading & safety design

| Concern | Implementation |
|---|---|
| Burp proxy threads | `processHttpMessage` only copies the request/response bytes and queues work. It never blocks or touches Swing |
| Group building | A single-thread capture executor gives deterministic group IDs, race-free dedup and ordered Repeater dispatch |
| Network I/O | A resizable `FixedThreadPool` runs `makeHttpRequest`. Nothing network-related runs on the EDT |
| UI updates | All Swing changes go through `ui_call()` → `SwingUtilities.invokeLater`. Table models are only touched on the EDT |
| Shared state | Roles live in a lock-guarded `RoleStore` that returns deep copies. Config, dedup set and the ID counter use `RLock` |
| Recursion | Requests the extension sends itself (`TOOL_EXTENDER`) and Repeater traffic are never captured. Only `TOOL_PROXY` responses are |
| Unload | `IExtensionStateListener` shuts down both executors |
| Header injection | Header names are validated. CR/LF is removed from values |

---

## 4. Offline tests

The pure logic and the capture → clone → Repeater → replay engine are tested under CPython 3, with stubs standing in for Burp and Java (the Swing UI needs a real Burp/JVM):

```powershell
python -m unittest discover -s tests -v
```

---

## 5. Troubleshooting

| Symptom | Fix |
|---|---|
| Extension type "Python" is greyed out | Set the Jython standalone JAR path (step 2) |
| Nothing is captured | Turn on *Capture Proxy traffic*. Check the scope, the API regex and that at least one role is enabled. Endpoints already seen are skipped by dedup (use *Reset Dedup Cache*) |
| Manual clone does nothing | At least one role must be enabled. See the **Log** tab |
| Replay rows show `Error / No response` | Timeout or connection failure. Lower the thread count and add throttling |
| Too many Repeater tabs | Turn off *Auto-send new groups to Repeater* and send groups manually |

