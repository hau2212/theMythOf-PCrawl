# theMythOfCrawl

A Burp Suite Professional extension for **multi-role API request cloning** and **grouped Repeater dispatching**. It's built for authorization and access-control testing (BOLA/IDOR, privilege escalation, tenant isolation) on applications you are authorized to test.

For every API endpoint it matches, the extension makes **one copy of the request per enabled role**. Each copy gets that role's headers. The copies are kept together as a group in the extension's own UI and in Burp Repeater. They can also be replayed in the background so you can compare status codes and response lengths side by side.

- Language: Python (Jython 2.7), legacy Extender API (`IBurpExtender`, `ITab`, `IHttpListener`, `IContextMenuFactory`, `IExtensionStateListener`, `IMessageEditorController`)
- Single file: [`theMythOfCrawl.py`](theMythOfCrawl.py). No build step.

---

## 1. Setup

> **Từ v1.11 extension gồm 2 file: `theMythOfCrawl.py` (file nạp vào Burp) và `tmoc_core.py`.**
> Giữ 2 file trong cùng một thư mục (cứ `git pull` cả repo) và chỉ chọn `theMythOfCrawl.py` khi Add extension.
> Lý do: Jython biên dịch mỗi file .py thành một class Java, và một class không được vượt giới hạn kích thước của JVM.

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
| Load 10-Role Template | Instantly populates 10 starter roles (`01_Admin` … `10_Guest`) with Replace or Append |

Each role holds a list of **header / cookie / JWT rules**, applied in order. You can edit any role either **inline on the right-hand side of the Roles tab** (and click **Save Profile Changes**) or by double-clicking a row to open the modal editor:

| Mode | Behavior |
|---|---|
| `REPLACE` (default) | Overwrites the HTTP header if it exists (duplicates with the same name are collapsed into one), otherwise adds it |
| `ADD` | Always appends a new HTTP header line, even if the header already exists |
| `REMOVE`, or a value of `[REMOVE]` | Removes **every** occurrence of the HTTP header (name matching ignores case) |
| `COOKIE_SET` | Sets or overwrites a **single cookie/session key** (`name=value`) inside the `Cookie:` header while keeping all other cookies intact (creates `Cookie:` if missing) |
| `COOKIE_REMOVE` (or `COOKIE_SET` with `[REMOVE]`) | Strips a **single cookie/session key** from the `Cookie:` header while keeping all other cookies intact (removes the `Cookie:` header if no cookies remain) |

Quick-action helpers in the Role Editor:
- **+ Set JWT / Bearer...**: Paste a raw JWT or Bearer token (or `[REMOVE]`), choose the header name (default `Authorization`) and prefix (default `Bearer`, or leave empty for raw token). The built-in **JWT / Token Inspector** automatically base64url-decodes any `eyJ...` token in the profile and displays its `Header` and `Payload` (`sub`, `role`, `exp`, etc.).
- **+ Set Cookie/Session Key...** & **+ Strip Cookie Key...**: Add `COOKIE_SET` / `COOKIE_REMOVE` rules for individual session keys (`JSESSIONID`, `session`, `sid`, etc.) without clobbering other cookies.
- **Paste Headers...** & **Paste Cookies...**: Bulk-import raw `Header: value` lines or `Cookie: a=1; b=2` strings. CR/LF characters are stripped from values, and invalid names are rejected.

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

### 2.3 Cloning (`1 API Gốc + N Roles`), Manual Recursive Sending & Repeater

For each matched API request with $N$ enabled roles, the extension stores:
- **`1 API Gốc` (`[API GỐC] 00_Original (Acc Crawl)` — Row 0 (`GỐC`) in the detail table):** The exact baseline request & response from the main account used during crawling.
- **`N API Roles thêm` (`01_Admin` … `10_Guest` — Rows `Role 1` … `Role N`):** $N$ cloned requests with each role's custom JWT/Bearer, Cookie/Session key rules (`COOKIE_SET` / `COOKIE_REMOVE`), or HTTP Header rules (`REPLACE` / `ADD` / `REMOVE`).

**Default Mode is Strictly Manual (Anti-Lag & Safe Crawling):**
- By default, **both** `Cho phép Tự động Gửi ngầm (auto_send)` and `Tự động đẩy Repeater (auto_repeater)` are **OFF (`False`)**.
- During crawling, APIs are captured and cloned into memory (`Not sent`) without spamming the target server or creating hundreds of Burp Repeater tabs.
- You manually trigger sending at **any level**:
  - **Parent / Sub-Folder Group (`▶ Gửi Nhánh/Group đang chọn`, e.g. `Toppage` or `Toppage > menu`):** Recursively sends **all** APIs inside that folder and all its nested sub-folders (`button "Search"`, `button "Export"`, etc.).
  - **Single API (`▶ Gửi API đang chọn (N Roles)`):** Sends all $N$ role requests of the selected API(s).
  - **Single Role (`▶ Gửi lại Role đang chọn`):** Sends only the selected role row(s).
- If you explicitly want automatic background replay or automatic Repeater tab creation, check `Cho phép Tự động Gửi ngầm` or `Tự động đẩy Repeater` in the top bar.

Tuning: **Replay worker threads** (1–64, resized live) and **Throttle per request (ms)**.

### 2.4 Hierarchical Grouping (`Toppage > menu > button "Search"`) & Per-API Group Selection

1. **3-Box Quick Hierarchy Bar (`Page` > `Menu` > `Button`) + Full Path:**
   - In the top bar, enter `Page` (e.g. `Toppage`), `Menu` (e.g. `menu`), and `Button` (e.g. `button "Search"`) and click **`Gộp 3 ô -> Path`** (or type `Toppage > menu > button "Search"` directly into the `Path` field).
   - Click **`+ Nút / Action Mới...`** when moving to the next button on the page; it pre-fills the current `Page > Menu > ...` prefix so you only need to type the new button name.
2. **Nested Hierarchy Tree (`Cây phân cấp Group`):**
   - Renders a nested folder tree: opening **`Group "Toppage"`** reveals **`Group "menu"`**, opening **`Group "menu"`** reveals **`Group "button \"Search\""`**, and opening **`Group "button \"Search\""`** reveals each captured API (`API 1 [G01]`, `API 2 [G02]`...) containing **`1 API GỐC`** + **`N API Roles`**.
3. **Default View = Per-API Grouping (`Mặc định: Group theo từng API`):**
   - The right-hand API table defaults to showing every captured API individually (`Chế độ xem: Mặc định: Group theo từng API`).
   - **Per-API Group Selection:** Double-click the **`Group Path (Click đúp đổi Group riêng)`** cell (Column 2) on **any individual API row** to pick an existing hierarchy path from the dropdown or type a custom `Page > Menu > Button` path for that specific API.

### 2.5 Master-Detail view (tab **API Groups**), Color Highlighting & Anti-Lag Architecture

Every row in the **Features**, **API Groups**, and **Role Results** tables is automatically color-highlighted based on the role replay outcomes (cached in $O(1)$ on the model so scrolling and mouse movement never lag on the Swing EDT):

| Color / Level | Meaning |
|---|---|
| **Yellow `INFO` (`Vàng INFO: Có Role lỗi / Lệch quyền`)** | Highlighted in soft yellow whenever **any role call in the API fails** (`401 Unauthorized`, `403 Forbidden`, `4xx`, `5xx`, or connection timeout) or when roles return different response body lengths (`2xx lệch Body`). Shows exact counts such as `INFO: 1 OK / 9 Lỗi (403,401)` on the API row and `INFO: Không đủ quyền (403)` / `INFO: Chưa xác thực (401)` on each failing role row. |
| **Orange `WARN` (`Cam WARN: Nghi vấn Bypass`)** | Highlighted in soft orange on a role row when an unauthenticated / stripped-auth profile (`Guest` or `[REMOVE]` on `Authorization`/`Cookie`) unexpectedly returns `2xx OK` while another role in the same API was denied (`401`/`403`). |
| **Green `OK` (`Xanh OK: Cả N Role 2xx`)** | Highlighted in soft green when all replayed roles succeeded with `2xx` and consistent body length. |
| **Red `ERR` (`Đỏ ERR: Lỗi 5xx / Mạng`)** | Status cell / filter for server `5xx` errors or connection failures. |
| **Blue `REDIRECT` (`3xx`)** | Highlighted in soft blue for `3xx` redirect responses. |

- **Top-left table (Features / Chức năng):** Lists `[Tất cả: M chức năng]` plus each `Tên 1`, `Tên 2`, …, showing how many APIs belong to each feature, its role audit status (`INFO: X/Y API có Role lỗi/lệch`), and its API range (`API 1, API 2`, `API 3 .. API 6`).
- **Top-right table (API Groups):** Sequential `API #` (`API 1`, `API 2`, …), `Group` (`G01`, `G02`, …), `Chức năng`, `Đánh giá / Màu (Info)`, method, host, path, original status and length, **Roles**, replay progress, source, and time. Includes a **`Lọc màu Audit`** dropdown on the toolbar to filter APIs by `Vàng INFO`, `Cam WARN`, `Đỏ ERROR`, `Xanh OK`, or `Chưa Replay`.
- **Middle table (roles of the selected group):** `#`, `Role`, `Đánh giá Role (Màu)`, state, status, body length, Δ vs original, time, sends, and the Repeater tab name or error.
- **Bottom:** read-only Burp request/response viewers for the selected role.
- **Tab `History & Features (Lịch sử Chức năng & API)`:**
  - **Left:** Interactive `JTree` hierarchy (`Root → Tên 1 (API 1, API 2) → Roles`, `Tên 2 (API 3, API 4) → Roles`) with one-click Repeater dispatch, replay, or jump-to-group.
  - **Right:** Full text audit report summarizing the total number of features, total number of APIs, each feature's API list in chronological order, and per-role replay status codes/lengths, with **Export Báo cáo Lịch sử (.txt/.md)...**.

| Button | Effect |
|---|---|
| **Send Entire Group to Repeater** | All role requests of each selected group (or double-click a group) |
| **Send Selected Role to Repeater** | The selected role row(s) (or double-click a role) |
| **Replay All N Roles to Server** | Re-sends every role of each selected group in the background and updates the results |
| Replay Selected Role(s) | Re-sends only the selected rows |
| Rebuild with Current Roles | Re-clones the group's original request using the roles as they are now (after you edit tokens) |
| Show Original Req/Resp | Displays the captured baseline request and response in the bottom viewers |
| Export Matrix JSON... | Exports all captured API groups and per-role status/length metrics to a JSON file |
| Delete Group(s) / Clear All / Reset Dedup Cache | Housekeeping |

How to read results: a low-privilege role that gets a `2xx` with a body length close to the admin's (small Δ) on a privileged endpoint is a candidate authorization flaw. Check it by hand in the Repeater tab group.

---

### 2.6 Role theo phạm vi, Copy STT + Path, cửa sổ riêng (v1.10)

- **Role chỉ render khi cần:** request của từng role là ảo, chỉ được dựng khi bạn xem / gửi / đẩy sang Repeater.
- **Bật / Tắt Role theo phạm vi** (tab Roles → `🎛 Bật/Tắt theo phạm vi...`, hoặc `Bật/Tắt tất cả`, hoặc chuột phải trên API / nhánh):
  - **Toàn bộ:** đổi cờ Enabled của role (mọi API).
  - **Các nhánh:** quy tắc lưu theo nhánh, áp dụng cho nhánh con và cả API bắt sau này. Nhánh sâu hơn thắng nhánh cha.
  - **Các API gốc:** chỉ những API chọn.
  - Thứ tự ưu tiên: Enabled toàn bộ → nhánh → từng API. Tab `Ngoại lệ đã đặt` liệt kê và cho xóa từng quy tắc. Các role còn bật giữ nguyên kết quả đã nhận.
- **📋 Copy STT + Path** (nút, chuột phải, `Ctrl+Shift+C`): ví dụ `200. / > contact > button "send"`. STT lấy từ dòng Excel khớp; nếu không có file thì tùy chọn: bỏ STT / đếm tăng dần (lưu lại, đặt lại được) / số API. Mẫu dòng chỉnh được trong `Cấu hình` (`{stt} {path} {method} {endpoint} {url} {api}`). API đã copy có cột `📋 Đã copy`; file Excel xuất ra có cột `Path để copy`, `Đã copy` và có thể ghi POSITION theo cùng định dạng.
- **Đối chiếu Excel chính xác hơn:** chuẩn hóa hai phía (bỏ host / query / `;jsessionid`, gộp `//`, giải mã `%XX` trừ `%2F`), số / UUID trong file được coi là tham số (tùy chọn), dòng có query (`?type=a`) và dòng có host (URL đầy đủ) được ưu tiên khi khớp, path cụ thể thắng path có tham số. Tab Độ phủ có cột gợi ý gần đúng (khác 1 đoạn, thiếu tiền tố), đếm dòng trùng và sheet `API ngoài danh sách`.
- **Tách cả extension ra cửa sổ riêng:** nút `🗗 Tách ra cửa sổ riêng` ở thanh trên; đóng cửa sổ để gắn lại vào tab Burp.
- **Tab 🌳 Cây Sub-folder** (cả khi mở cửa sổ riêng) có khung Request / Response bên dưới giống Proxy history: chọn API → xem API gốc, chọn role → xem role đó.

### 2.7 Đích bắt, chờ xác nhận, chuyển / hoàn tác, giữ chỗ (v1.11)

- **➜ Request mới sẽ vào:** thanh thứ 2 ở trên cùng luôn hiện đích của request mới. Đích chỉ đổi khi bạn chọn lại
  (nút cam: danh sách đường dẫn có lọc / nhập mới; `🌳 Lấy nhánh đang chọn trong cây`; `＋ Nhánh mới...`;
  chuột phải nhánh → `Đặt làm ĐÍCH`). Bấm chọn chỗ khác trong cây / bảng **không** đổi đích.
- **⏳ Chờ xác nhận** (tùy chọn `Hỏi xác nhận vị trí API mới`, mặc định bật): API mới nằm trong nhánh đích nhưng
  màu xám. Xác nhận từng API, nhiều API (Ctrl / Shift + click trong cây hoặc bảng), cả nhánh hoặc tất cả
  (nút `⏳ Chờ xác nhận: N`). Chuyển sang đường dẫn khác cũng tính là xác nhận.
- **↪ Chuyển / ↶ Hoàn tác:** chọn nhiều API → chuyển sang đường dẫn khác; `Về vị trí trước` quay lại từng bước.
  Mọi thay đổi ghi vào nhật ký.
- **Giữ chỗ:** mỗi endpoint (method + host + path) nhớ vị trí đã xác nhận, kể cả sau khi xóa API, `Xóa toàn bộ`,
  reset dedup hay nạp lại extension. Khi gặp lại, API **quay về chỗ cũ** (nhánh cũ đã bị xóa thì được tạo lại),
  chờ xác nhận, và có 2 dòng con: `📍 Vị trí cũ` và `🆕 Vừa gặp tại ...` (chuột phải để giữ / chuyển).
  Nhánh nào có API đã xóa sẽ hiện `👻 N đã xóa (giữ chỗ)`.
- **Tab 🧭 Vị trí & Audit:** bảng mọi endpoint đã nhớ (vị trí giữ chỗ, API hiện tại, số lần xóa, số lần gặp,
  số lần bị bỏ qua do trùng, nơi gặp lần cuối) với Thêm / Sửa / Quên giữ chỗ / Cho phép bắt lại, và nhật ký
  (bắt mới, quay về chỗ cũ, xác nhận, chuyển, hoàn tác, xóa, đổi tên nhánh, sửa giữ chỗ) với nút hoàn tác từng dòng.
  Cả hai được xuất vào file Excel.
- **Xóa API giờ cho bắt lại được:** xóa API hoặc nhánh sẽ xóa luôn khóa chống trùng của chúng.
- **Excel:** mỗi API có icon copy và cột `Excel #STT · gặp N` (bấm để mở dòng đó trong tab Độ phủ Excel). Tab Độ phủ
  có bộ đếm lượt gặp từng dòng và bảng chi tiết từng lần gặp (path thực tế, vị trí, kết quả).

### 2.8 Giao diện gọn, API trùng, giữ chỗ cho cả API chưa xác nhận (v1.12)

- **Header 1 hàng:** `Capture` · `CHỈ CRAWL / GỬI` · `Hàng đợi` · `➜ Đích [path ▾]` · `Cần xử lý: N` · `⚙ ▾` · `🗗`.
  Đường dẫn và các thao tác nhánh nằm trong dropdown của nút Đích (chọn từ danh sách, lấy từ cây, nhánh con /
  cùng cấp mới, lên 1 cấp, đổi tên, đích gần đây). Các tùy chọn (xác nhận vị trí, giữ chỗ, API trùng, hiện API
  đã xóa) nằm trong `⚙ ▾`. Tên tab rút gọn: API · Lịch sử · Roles · Cấu hình · Log · Excel · Cây · Audit.
- **Icon ⓘ:** rê chuột xem tóm tắt, bấm xem giải thích đầy đủ (header, các phần của tab Audit, màu sắc).
- **Giữ chỗ cho cả API chưa xác nhận:** API bị xóa (hoặc Xóa toàn bộ, xóa path, reset chống trùng) nhớ vị trí
  đã xác nhận, nếu chưa xác nhận thì nhớ nơi nó nằm lúc bị xóa. Bắt lại sẽ về đúng chỗ đó; path đã mất được tạo lại
  và tab Audit > Cần xử lý giải thích, cho chọn: khôi phục path cũ / về nơi vừa gặp / path khác.
- **API trùng:** cùng endpoint gặp ở chỗ MỚI → tạo bản #2, #3 ... (màu tím, nhãn `⧉2/3`) và hỏi có giữ ở chỗ mới
  không. Giữ = hiện ở chỗ mới; Không = ẩn khỏi màn hình crawl, vẫn ở Audit > API trùng & ẩn (bấm Hiện để đưa lại).
  Gặp lại ở chỗ đã có bản thì chỉ đếm. Bấm nhãn tím (bảng hoặc cây) để xem nhanh mọi bản và thao tác nhanh.
- **Tab Audit:** Cần xử lý (giải thích từng API + nút) · Giữ chỗ · API trùng & ẩn · Nhật ký (hoàn tác từng dòng).
- **Chọn nhiều:** Ctrl / Shift + click trong cây (vd cả nhánh A + vài API của nhánh B) hoặc trong bảng; mọi thao tác
  áp dụng cho tất cả.

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

