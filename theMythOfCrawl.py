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
import os
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
                         BoxLayout, Box, JTree, JRadioButton, ButtonGroup, JFrame, JList, DefaultListModel,
                         JMenu, JCheckBoxMenuItem)
from javax.swing import Timer, UIManager, Icon, Scrollable, JComponent, KeyStroke, AbstractAction
from javax.swing.event import (ListSelectionListener, TreeSelectionListener, ChangeListener,
                               TreeWillExpandListener, DocumentListener)
from javax.swing.table import AbstractTableModel, DefaultTableCellRenderer
from javax.swing.tree import (DefaultMutableTreeNode, DefaultTreeModel, DefaultTreeCellRenderer,
                              TreeSelectionModel, TreePath, TreeCellRenderer)
from javax.swing.filechooser import FileNameExtensionFilter

# ---------------------------------------------------------------------------------------------------
# The core lives in tmoc_core.py next to this file (Jython cannot compile one module this large).
# Burp runs this file directly, so its folder is put on sys.path first; a cached copy from an earlier
# load of the extension is dropped so 'git pull' + reload always uses the new code.
def _tmoc_core_dir():
    found = []
    try:
        found.append(os.path.dirname(os.path.abspath(sys._getframe(0).f_code.co_filename)))
    except Exception:
        pass
    try:
        found.append(os.path.dirname(os.path.abspath(__file__)))
    except NameError:
        pass
    for d in found:
        if d and os.path.isfile(os.path.join(d, "tmoc_core.py")):
            return d
    return None


def _load_tmoc_core(folder):
    if folder and folder not in sys.path:
        sys.path.insert(0, folder)
    sys.modules.pop("tmoc_core", None)
    import tmoc_core
    globals().update(dict([(n, getattr(tmoc_core, n)) for n in tmoc_core.__all__]))
    return tmoc_core


try:
    _load_tmoc_core(_tmoc_core_dir())
    _CORE_ERROR = None
except ImportError as _core_exc:
    _CORE_ERROR = _core_exc   # retried in registerExtenderCallbacks with Burp's path of this file


class _PlacementMixin(object):
    """Capture destination, pending confirmation, moves / revert, 'giữ chỗ' book and its tab.
    Kept out of BurpExtender: Jython limits the size of one class body."""

    def _build_header_bar(self, cfg):
        """'➜ [đích ▾] ⓘ  [Cần xử lý ▾] ⓘ' - the destination and the decisions waiting for you."""
        bar = JPanel(FlowLayout(FlowLayout.LEFT, 3, 0))
        arrow = JLabel(u"➜ Đích:")
        arrow.setFont(arrow.getFont().deriveFont(Font.BOLD))
        bar.add(arrow)
        self.btn_dest = JButton(" ", actionPerformed=lambda e: self._show_destination_menu())
        self.btn_dest.setFont(self.btn_dest.getFont().deriveFont(Font.BOLD))
        self.btn_dest.setBackground(Color(234, 88, 12))
        self.btn_dest.setForeground(Color(255, 255, 255))
        self.btn_dest.setMargin(Insets(2, 8, 2, 8))
        bar.add(self.btn_dest)
        bar.add(info_icon(HELP["dest"], u"Đích của request mới"))
        self.btn_todo = JButton(u"Cần xử lý: 0", actionPerformed=lambda e: self._show_todo_menu())
        self.btn_todo.setFont(self.btn_todo.getFont().deriveFont(Font.BOLD))
        self.btn_todo.setMargin(Insets(2, 8, 2, 8))
        bar.add(self.btn_todo)
        bar.add(info_icon(HELP["todo"], u"Cần xử lý"))
        self._recent_dest = []
        self._refresh_destination_bar()
        return bar

    def _set_place_option(self, key, value):
        cfg = self.get_config()
        cfg[key] = bool(value)
        self.apply_config(cfg)

    def _refresh_destination_bar(self):
        btn = getattr(self, "btn_dest", None)
        if btn is None:
            return
        name = self.active_feature().name
        shown = name if len(name) <= 60 else u"…" + name[-58:]
        if btn.getText() != u"%s ▾" % shown:
            btn.setText(u"%s ▾" % shown)
            btn.setToolTipText(u"Request mới sẽ vào: %s  (bấm để đổi)" % name)
        pending = self.pending_groups()
        dups = len([g for g in pending if getattr(g, "dup_pending", False)])
        n = len(pending)
        self.btn_todo.setText((u"Cần xử lý: %d" % n) + ((u" (⧉%d)" % dups) if dups else u""))
        self.btn_todo.setBackground(Color(128, 128, 140) if n else None)
        self.btn_todo.setForeground(Color(255, 255, 255) if n else None)

    def _show_destination_menu(self):
        menu = JPopupMenu()
        menu.add(JMenuItem(u"📂 Chọn đích từ danh sách...", actionPerformed=lambda e: self._on_pick_destination()))
        menu.add(JMenuItem(u"🌳 Lấy nhánh đang chọn trong cây", actionPerformed=lambda e: self._on_dest_from_tree()))
        menu.add(JMenuItem(u"＋ Nhánh con mới của đích...", actionPerformed=lambda e: self._on_new_destination()))
        menu.add(JMenuItem(u"＋ Nhánh mới cùng cấp (nút / action tiếp theo)...", actionPerformed=self._on_next_feature))
        menu.add(JMenuItem(u"⬆ Lên 1 cấp", actionPerformed=self._on_pop_subfolder))
        menu.add(JMenuItem(u"✏ Đổi tên / sửa đường dẫn đích...", actionPerformed=lambda e: self._on_rename_destination()))
        more = JMenu(u"Khác")
        more.add(JMenuItem(u"⚙ Quản lý các cấp của đích (thêm / xóa / đổi thứ tự)...",
                           actionPerformed=self._on_open_subfolder_manager))
        more.add(JMenuItem(u"🗑 Xóa nhánh đích...", actionPerformed=self._on_delete_active_branch))
        menu.add(more)
        recent = [p for p in self._recent_dest if p != self.active_feature().name][:8]
        if recent:
            menu.addSeparator()
            title = JMenuItem(u"Gần đây:")
            title.setEnabled(False)
            menu.add(title)
            for path in recent:
                menu.add(JMenuItem(u"   " + path, actionPerformed=lambda e, p=path: self.set_destination(p)))
        menu.show(self.btn_dest, 0, self.btn_dest.getHeight())

    def _on_rename_destination(self):
        act = self.active_feature()
        name = JOptionPane.showInputDialog(self.main_panel, u"Sửa đường dẫn của đích (các API trong nhánh này đổi theo):",
                                           act.name)
        if name is not None and u_text(name).strip():
            self._apply_or_switch_path(normalize_hierarchy_path(name), rename_current=True)
            self._refresh_destination_bar()

    def _show_todo_menu(self):
        groups = self.pending_groups()
        dups = [g for g in groups if getattr(g, "dup_pending", False)]
        menu = JPopupMenu()
        menu.add(JMenuItem(u"🧭 Mở danh sách Cần xử lý (giải thích + nút cho từng API)...",
                           actionPerformed=lambda e: self.show_audit("decide")))
        menu.addSeparator()
        n = len(groups)
        items = [
            (JMenuItem(u"✔ Giữ chỗ hiện tại cho cả %d API" % n,
                       actionPerformed=lambda e: self.confirm_groups(self.pending_groups(), u"xác nhận tất cả")), n),
            (JMenuItem(u"↪ Chuyển cả %d API sang path khác..." % n,
                       actionPerformed=lambda e: self.open_move_dialog(self.pending_groups())), n),
            (JMenuItem(u"🙈 Không giữ %d API trùng (ẩn, vẫn lưu ở Audit)" % len(dups),
                       actionPerformed=lambda e: self.hide_groups(
                           [g for g in self.pending_groups() if getattr(g, "dup_pending", False)])), len(dups)),
            (JMenuItem(u"🔎 Lọc bảng API: chỉ API đang chờ", actionPerformed=lambda e: self._filter_pending()), n),
            (None, 1),
            (JMenuItem(u"🙈 Xem API trùng & đang ẩn (%d ẩn)" % len(self._hidden),
                       actionPerformed=lambda e: self.show_audit("dups")), 1),
            (JMenuItem(u"🗑 Xóa %d API đang chờ..." % n, actionPerformed=lambda e: self._drop_pending()), n),
        ]
        for item, enabled in items:
            if item is None:
                menu.addSeparator()
                continue
            item.setEnabled(bool(enabled))
            menu.add(item)
        menu.show(self.btn_todo, 0, self.btn_todo.getHeight())

    def known_paths(self):
        paths = [f.name for f in self.features_list()]
        if self.group_model is not None:
            paths += [g.feature_name for g in self.group_model.all_groups()]
        paths += [r.get("place") for r in self.places.entries.values() if r.get("place")]
        out = set()
        for p in paths:
            parts = split_hierarchy_path(p)
            for i in range(1, len(parts) + 1):
                out.add(normalize_hierarchy_path(parts[:i]))
        return out

    def set_destination(self, path):
        if not path:
            return
        self._apply_or_switch_path(path, rename_current=False)
        name = self.active_feature().name
        self._recent_dest = [name] + [p for p in getattr(self, "_recent_dest", []) if p != name][:11]
        self.log(u"➜ Đích cho request mới: %s" % self.active_feature().name)
        self._refresh_destination_bar()
        self._flash_status(u"➜ Request mới sẽ vào: %s" % self.active_feature().name)

    def _on_pick_destination(self):
        path = PathPickerDialog(self.main_panel, "Chọn đích cho request mới", self.known_paths(),
                                self.active_feature().name,
                                "Mọi request mới sẽ vào đường dẫn này cho tới khi bạn chọn lại.").show()
        self.set_destination(path)

    def _on_dest_from_tree(self):
        prefix = self._selected_hierarchy_prefix()
        if not prefix:
            JOptionPane.showMessageDialog(self.main_panel, "Chọn 1 nhánh trong cây trước.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        self.set_destination(prefix)

    def _on_new_destination(self):
        name = JOptionPane.showInputDialog(
            self.main_panel, "Đường dẫn nhánh mới (ngăn cách bởi '>'), sẽ thành đích cho request mới:",
            self.active_feature().name + " > ")
        if name is not None and u_text(name).strip().strip(">").strip():
            self.set_destination(normalize_hierarchy_path(name))

    def _filter_pending(self):
        combo = getattr(self, "cb_audit_filter", None)
        values = [v for _, v in AUDIT_FILTER_OPTIONS]
        if combo is not None:
            combo.setSelectedIndex(values.index(AUDIT_PENDING))
        else:
            self.group_model.set_audit_filter(AUDIT_PENDING)
        self.tabs.setSelectedIndex(0)

    def _drop_pending(self):
        groups = self.pending_groups()
        if not groups or JOptionPane.showConfirmDialog(
                self.main_panel, u"Xóa %d API đang chờ xác nhận?" % len(groups), EXT_NAME,
                JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
            return
        self.group_model.remove_groups(groups)
        self.on_groups_removed(groups, u"bỏ API chờ xác nhận")
        self._refresh_feature_views()
        self.update_status()

    def _add_place_items(self, menu, groups, branch=None):
        groups = list(groups or [])
        pending = [g for g in groups if getattr(g, "pending", False)]
        n = len(groups)
        items = [
            (JMenuItem(u"✔ Xác nhận vị trí (%d API đang chờ)" % len(pending),
                       actionPerformed=lambda e: self.confirm_groups(pending)), bool(pending)),
            (JMenuItem(u"↪ Chuyển %d API sang đường dẫn khác..." % n,
                       actionPerformed=lambda e: self.open_move_dialog(groups)), n > 0),
            (JMenuItem(u"↶ Đưa %d API về vị trí trước" % n,
                       actionPerformed=lambda e: self._on_revert(groups)),
             any([g.place_history for g in groups])),
        ]
        if n == 1:
            items.append((JMenuItem(u"🧭 Lịch sử vị trí API #%d" % groups[0].gid,
                                    actionPerformed=lambda e: self.show_place_of(groups[0].book_key)), True))
        for item, enabled in items:
            item.setEnabled(enabled)
            menu.add(item)

    def open_move_dialog(self, groups):
        groups = list(groups or [])
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, "Chọn API (bảng hoặc cây) trước.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return 0
        path = PathPickerDialog(self.main_panel, u"Chuyển %d API sang đường dẫn khác" % len(groups),
                                self.known_paths(), groups[0].feature_name,
                                u"%d API sẽ được chuyển và xác nhận vị trí (ghi vào nhật ký, hoàn tác được)."
                                % len(groups)).show()
        if not path:
            return 0
        n = self.move_groups_to_path(groups, path)
        self._flash_status(u"↪ Đã chuyển %d API sang %s" % (n, path))
        return n

    def _on_revert(self, groups):
        n = self.revert_groups(list(groups or []))
        self._flash_status(u"↶ %d API đã về vị trí trước" % n if n else u"Không có vị trí trước để quay về")

    # ---- "Audit" tab: Cần xử lý | Giữ chỗ | API trùng & ẩn | Nhật ký
    def _audit_bar(self, help_key, title, *controls):
        bar = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        bar.add(info_icon(HELP[help_key], title))
        for c in controls:
            bar.add(c)
        return bar

    def _audit_table(self, model, widths, audit_col, method_col=None, bold=()):
        table = JTable(model)
        style_data_table(table)
        table.setAutoCreateRowSorter(True)
        renderer = AuditTableRenderer(model, audit_col=audit_col, method_col=method_col, bold_cols=bold)
        for col, width in enumerate(widths):
            column = table.getColumnModel().getColumn(col)
            column.setPreferredWidth(width)
            column.setCellRenderer(renderer)
        return table

    def _build_places_tab(self):
        self.audit_tabs = JTabbedPane()
        self.audit_tabs.addTab(u"Cần xử lý", self._build_decide_panel())
        self.audit_tabs.addTab(u"Giữ chỗ", self._build_book_panel())
        self.audit_tabs.addTab(u"API trùng & ẩn", self._build_dups_panel())
        self.audit_tabs.addTab(u"Nhật ký", self._build_log_panel())
        self.audit_tabs.addChangeListener(_Change(lambda e: self._reload_places()))
        self.places_panel = JPanel(BorderLayout())
        self.places_panel.add(self.audit_tabs, BorderLayout.CENTER)
        return self.places_panel

    def show_audit(self, section="decide"):
        if getattr(self, "places_panel", None) is None:
            return
        self.tabs.setSelectedComponent(self.places_panel)
        self.audit_tabs.setSelectedIndex(["decide", "places", "dups", "log"].index(section))
        self._reload_places()

    # Cần xử lý
    def _build_decide_panel(self):
        buttons = [JButton(u"✔ Giữ chỗ hiện tại", actionPerformed=lambda e: self._decide("keep")),
                   JButton(u"↪ Về nơi vừa gặp", actionPerformed=lambda e: self._decide("found")),
                   JButton(u"📁 Path khác...", actionPerformed=lambda e: self._decide("other")),
                   JButton(u"🙈 Không giữ", actionPerformed=lambda e: self._decide("hide")),
                   JButton(u"🗑 Xóa", actionPerformed=lambda e: self._decide("delete")),
                   JButton(u"Chọn hết", actionPerformed=lambda e: self.decide_table.selectAll())]
        buttons[0].setFont(buttons[0].getFont().deriveFont(Font.BOLD))
        self.decide_model = _RowsModel(DECIDE_COLS)
        self.decide_table = self._audit_table(self.decide_model, (150, 80, 300, 300, 300), 0, None, (1,))
        self.decide_table.getSelectionModel().addListSelectionListener(_SelectionListener(self._on_decide_selected))
        self.decide_text = JTextArea(4, 60)
        self.decide_text.setEditable(False)
        self.decide_text.setLineWrap(True)
        self.decide_text.setWrapStyleWord(True)
        self.decide_text.setBorder(BorderFactory.createEmptyBorder(6, 8, 6, 8))
        split = JSplitPane(JSplitPane.VERTICAL_SPLIT, JScrollPane(self.decide_table), JScrollPane(self.decide_text))
        split.setResizeWeight(0.65)
        panel = JPanel(BorderLayout())
        panel.add(self._audit_bar("decide", u"Cần xử lý", *buttons), BorderLayout.NORTH)
        panel.add(split, BorderLayout.CENTER)
        return panel

    def _selected_rows_payload(self, table, model):
        return [model.payload_at(table.convertRowIndexToModel(vr)) for vr in table.getSelectedRows()]

    def _on_decide_selected(self):
        rows = self._selected_rows_payload(self.decide_table, self.decide_model)
        if not rows:
            self.decide_text.setText(u"Chọn 1 dòng để xem giải thích và lựa chọn.")
        elif len(rows) == 1:
            self.decide_text.setText(decision_text(rows[0], self._copies_of(rows[0].book_key)))
        else:
            self.decide_text.setText(u"%d API đang chọn. Các nút phía trên áp dụng cho tất cả." % len(rows))
        self.decide_text.setCaretPosition(0)

    def _decide(self, action):
        groups = self._selected_rows_payload(self.decide_table, self.decide_model)
        if not groups:
            JOptionPane.showMessageDialog(self.main_panel, u"Chọn ít nhất 1 dòng.", EXT_NAME,
                                          JOptionPane.INFORMATION_MESSAGE)
            return
        if action == "keep":
            n = self.confirm_groups(groups, u"giữ chỗ hiện tại")
            msg = u"✔ Đã giữ chỗ hiện tại cho %d API" % n
        elif action == "found":
            n = 0
            for g in groups:
                hint = getattr(g, "place_hint", None)
                if hint and hint.get("found"):
                    n += 1 if self.move_groups_to_path([g], hint["found"], note=u"về nơi vừa gặp") else 0
                else:
                    n += self.confirm_groups([g], u"đã ở nơi vừa gặp")
            msg = u"↪ %d API đã ở nơi vừa gặp" % n
        elif action == "other":
            n = self.open_move_dialog(groups)
            msg = u"📁 Đã chuyển %d API" % (n or 0)
        elif action == "hide":
            n = self.hide_groups(groups, u"không giữ")
            msg = u"🙈 Đã ẩn %d API (xem lại ở tab API trùng & ẩn)" % n
        else:
            if JOptionPane.showConfirmDialog(self.main_panel, u"Xóa %d API?" % len(groups), EXT_NAME,
                                             JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
                return
            self.group_model.remove_groups(groups)
            self.on_groups_removed(groups, u"xóa từ Cần xử lý")
            self._refresh_feature_views()
            msg = u"🗑 Đã xóa %d API" % len(groups)
        self._flash_status(msg)
        self._ui_tick(None)

    # Giữ chỗ
    def _build_book_panel(self):
        self.tf_place_filter = JTextField(16)
        self.tf_place_filter.setToolTipText(u"Lọc theo method, path, vị trí...")
        self.tf_place_filter.getDocument().addDocumentListener(_DocChange(lambda: self._reload_places()))
        self.cb_place_view = JComboBox([u"Tất cả", u"Đang có API", u"👻 Đã xóa (giữ chỗ)", u"⏳ Chờ xác nhận"])
        self.cb_place_view.addActionListener(_Action(lambda e: self._reload_places()))
        more = JButton(u"Thêm ▾")
        more.addActionListener(_Action(lambda e: self._show_book_more(more)))
        bar = self._audit_bar("places", u"Giữ chỗ", JLabel(u"Lọc:"), self.tf_place_filter, self.cb_place_view,
                              JButton(u"✏ Sửa chỗ...", actionPerformed=lambda e: self._on_edit_place()),
                              JButton(u"➕ Thêm...", actionPerformed=lambda e: self._on_add_place()), more)
        self.lbl_places = JLabel(u" ")
        self.lbl_places.setBorder(BorderFactory.createEmptyBorder(0, 8, 2, 8))
        self.place_model = _RowsModel(PLACE_COLS)
        self.place_table = self._audit_table(self.place_model, (65, 280, 150, 280, 80, 140, 70, 60, 90, 110, 240, 80),
                                             5, 0, (3,))
        self.place_table.addMouseListener(_DoubleClick(lambda: self._on_edit_place()))
        top = JPanel(BorderLayout())
        top.add(bar, BorderLayout.NORTH)
        top.add(self.lbl_places, BorderLayout.SOUTH)
        panel = JPanel(BorderLayout())
        panel.add(top, BorderLayout.NORTH)
        panel.add(JScrollPane(self.place_table), BorderLayout.CENTER)
        return panel

    def _show_book_more(self, btn):
        menu = JPopupMenu()
        menu.add(JMenuItem(u"✖ Quên giữ chỗ (lần sau vào đích hiện tại)", actionPerformed=lambda e: self._on_forget_place()))
        menu.add(JMenuItem(u"♻ Cho phép bắt lại ngay (xóa bộ nhớ chống trùng)",
                           actionPerformed=lambda e: self._on_recapture_place()))
        menu.add(JMenuItem(u"🔎 Mở API đang có", actionPerformed=lambda e: self._on_open_place_api()))
        menu.add(JMenuItem(u"🕘 Xem nhật ký của endpoint này", actionPerformed=lambda e: self._show_log_of_selected()))
        menu.show(btn, 0, btn.getHeight())

    def _show_log_of_selected(self):
        rec = self._selected_place()
        if rec is not None:
            self._log_key = rec.get("key")
            self.audit_tabs.setSelectedIndex(3)
            self._reload_places()

    # API trùng & ẩn
    def _build_dups_panel(self):
        self.cb_dup_view = JComboBox([u"Tất cả API trùng & ẩn", u"Chỉ đang ẩn"])
        self.cb_dup_view.addActionListener(_Action(lambda e: self._reload_places()))
        bar = self._audit_bar("dups", u"API trùng & ẩn", self.cb_dup_view,
                              JButton(u"👁 Hiện", actionPerformed=lambda e: self._dup_action("show")),
                              JButton(u"🙈 Ẩn", actionPerformed=lambda e: self._dup_action("hide")),
                              JButton(u"✔ Giữ (bản chờ)", actionPerformed=lambda e: self._dup_action("keep")),
                              JButton(u"🔎 Mở", actionPerformed=lambda e: self._dup_action("open")),
                              JButton(u"🗑 Xóa", actionPerformed=lambda e: self._dup_action("delete")))
        self.dup_model = _RowsModel(DUP_COLS)
        self.dup_table = self._audit_table(self.dup_model, (320, 70, 80, 320, 140, 70, 80), 4, None, (1,))
        self.dup_table.addMouseListener(_DoubleClick(lambda: self._dup_action("open")))
        panel = JPanel(BorderLayout())
        panel.add(bar, BorderLayout.NORTH)
        panel.add(JScrollPane(self.dup_table), BorderLayout.CENTER)
        return panel

    def _dup_action(self, action, groups=None):
        if groups is None:
            groups = self._selected_rows_payload(self.dup_table, self.dup_model)
        if not groups:
            return 0
        if action == "show":
            n = self.show_groups(groups)
        elif action == "hide":
            n = self.hide_groups(groups)
        elif action == "keep":
            n = self.keep_duplicates(groups)
        elif action == "open":
            g = groups[0]
            if getattr(g, "hidden", False):
                self.show_groups([g])
                self._ui_tick(None)
            self.group_model.set_feature_filter(None)
            self.group_model.set_hierarchy_filter(None)
            self.tabs.setSelectedIndex(0)
            self._select_group_in_table(g)
            return 1
        else:
            if JOptionPane.showConfirmDialog(self.main_panel, u"Xóa %d bản?" % len(groups), EXT_NAME,
                                             JOptionPane.YES_NO_OPTION) != JOptionPane.YES_OPTION:
                return 0
            shown = [g for g in groups if not getattr(g, "hidden", False)]
            if shown:
                self.group_model.remove_groups(shown)
            self.on_groups_removed(groups, u"xóa bản trùng")
            self._refresh_feature_views()
            n = len(groups)
        self._ui_tick(None)
        return n

    def show_dup_popup(self, g):
        """Quick look at every copy of a duplicated API (#1 ... #n) with the common actions."""
        copies = sorted(self._copies_of(g.book_key), key=lambda c: c.dup_no)
        model = _RowsModel([u"Bản", u"API", u"Đang ở", u"Trạng thái", u"Excel"])
        rows = []
        for c in copies:
            hidden = getattr(c, "hidden", False)
            state = u"🙈 ẩn" if hidden else (u"⏳ chờ quyết định" if getattr(c, "dup_pending", False) else u"đang hiện")
            e = getattr(c, "target", None)
            rows.append((c, AUDIT_PENDING if hidden else AUDIT_NONE,
                         [u"#%d" % c.dup_no, format_api_label(c.gid), c.feature_name, state,
                          (u"#%s" % e.stt) if e is not None else u""]))
        model.set_rows(rows)
        table = JTable(model)
        style_data_table(table)
        for col, width in enumerate((45, 70, 300, 120, 60)):
            table.getColumnModel().getColumn(col).setPreferredWidth(width)
        mine = [i for i, c in enumerate(copies) if c is g]
        if mine:
            table.setRowSelectionInterval(mine[0], mine[0])
        scroll = JScrollPane(table)
        scroll.setPreferredSize(Dimension(620, min(60 + 24 * len(rows), 260)))
        popup = JPopupMenu()

        def act(kind):
            vr = table.getSelectedRow()
            if vr < 0:
                return
            target = model.payload_at(vr)
            popup.setVisible(False)
            if kind == "audit":
                self.show_audit("dups")
            else:
                self._dup_action(kind, [target])

        head = JLabel(u"  ⧉ %s %s  ·  %d bản (số #1, #2 ... theo thứ tự gặp)" % (g.method, strip_query(g.path),
                                                                              len(copies)))
        head.setFont(head.getFont().deriveFont(Font.BOLD))
        head.setForeground(DUP_PURPLE)
        btns = JPanel(FlowLayout(FlowLayout.LEFT, 4, 2))
        for label, kind in ((u"🔎 Mở", "open"), (u"✔ Giữ", "keep"), (u"🙈 Ẩn", "hide"), (u"👁 Hiện", "show"),
                            (u"🗑 Xóa", "delete"), (u"Chi tiết ở Audit", "audit")):
            btns.add(JButton(label, actionPerformed=lambda e, k=kind: act(k)))
        panel = JPanel(BorderLayout(2, 2))
        panel.add(head, BorderLayout.NORTH)
        panel.add(scroll, BorderLayout.CENTER)
        panel.add(btns, BorderLayout.SOUTH)
        popup.add(panel)
        anchor = getattr(self, "_chip_anchor", None) or (self.main_panel, 40, 40)
        popup.show(anchor[0], anchor[1], anchor[2])
        return popup

    # Nhật ký
    def _build_log_panel(self):
        self._log_key = None
        self.tf_log_filter = JTextField(16)
        self.tf_log_filter.getDocument().addDocumentListener(_DocChange(lambda: self._reload_places()))
        self.btn_log_scope = JButton(u"Tất cả endpoint", actionPerformed=lambda e: self._clear_log_scope())
        self.btn_log_scope.setToolTipText(u"Đang xem nhật ký của 1 endpoint - bấm để xem tất cả")
        bar = self._audit_bar("log", u"Nhật ký vị trí", JLabel(u"Lọc:"), self.tf_log_filter, self.btn_log_scope,
                              JButton(u"↶ Hoàn tác dòng chọn", actionPerformed=lambda e: self._on_revert_log()),
                              JButton(u"Xóa nhật ký...", actionPerformed=lambda e: self._on_clear_place_log()))
        self.place_log_model = _RowsModel(PLACE_LOG_COLS)
        self.place_log_table = self._audit_table(self.place_log_model, (45, 110, 230, 70, 65, 260, 240, 240, 300),
                                                 2, 4, (0,))
        self.place_log_table.addMouseListener(_DoubleClick(lambda: self._on_revert_log()))
        panel = JPanel(BorderLayout())
        panel.add(bar, BorderLayout.NORTH)
        panel.add(JScrollPane(self.place_log_table), BorderLayout.CENTER)
        return panel

    def _clear_log_scope(self):
        self._log_key = None
        self._reload_places()

    def _selected_place(self):
        table = getattr(self, "place_table", None)
        if table is None:
            return None
        vr = table.getSelectedRow()
        return self.place_model.payload_at(table.convertRowIndexToModel(vr)) if vr >= 0 else None

    def _reload_places(self):
        if getattr(self, "audit_tabs", None) is None:
            return
        pending = self.pending_groups()
        keep = self._selected_rows_payload(self.decide_table, self.decide_model)
        self.decide_model.set_rows([
            (g, AUDIT_PENDING if decision_kind(g) == "new" else AUDIT_INFO,
             [DECISION_LABELS[decision_kind(g)], format_api_label(g.gid), u"%s %s" % (g.method, strip_query(g.path)),
              g.feature_name, (getattr(g, "place_hint", None) or {}).get("found")
              or (g.feature_name if getattr(g, "dup_pending", False) else u"")])
            for g in sorted(pending, key=lambda x: x.gid)])
        for g in keep:
            for r in range(self.decide_model.getRowCount()):
                if self.decide_model.payload_at(r) is g:
                    vr = self.decide_table.convertRowIndexToView(r)
                    self.decide_table.addRowSelectionInterval(vr, vr)
        self._on_decide_selected()
        keep_rec = self._selected_place()
        rows = place_rows(self.places, self.cb_place_view.getSelectedIndex(), self.tf_place_filter.getText())
        self.place_model.set_rows([(rec, PLACE_STATE_LEVEL[st], cells) for rec, st, cells in rows])
        if keep_rec is not None:
            self._select_place_key(keep_rec.get("key"), scroll=False)
        dup_rows_ = dup_rows(dict(self._copies), self.cb_dup_view.getSelectedIndex() == 1)
        self.dup_model.set_rows(dup_rows_)
        key = self._log_key
        log_rows = place_log_rows(self.places, key, self.tf_log_filter.getText())
        self.place_log_model.set_rows([(ev, PLACE_ACTION_LEVEL.get(ev.get("action"), AUDIT_NONE), cells)
                                       for ev, cells in log_rows])
        rec = self.places.get(key) if key else None
        self.btn_log_scope.setText((u"Chỉ: %s %s ✖" % (rec.get("method"), short_path(rec.get("path") or u"", 30)))
                                   if rec else u"Tất cả endpoint")
        self.btn_log_scope.setEnabled(rec is not None)
        counts = {}
        for r in self.places.entries.values():
            st = place_state(r)
            counts[st] = counts.get(st, 0) + 1
        self.lbl_places.setText(u"%d endpoint · %d đang có API · 👻 %d đã xóa (giữ chỗ) · click đúp để sửa chỗ"
                                % (len(self.places.entries), counts.get("live", 0) + counts.get("pending", 0),
                                   counts.get("deleted", 0)))
        dup_count = len([1 for k, v in self._copies.items() if len(v) > 1])
        titles = [u"Cần xử lý (%d)" % len(pending), u"Giữ chỗ (%d)" % len(self.places.entries),
                  u"API trùng & ẩn (%d ⧉ · %d 🙈)" % (dup_count, len(self._hidden)), u"Nhật ký (%d)" % len(self.places.log)]
        for i, t in enumerate(titles):
            if self.audit_tabs.getTitleAt(i) != t:
                self.audit_tabs.setTitleAt(i, t)

    def _select_place_key(self, key, scroll=True):
        for r in range(self.place_model.getRowCount()):
            rec = self.place_model.payload_at(r)
            if rec is not None and rec.get("key") == key:
                vr = self.place_table.convertRowIndexToView(r)
                if vr >= 0:
                    self.place_table.setRowSelectionInterval(vr, vr)
                    if scroll:
                        self.place_table.scrollRectToVisible(self.place_table.getCellRect(vr, 0, True))
                return True
        return False

    def show_place_of(self, key, view=0):
        if getattr(self, "places_panel", None) is None:
            return
        self.tabs.setSelectedComponent(self.places_panel)
        self.audit_tabs.setSelectedIndex(1)
        self.cb_place_view.setSelectedIndex(view)
        self.tf_place_filter.setText(u"")
        self._log_key = key
        self._reload_places()
        if key is not None:
            self._select_place_key(key)

    def _on_edit_place(self, rec=None):
        rec = rec or self._selected_place()
        if rec is None:
            return
        path = PathPickerDialog(self.main_panel, u"Vị trí giữ chỗ cho %s %s" % (rec.get("method"), rec.get("path")),
                                self.known_paths(), rec.get("place") or self.active_feature().name,
                                u"Lần sau API này được bắt lại (sau khi xóa) sẽ vào đường dẫn này.").show()
        if path:
            self.edit_place(rec["key"], path)
            self._ui_tick(None)

    def _on_add_place(self):
        raw = JOptionPane.showInputDialog(
            self.main_panel, u"Endpoint cần giữ chỗ, dạng 'METHOD host /path'\nVD: POST api.example.com /contact/send",
            u"GET %s /" % (self.group_model.all_groups()[0].host if self.group_model.all_groups() else u"host"))
        if raw is None:
            return
        parts = u_text(raw).split()
        if len(parts) != 3 or not parts[2].startswith("/"):
            JOptionPane.showMessageDialog(self.main_panel, u"Cần đúng 3 phần: METHOD host /path", EXT_NAME,
                                          JOptionPane.WARNING_MESSAGE)
            return
        path = PathPickerDialog(self.main_panel, u"Vị trí giữ chỗ", self.known_paths(), self.active_feature().name).show()
        if path:
            key = self.add_manual_place(parts[0], parts[1], parts[2], path)
            self._ui_tick(None)
            self._select_place_key(key)

    def _on_forget_place(self):
        rec = self._selected_place()
        if rec is None:
            return
        if JOptionPane.showConfirmDialog(self.main_panel, u"Quên vị trí giữ chỗ của %s %s?\nLần sau bắt lại sẽ vào "
                                         u"đích hiện tại." % (rec.get("method"), rec.get("path")), EXT_NAME,
                                         JOptionPane.YES_NO_OPTION) == JOptionPane.YES_OPTION:
            self.forget_place(rec["key"])
            self._ui_tick(None)

    def _on_recapture_place(self):
        rec = self._selected_place()
        if rec is not None:
            n = self.allow_recapture(rec["key"])
            self._flash_status(u"♻ Đã xóa %d khóa chống trùng: request tiếp theo của endpoint này sẽ được bắt" % n)
            self._ui_tick(None)

    def _on_open_place_api(self):
        rec = self._selected_place()
        g = self._group_by_gid(rec.get("gid")) if rec is not None else None
        if g is None:
            self._flash_status(u"Endpoint này hiện không có API (đã xóa)")
            return
        self.group_model.set_feature_filter(None)
        self.group_model.set_hierarchy_filter(None)
        self.tabs.setSelectedIndex(0)
        self._select_group_in_table(g)

    def _on_revert_log(self):
        vr = self.place_log_table.getSelectedRow()
        if vr < 0:
            return
        ev = self.place_log_model.payload_at(self.place_log_table.convertRowIndexToModel(vr))
        msg = self.revert_event(ev)
        self._flash_status(msg)
        JOptionPane.showMessageDialog(self.main_panel, msg, EXT_NAME, JOptionPane.INFORMATION_MESSAGE)
        self._ui_tick(None)

    def _on_clear_place_log(self):
        if JOptionPane.showConfirmDialog(self.main_panel, u"Xóa toàn bộ nhật ký vị trí? (vị trí giữ chỗ vẫn giữ nguyên)",
                                         EXT_NAME, JOptionPane.YES_NO_OPTION) == JOptionPane.YES_OPTION:
            with self.places._lock:
                self.places.log = []
                self.places.dirty = True
            self._after_place_change()
            self._ui_tick(None)

    def pending_groups(self):
        return [g for g in (self.group_model.all_groups() if self.group_model is not None else [])
                if getattr(g, "pending", False)]

    def confirm_groups(self, groups, note=u""):
        n = self.keep_duplicates([g for g in groups if getattr(g, "dup_pending", False)])
        for g in groups:
            if not getattr(g, "pending", False):
                continue
            g.pending = False
            g.place_hint = None
            if g.book_key:
                self.places.set_place(g.book_key, g.feature_name)
                self.places.update(g.book_key, pending=False)
            self.places.event("confirm", g.book_key, g.gid, g.method, g.path, None, g.feature_name, note)
            self._notify_results(g, None)
            n += 1
        if n:
            self.log("Đã xác nhận vị trí của %d API." % n)
            self._after_place_change()
        return n

    def move_groups_to_path(self, groups, path, action="move", confirm=True, note=u""):
        feat = self.find_or_create_feature_by_path(path)
        return self.move_groups_to_feature(groups, feat.fid, action=action, confirm=confirm, note=note)

    def revert_groups(self, groups):
        """Each API goes back to the branch it was in before its last move."""
        n = 0
        for g in groups:
            if not g.place_history:
                continue
            prev = g.place_history.pop()
            feat = self.find_or_create_feature_by_path(prev)
            self.move_groups_to_feature([g], feat.fid, action="revert", confirm=not g.pending,
                                        note=u"về vị trí trước", push_history=False)
            n += 1
        return n

    def revert_event(self, ev):
        """Undo one line of the placement log. Returns a message for the user."""
        action = ev.get("action")
        if action in ("edit", "manual", "forget", "rename", "delete", "recapture"):
            if action == "edit" and ev.get("key") and self.places.get(ev["key"]) is not None:
                self.places.set_place(ev["key"], ev.get("src"))
                self.places.event("revert", ev["key"], None, ev.get("method"), ev.get("path"), ev.get("dst"),
                                  ev.get("src"), u"hoàn tác sửa giữ chỗ #%s" % ev.get("id"))
                self._after_place_change()
                return u"Đã trả vị trí giữ chỗ về: %s" % (ev.get("src") or u"(trống)")
            return u"Thao tác '%s' không hoàn tác tự động được." % PLACE_ACTIONS.get(action, action)
        g = self._live_group_for(ev)
        if g is None:
            return u"API của dòng này không còn (đã xóa) - hãy sửa vị trí giữ chỗ ở bảng phía trên."
        if not ev.get("src"):
            return u"Dòng này không có vị trí trước để quay về."
        self.move_groups_to_path([g], ev["src"], action="revert", confirm=not g.pending,
                                 note=u"hoàn tác dòng nhật ký #%s" % ev.get("id"))
        return u"API #%d đã về: %s" % (g.gid, ev["src"])

    def _live_group_for(self, ev):
        if self.group_model is None or ev.get("gid") is None:
            return None
        for g in self.group_model.all_groups():
            if g.gid == ev["gid"] and (ev.get("key") is None or g.book_key == ev.get("key")):
                return g
        return None

    def _after_place_change(self):
        self._stale_places = True
        self._mark(structure=True, status=True)

    def on_groups_removed(self, groups, note=u""):
        """
        Deleted APIs keep their place ('giữ chỗ': the confirmed one, else where they were) and can
        be captured again; the copies left of the same endpoint keep its dedup memory.
        """
        for g in groups:
            self._drop_copy(g)
            self._hidden.pop(g.gid, None)
        self.forget_dedup(groups)
        for g in groups:
            if not g.book_key:
                continue
            left = self._copies_of(g.book_key)
            if self.places.deleted(g.book_key, g.gid, g.feature_name, left[0].gid if left else None) is not None:
                self.places.event("delete", g.book_key, g.gid, g.method, g.path, g.feature_name, None,
                                  note or (u"giữ chỗ: %s" % (self.places.get(g.book_key) or {}).get("place")))
        self._refresh_dup_totals()
        self._after_place_change()

    # ---- copies of one endpoint (duplicates)
    def _copies_of(self, key):
        return list(self._copies.get(key, [])) if key else []

    def _add_copy(self, g):
        with self._state_lock:
            self._copies.setdefault(g.book_key, []).append(g)
        self._refresh_dup_totals(g.book_key)

    def _drop_copy(self, g):
        with self._state_lock:
            lst = self._copies.get(g.book_key)
            if lst is not None:
                self._copies[g.book_key] = [c for c in lst if c is not g]
                if not self._copies[g.book_key]:
                    del self._copies[g.book_key]

    def _refresh_dup_totals(self, key=None):
        keys = [key] if key else list(self._copies.keys())
        for k in keys:
            copies = self._copies_of(k)
            for c in copies:
                c.dup_total = len(copies)

    def hidden_groups(self):
        return sorted(self._hidden.values(), key=lambda g: g.gid)

    def keep_duplicates(self, groups):
        """'Có': keep the duplicate at its new place (it stays numbered #2, #3 ... in the duplicate list)."""
        n = 0
        for g in groups:
            if getattr(g, "dup_pending", False):
                g.dup_pending = False
                g.pending = False
                self.places.event("dup_keep", g.book_key, g.gid, g.method, g.path, None, g.feature_name,
                                  u"bản trùng #%d" % g.dup_no)
                self._notify_results(g, None)
                n += 1
        if n:
            self._after_place_change()
        return n

    def hide_groups(self, groups, note=u""):
        """'Không': the API leaves the crawl screens but stays in the audit (can be shown again)."""
        groups = [g for g in groups if g.gid not in self._hidden]
        if not groups:
            return 0
        if self.group_model is not None:
            self.group_model.remove_groups(groups)
        for g in groups:
            g.hidden = True
            g.dup_pending = False
            g.pending = False
            self._hidden[g.gid] = g
            self.places.event("hide", g.book_key, g.gid, g.method, g.path, g.feature_name, None,
                              note or u"vẫn lưu trong Audit, bấm Hiện để đưa lại")
        self._refresh_feature_views()
        self._after_place_change()
        return len(groups)

    def show_groups(self, groups):
        groups = [g for g in groups if self._hidden.pop(g.gid, None) is not None]
        for g in groups:
            g.hidden = False
            self.places.event("show", g.book_key, g.gid, g.method, g.path, None, g.feature_name)
        if groups and self.group_model is not None:
            self.group_model.add_many(groups)
        self._refresh_feature_views()
        self._after_place_change()
        return len(groups)

    def edit_place(self, key, new_place):
        rec = self.places.get(key)
        if rec is None:
            return False
        old = rec.get("place")
        clean = normalize_hierarchy_path(new_place) if new_place else None
        self.places.set_place(key, clean)
        self.places.event("edit", key, rec.get("gid"), rec.get("method"), rec.get("path"), old, clean)
        self._after_place_change()
        return True

    def forget_place(self, key):
        rec = self.places.forget(key)
        if rec is not None:
            self.places.event("forget", key, rec.get("gid"), rec.get("method"), rec.get("path"), rec.get("place"), None)
            self._after_place_change()
        return rec is not None

    def add_manual_place(self, method, host, path, place, protocol="https", port=None):
        method = (method or "GET").upper()
        port = port or (443 if protocol == "https" else 80)
        key = dedup_key(method, protocol, host, port, path, self.config.get("dedup_normalize_ids", False))
        self.places.ensure(key, method, host, path)
        self.places.set_place(key, normalize_hierarchy_path(place))
        self.places.event("manual", key, None, method, path, None, normalize_hierarchy_path(place))
        self._after_place_change()
        return key

    def allow_recapture(self, key):
        """Drop the dedup memory of one endpoint so its next request is captured again."""
        n = 0
        with self._state_lock:
            for k in list(self._seen_keys):
                if k == key or k.endswith(u"|" + key):
                    self._seen_keys.discard(k)
                    self._seen_gid.pop(k, None)
                    n += 1
        rec = self.places.get(key) or {}
        self.places.event("recapture", key, rec.get("gid"), rec.get("method"), rec.get("path"), None, None,
                          u"%d khóa chống trùng đã xóa" % n)
        self._after_place_change()
        return n

    def feature_by_name(self, name):
        clean = normalize_hierarchy_path(name).lower()
        with self._state_lock:
            for f in self._features:
                if f.name.lower() == clean:
                    return f
        return None

    def _place_key(self, method, service, path, cfg=None):
        cfg = cfg or self.config
        return dedup_key(method, service.getProtocol(), service.getHost(), service.getPort(), path,
                         cfg.get("dedup_normalize_ids", False))

    def _save_places(self, force=False):
        book = self.places
        if not (book.dirty or force):
            return
        now = time.time()
        if not force and now - self._places_saved_at < 3.0:
            return
        self._places_saved_at = now
        try:
            self.callbacks.saveExtensionSetting(SETTINGS_KEY_PLACES, book.to_json())
        except (Throwable, Exception):
            self._print_error("Could not save the API places:\n%s" % u_text(traceback.format_exc()))

    def _auto_expand_api(self, gid):
        """Open a returning API in the trees so its 'vị trí cũ / vừa gặp tại' rows are visible."""
        def do():
            for name in ("left", "full"):
                self._tree_states[name]["expanded"].add(("G", gid))
        ui_call(do)

    @staticmethod
    def _load_ghosts(node, nodes=None):
        node.removeAllChildren()
        for rec in sorted(node.payload, key=lambda r: (u_text(r.get("path")), r.get("method"))):
            label = u"👻 %s %s   ·   xóa %d lần (lần cuối %s)   ·   gặp %d lần%s" % (
                rec.get("method"), short_path(rec.get("path") or u"", 60), rec.get("deleted", 0),
                rec.get("deleted_at") or u"-", rec.get("seen", 0),
                (u"   ·   lần cuối gặp tại %s" % rec["last_found_at"]) if rec.get("last_found_at") else u"")
            child = HierarchyTreeNode("GHOST", rec, label, key=("GHO", rec.get("key")))
            node.add(child)
            if nodes is not None:
                nodes[child.key] = child
        node.loaded = True

    def forget_dedup(self, groups):
        """Deleted APIs are captured again the next time you pass by them (their dedup keys are dropped)."""
        n = 0
        with self._state_lock:
            for g in groups:
                key = getattr(g, "dedup_key", None)
                if key is None or self._seen_gid.get(key) != g.gid:
                    continue
                left = [c for c in self._copies.get(g.book_key, []) if c is not g]
                if left:
                    self._seen_gid[key] = left[0].gid      # another copy still stands for this endpoint
                    continue
                self._seen_keys.discard(key)
                del self._seen_gid[key]
                n += 1
        if n:
            self.log("Đã xóa %d API: lần sau đi qua chúng sẽ được bắt lại." % n)
        return n


class _WorkbenchMixin(object):
    """Copy STT + path, Excel jumps and hit audit, role scopes, detached window, tree viewers.
    Kept out of BurpExtender: Jython limits the size of one class body."""

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
        ev = getattr(self._group_cell_click, "last_event", None)
        if ev is not None:
            self._chip_anchor = (self.group_table, ev.getX(), ev.getY())
        kind = {GroupTableModel.COPY_COL: "copy", GroupTableModel.EXCEL_COL: "excel",
                GroupTableModel.DUP_COL: "dup"}.get(model_col)
        self.on_chip(kind, g)

    def on_chip(self, kind, g):
        if kind == "copy":
            line = self.copy_groups([g])
            self._flash_status(u"📋 Đã copy: %s" % line)
        elif kind == "dup":
            if getattr(g, "dup_total", 1) > 1:
                self.show_dup_popup(g)
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
        dup = dup_badge(g)
        if dup and dup in text:
            fm = comp.getFontMetrics(comp.getFont())
            start = (icon.getIconWidth() if icon is not None else 0) + comp.getIconTextGap() + \
                fm.stringWidth(text[:text.index(dup)])
            if start - 2 <= rel <= start + fm.stringWidth(dup) + 2:
                return "dup", g
        return None

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
        self.btn_detach.setText(u"🗗 Gắn lại")
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
        self.btn_detach.setText(u"🗗")
        self._ensure_tree_renderers()

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


class BurpExtender(_PlacementMixin, _WorkbenchMixin, IBurpExtender, ITab, IHttpListener,
                   IContextMenuFactory, IExtensionStateListener):

    # ------------------------------------------------------------------ setup
    def registerExtenderCallbacks(self, callbacks):
        global _CORE_ERROR
        if _CORE_ERROR is not None:
            try:
                _load_tmoc_core(os.path.dirname(os.path.abspath(callbacks.getExtensionFilename())))
                _CORE_ERROR = None
            except ImportError as e:
                callbacks.printError("theMythOfCrawl: tmoc_core.py must be in the same folder as theMythOfCrawl.py "
                                     "(%s)" % e)
                raise
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
        self.places = PlacementBook()
        self._copies = {}
        self._hidden = {}
        self._stale_places = True
        self._places_saved_at = 0.0
        try:
            self.places.load_json(callbacks.loadExtensionSetting(SETTINGS_KEY_PLACES))
        except (Throwable, Exception):
            callbacks.printError("Could not load the stored API places: %s" % u_text(traceback.format_exc()))
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
            self._save_places(True)
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
        self._save_places()
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
            self._refresh_destination_bar()

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
        table = getattr(self, "places_panel", None)
        if self._stale_places and table is not None and table.isShowing():
            self._stale_places = False
            self._reload_places()
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
        self.move_groups_to_feature([group], feat.fid, confirm=True)

    # ---- capture destination ("Request mới sẽ vào ...")
    # ---- "Vị trí & Audit" tab
    # ---- placement: confirm / move / revert (every change goes to the placement log)
    # ---- placement book: add / edit / forget / allow recapture
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
        n_places = self.places.rename_prefix(old_clean, new_clean)
        self.places.event("rename", None, None, u"", u"", old_clean, new_clean, u"%d vị trí giữ chỗ cập nhật" % n_places)
        self._stale_places = True

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
                    self.on_groups_removed(matched, u"xóa cả nhánh %s" % clean_prefix)
                elif matched:
                    self.move_groups_to_feature(matched, fallback_feat.fid,
                                                note=u"nhánh %s bị xóa, API chuyển lên nhánh cha" % clean_prefix)
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

    def move_groups_to_feature(self, groups, fid, action="move", confirm=False, note=u"", push_history=True):
        feat = self.get_feature(fid)
        if feat is None or not groups:
            return 0
        cfg = self.get_config()
        moved = 0
        for g in groups:
            old = g.feature_name
            if old != feat.name:
                moved += 1
                if push_history:
                    g.place_history.append(old)
                    del g.place_history[:-30]
            if confirm and getattr(g, "pending", False):
                g.pending = False
                g.place_hint = None
                if g.book_key:
                    self.places.update(g.book_key, pending=False)
            if old != feat.name or confirm:
                if g.book_key and not getattr(g, "pending", False):
                    self.places.set_place(g.book_key, feat.name)
                self.places.event(action, g.book_key, g.gid, g.method, g.path, old, feat.name,
                                  note + (u" (đã xác nhận)" if confirm and old == feat.name else u""))
            g.fid = feat.fid
            g.feature_name = feat.name
            g.sync_original_meta(cfg["short_path_len"], cfg["include_feature_in_tab"])
            for r in g.results:
                r.tab_name = repeater_tab_name(g.gid, g.method, g.path, r.role_name,
                                               cfg["short_path_len"], g.fid, cfg["include_feature_in_tab"])
        if self.group_model is not None:
            self.group_model._rebuild_view()
            self.group_model.fireTableDataChanged()
        self._after_place_change()
        self._refresh_feature_views()
        self.update_status()
        return moved

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
                    # Same endpoint met again: skipped, unless it shows up at a NEW place (another
                    # branch than every copy so far) - then it becomes a duplicate copy to decide on.
                    pkey = self._place_key(method, service, path, cfg)
                    copies = self._copies_of(pkey)
                    places = set([c.feature_name.lower() for c in copies])
                    if not (cfg.get("dup_new_place", True) and copies and feat.name.lower() not in places):
                        hit(HIT_DUP, earlier)
                        self.places.ensure(pkey, method, service.getHost(), path)
                        self.places.seen(pkey, standing, skipped=True)
                        if source == "Manual":
                            self.log("Skipped %s %s (duplicate endpoint)" % (method, url))
                        self.update_status()
                        return

        # Placement: a deleted API that comes back returns to its remembered place ('giữ chỗ');
        # a duplicate met at a new place asks whether to keep it there; new APIs wait (grey) for a
        # confirmation of their place when that option is on.
        pkey = self._place_key(method, service, path, cfg)
        rec = self.places.get(pkey)
        copies = self._copies_of(pkey)
        pending = bool(cfg.get("confirm_new_apis", True))
        action = "pending" if pending else "capture"
        hint = None
        if copies:
            pending = True
            action = "dup"
        elif (rec is not None and rec.get("place") and cfg.get("restore_known_place", True)
                and rec["place"].lower() != feat.name.lower()):
            old_exists = self.feature_by_name(rec["place"]) is not None
            found_at = feat.name
            feat = self.find_or_create_feature_by_path(rec["place"])
            hint = {"old": feat.name, "found": found_at, "old_missing": not old_exists,
                    "deleted": rec.get("deleted", 0)}
            pending = True
            action = "return"

        # Roles are optional: with none enabled the API is still captured, stored and shown
        # ("1 API gốc + 0 role") and every send / Repeater action falls back to the original.
        roles = effective_roles(self.roles.all(), feat.name, self.role_branch_rules)

        with self._state_lock:
            gid = self._next_gid
            self._next_gid += 1

        group = ApiGroup(gid, service, method, path, "%s" % url, req, resp, source,
                         feat.fid, feat.name)
        group.book_key = pkey
        group.pending = pending
        group.place_hint = hint
        rec = self.places.ensure(pkey, method, service.getHost(), path)
        group.dup_no = self.places.next_copy_no(pkey)
        group.dup_pending = bool(copies)
        self._add_copy(group)
        if not copies:
            self.places.update(pkey, gid=gid, pending=pending)
        self.places.seen(pkey, standing)
        if not pending:
            self.places.set_place(pkey, feat.name)
        if copies:
            first = sorted(copies, key=lambda c: c.dup_no)[0]
            self.places.event("dup", pkey, gid, method, path, first.feature_name, feat.name,
                              u"bản #%d; bản #%d (API #%d) đang ở %s" % (group.dup_no, first.dup_no, first.gid,
                                                                       first.feature_name))
        elif hint is not None:
            note = u"từng ở đây (đã xóa %d lần); vừa gặp tại %s%s" % (
                hint["deleted"], hint["found"], u"; nhánh cũ đã bị xóa nên được tạo lại" if hint["old_missing"] else u"")
            self.places.event("return", pkey, gid, method, path, hint["found"], feat.name, note)
            self._auto_expand_api(gid)
        else:
            self.places.event(action, pkey, gid, method, path, standing if standing != feat.name else None,
                              feat.name, u"theo dòng Excel" if target is not None and target.position else u"")
        group.message_builder = self._build_message
        group.target = target
        if key is not None:
            group.dedup_key = key
            with self._state_lock:
                self._seen_gid[key] = gid
        hit(HIT_NEW, gid)
        self._stale_places = True
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
        self.btn_send_mode = JButton(" ", actionPerformed=self._on_toggle_send_mode)
        self.btn_send_mode.setFont(Font("Dialog", Font.BOLD, 12))
        self.btn_send_mode.setMargin(Insets(2, 8, 2, 8))
        self.btn_queue = JButton("Hàng đợi: 0", actionPerformed=self._on_cancel_queue)
        self.btn_queue.setMargin(Insets(2, 6, 2, 6))
        self.btn_capture_opts.setText(u"⚙ ▾")
        self.btn_capture_opts.setToolTipText(u"Tùy chọn: phạm vi bắt, regex, tự gửi, xác nhận vị trí, giữ chỗ, API trùng...")
        # The path chips / text field stay alive (off-screen) for the existing path actions; the
        # destination button and its menu replace them in the header.
        left_header.add(self.cb_capture)
        left_header.add(self.btn_send_mode)
        left_header.add(self.btn_queue)
        left_header.add(info_icon(HELP["capture"], u"Bắt & gửi"))
        left_header.add(JLabel(u" │ "))
        left_header.add(self._build_header_bar(cfg))
        left_header.add(JLabel(u" │ "))
        left_header.add(self.btn_capture_opts)
        self.btn_detach = JButton(u"🗗", actionPerformed=self._on_toggle_detach)
        self.btn_detach.setMargin(Insets(1, 6, 1, 6))
        self.btn_detach.setToolTipText(u"Tách cả extension ra cửa sổ riêng (bấm lại / đóng cửa sổ để gắn vào tab Burp)")
        left_header.add(self.btn_detach)

        right_header = JPanel(FlowLayout(FlowLayout.LEFT, 4, 0))
        self.status_label = JLabel("")
        self.status_label.setFont(Font("Dialog", Font.PLAIN, 11))
        bg, fg = _ui_colors()
        self.status_label.setForeground(_mix(fg, bg, 0.30))
        right_header.add(info_icon(HELP["colors"], u"Màu & nhãn"))
        right_header.add(self.status_label)

        self._rebuild_subfolder_chips(self.active_feature().name)
        top_container.add(left_header, BorderLayout.NORTH)
        top_container.add(right_header, BorderLayout.SOUTH)
        self.main_panel.add(top_container, BorderLayout.NORTH)

        self.tabs = JTabbedPane()
        for title, builder, tip in (
                (u"API", self._build_groups_tab, u"Danh sách API đã bắt, kết quả từng role, Repeater gộp"),
                (u"Lịch sử", self._build_history_tab, u"Cây lịch sử theo nhánh và báo cáo"),
                (u"Roles", self._build_roles_tab, u"Các role / profile (header, cookie, JWT) và profile API gốc"),
                (u"Cấu hình", lambda: self._build_settings_tab(cfg), u"Bộ lọc bắt, tốc độ gửi, Excel, copy"),
                (u"Log", self._build_log_tab, u"Nhật ký theo nhánh / API, xuất Excel"),
                (u"Excel", self._build_coverage_tab, u"Đối chiếu file Excel: dòng nào đã bắt, số lần gặp, ở đâu"),
                (u"Cây", self._build_tree_tab, u"Cây nhánh cỡ lớn, mở được cửa sổ riêng, có Request / Response"),
                (u"Audit", self._build_places_tab, u"Cần xử lý, giữ chỗ, API trùng & ẩn, nhật ký vị trí")):
            self.tabs.addTab(title, None, builder(), tip)
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
        self.left_hierarchy_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION)
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
        dup_col = cm.getColumn(GroupTableModel.DUP_COL)
        dup_col.setPreferredWidth(56)
        dup_col.setMinWidth(52)
        excel_col.setMinWidth(70)
        dup_col.setCellRenderer(_ActionCellRenderer(
            self.group_model, "dup", lambda r: u"API trùng: bấm để xem nhanh các bản" if
            getattr(self.group_model.group_at(r), "dup_total", 1) > 1 else None))
        # 'Copy' first, 'Excel' and 'Trùng' right after Method (the other columns keep their model index)
        cm.moveColumn(GroupTableModel.COPY_COL, 0)
        cm.moveColumn(GroupTableModel.EXCEL_COL, 6)
        cm.moveColumn(GroupTableModel.DUP_COL, 7)
        cell_click = _TableCellClick(self.group_table, (GroupTableModel.COPY_COL, GroupTableModel.EXCEL_COL,
                                                        GroupTableModel.DUP_COL), self._on_group_cell_click)
        self._group_cell_click = cell_click
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
        self.full_tree.getSelectionModel().setSelectionMode(TreeSelectionModel.DISCONTIGUOUS_TREE_SELECTION)
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
            ("➜ Đặt nhánh đang chọn làm ĐÍCH cho request mới", lambda: self._on_dest_from_tree()),
            ("✔ Xác nhận vị trí các API đang chọn / trong nhánh", lambda: self.confirm_groups(self._selected_tree_groups())),
            ("↪ Chuyển các API đang chọn sang đường dẫn khác...", lambda: self.open_move_dialog(self._selected_tree_groups())),
            ("↶ Đưa các API đang chọn về vị trí trước", lambda: self._on_revert(self._selected_tree_groups())),
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
        label.setText("➜ Request mới sẽ vào: %s   ·   %d nhánh, %d API   ·   Chuột phải để Gửi / Đẩy / Thêm / Sửa / Xóa; "
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
                                      lambda g: self.copy_label_for(g, assign=False), self.target_hits, self.places)
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
            "confirm_new_apis": self.config.get("confirm_new_apis", True),
            "restore_known_place": self.config.get("restore_known_place", True),
            "dup_new_place": self.config.get("dup_new_place", True),
            "show_ghosts": self.config.get("show_ghosts", True),
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
        cfg = self.get_config()
        for label, key in ((u"Hỏi xác nhận vị trí API mới (màu xám)", "confirm_new_apis"),
                           (u"API đã xóa quay về chỗ cũ (giữ chỗ)", "restore_known_place"),
                           (u"Gặp API trùng ở chỗ mới: hỏi giữ thêm bản (màu tím)", "dup_new_place"),
                           (u"Hiện API đã xóa (👻 giữ chỗ) trong cây", "show_ghosts")):
            item = JCheckBoxMenuItem(label, bool(cfg.get(key, True)))
            item.addActionListener(_Action(lambda e, k=key, it=item: self._set_place_option(k, it.isSelected())))
            menu.add(item)
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
        self._add_place_items(menu, groups)
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
                menu.add(JMenuItem("➜ Đặt \"%s\" làm ĐÍCH cho request mới" % title,
                                   actionPerformed=lambda e, p=prefix: self.set_destination(p)))
                menu.addSeparator()
                self._add_place_items(menu, self._selected_tree_groups(), branch=prefix)
                menu.addSeparator()
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
            menu.addSeparator()
            self._add_place_items(menu, self._selected_tree_groups() or [g])
        elif kind == "PLACE" and payload is not None:
            g, place, which = payload
            if which == "old":
                menu.add(JMenuItem(u"✔ Giữ API #%d ở vị trí cũ: %s" % (g.gid, place),
                                   actionPerformed=lambda e: self.confirm_groups([g], u"giữ ở vị trí cũ")))
            else:
                menu.add(JMenuItem(u"↪ Chuyển API #%d sang nơi vừa gặp: %s" % (g.gid, place),
                                   actionPerformed=lambda e: self.move_groups_to_path([g], place, note=u"chọn nơi vừa gặp")))
            menu.add(JMenuItem(u"↪ Chuyển sang đường dẫn khác...", actionPerformed=lambda e: self.open_move_dialog([g])))
            menu.add(JMenuItem(u"🧭 Lịch sử vị trí của API này", actionPerformed=lambda e: self.show_place_of(g.book_key)))
        elif kind == "GHOSTS" and payload is not None:
            menu.add(JMenuItem(u"🧭 Xem %d API đã xóa trong tab Vị trí & Audit" % len(payload),
                               actionPerformed=lambda e: self.show_place_of(None, view=2)))
        elif kind == "GHOST" and payload is not None:
            rec = payload
            menu.add(JMenuItem(u"✏ Sửa vị trí giữ chỗ (%s)..." % (rec.get("place") or u"-"),
                               actionPerformed=lambda e: self._on_edit_place(rec)))
            menu.add(JMenuItem(u"♻ Cho phép bắt lại ngay (xóa khóa chống trùng)",
                               actionPerformed=lambda e: self._flash_status(
                                   u"♻ Đã xóa %d khóa chống trùng" % self.allow_recapture(rec["key"]))))
            menu.add(JMenuItem(u"✖ Quên giữ chỗ (lần sau bắt lại sẽ vào đích hiện tại)",
                               actionPerformed=lambda e: self.forget_place(rec["key"])))
            menu.add(JMenuItem(u"🧭 Lịch sử trong tab Vị trí & Audit", actionPerformed=lambda e: self.show_place_of(rec["key"])))
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
        pend = {}
        for g in stats.groups:
            if getattr(g, "pending", False):
                low = [x.lower() for x in split_hierarchy_path(g.feature_name)]
                for i in range(len(low)):
                    k = " > ".join(low[:i + 1])
                    pend[k] = pend.get(k, 0) + 1
        ghosts = {}
        ghost_count = {}
        if getattr(self, "places", None) is not None and self.config.get("show_ghosts", True):
            for rec in list(self.places.entries.values()):
                if rec.get("gid") is None and rec.get("place"):
                    low = [x.lower() for x in split_hierarchy_path(rec["place"])]
                    ghosts.setdefault(" > ".join(low), []).append(rec)
                    for i in range(len(low)):
                        k = " > ".join(low[:i + 1])
                        ghost_count[k] = ghost_count.get(k, 0) + 1

        def ensure_folder_chain(parts):
            parent = root
            lowered = [p.lower() for p in parts]
            for idx in range(len(parts)):
                key = ("F", " > ".join(lowered[:idx + 1]))
                node = nodes.get(key)
                if node is None:
                    total, flagged, ok = stats.prefix.get(key[1], (0, 0, 0))
                    lvl, summary = audit_from_counts(total, flagged, ok)
                    extra = u""
                    if pend.get(key[1]):
                        extra += u"   ·   ⏳ %d chờ xác nhận" % pend[key[1]]
                    if ghost_count.get(key[1]):
                        extra += u"   ·   👻 %d đã xóa (giữ chỗ)" % ghost_count[key[1]]
                    node = HierarchyTreeNode(
                        "FOLDER", " > ".join(parts[:idx + 1]),
                        u"%s   ·   %d API   ·   %s%s" % (parts[idx], total, summary, extra),
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
                "GROUP", g, group_tree_label(g, g_audit), audit_level=display_level(g), key=key)
            nodes[key] = node
            if id(leaf) in open_ids and key in expanded:
                self._load_group_children(node, nodes)
                expand.append(node)
            else:
                node.loaded = False
                node.add(HierarchyTreeNode("LOADING", None, "..."))
            leaf.add(node)
        for fkey, recs in ghosts.items():
            folder = nodes.get(("F", fkey))
            if folder is None:
                continue
            gkey = ("GH", fkey)
            gnode = HierarchyTreeNode("GHOSTS", recs, u"👻 %d API đã xóa từng nằm ở đây (giữ chỗ - bắt lại sẽ về đây)"
                                      % len(recs), key=gkey)
            nodes[gkey] = gnode
            if id(folder) in open_ids and gkey in expanded:
                self._load_ghosts(gnode, nodes)
                expand.append(gnode)
            else:
                gnode.loaded = False
                gnode.add(HierarchyTreeNode("LOADING", None, "..."))
            folder.add(gnode)
        return root, nodes, expand

    @staticmethod
    def _load_group_children(g_node, nodes=None):
        """Replace an API node's placeholder with its real rows: 1 original + N roles."""
        g = g_node.payload
        g_node.removeAllChildren()
        hint = getattr(g, "place_hint", None)
        if hint:
            old = HierarchyTreeNode("PLACE", (g, hint["old"], "old"), u"📍 Vị trí cũ (giữ chỗ): %s   ·   đang đặt ở đây%s"
                                    % (hint["old"], u" · nhánh cũ đã bị xóa nên được tạo lại" if hint.get("old_missing") else u""),
                                    key=("P", g.gid, "old"))
            found = HierarchyTreeNode("PLACE", (g, hint["found"], "found"),
                                      u"🆕 Vừa gặp tại: %s   ·   chuột phải để chuyển sang đây" % hint["found"],
                                      key=("P", g.gid, "found"))
            for child in (old, found):
                g_node.add(child)
                if nodes is not None:
                    nodes[child.key] = child
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
            "GHOSTS": self._load_ghosts,
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
        if tree.getSelectionCount() > 1:
            n = len(self._selected_tree_groups(tree))
            self._flash_status(u"Đang chọn %d mục trong cây = %d API (Ctrl / Shift + click để thêm bớt)"
                               % (tree.getSelectionCount(), n))
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
        many = self._many_selected_in_tree()
        if many is not None:
            for g in many:
                self.replay(g, self.default_targets(g))
            self._flash_status(u"▶ Xếp hàng gửi %d API đang chọn" % len(many))
            return
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
    # ---- 'Đẩy / Gửi có chọn Role'
    def _selected_tree_groups(self, tree=None):
        """APIs of every selected node of a tree (Ctrl / Shift + click selects several)."""
        tree = tree or getattr(self, "_menu_tree", None) or getattr(self, "left_hierarchy_tree", None)
        out = []
        seen = set()
        for path in (tree.getSelectionPaths() if tree is not None else None) or []:
            kind, payload = self._extract_node_kind_payload(path.getLastPathComponent())
            if kind == "ROOT":
                found = self.group_model.all_groups()
            elif kind == "FOLDER" and payload:
                found = self.groups_for_hierarchy_prefix(payload)
            elif kind == "GROUP" and payload is not None:
                found = [payload]
            elif kind in ("ROLE", "ORIG", "PLACE") and payload is not None:
                found = [payload[0]]
            else:
                found = []
            for g in found:
                if id(g) not in seen:
                    seen.add(id(g))
                    out.append(g)
        return out

    def _groups_in_scope(self):
        """(groups, label): selected rows of the API table, else the selected tree node(s) / branch."""
        groups = self._selected_groups() if self.group_table is not None else []
        if groups and getattr(self, "_scope_source", "table") == "table":
            return groups, ("%d API đang chọn" % len(groups)) if len(groups) > 1 else format_api_label(groups[0].gid)
        tree = getattr(self, "_menu_tree", None) or getattr(self, "left_hierarchy_tree", None)
        if tree is not None and tree.getSelectionCount() > 1:
            many = self._selected_tree_groups(tree)
            return many, "%d mục chọn trong cây (%d API)" % (tree.getSelectionCount(), len(many))
        kind, payload = self._selected_left_tree_payload()
        if kind == "PLACE" and payload is not None:
            return [payload[0]], format_api_label(payload[0].gid)
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

    def _many_selected_in_tree(self):
        tree = getattr(self, "_menu_tree", None) or getattr(self, "left_hierarchy_tree", None)
        if tree is not None and tree.getSelectionCount() > 1 and getattr(self, "_scope_source", "") == "tree":
            return self._selected_tree_groups(tree)
        return None

    def _on_send_selected_hierarchy_repeater(self, event):
        many = self._many_selected_in_tree()
        if many is not None:
            for g in many:
                self._dispatch_group_with_selected_mode(g)
            self._flash_status(u"📤 Đã đẩy %d API đang chọn sang Repeater" % len(many))
            return
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
        return self.open_move_dialog(groups)

    def _on_move_groups_feature_old(self, groups):
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
        self.on_groups_removed(groups)
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
        self.on_groups_removed(self.group_model.all_groups() + self.hidden_groups(), u"Xóa toàn bộ")
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
