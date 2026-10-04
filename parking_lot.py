"""
Park That Thought (formerly Parking Lot): a floating capture pad for fleeting thoughts during focus sessions.

Setup (once):   pip install PySide6 pynput
Run:            pythonw parking_lot.py      (pythonw = no console window)

- Round bubble on the screen edge. Drag it to move it. Drop files/text/images on it = new task.
- Scribble the mouse up-down (slant is fine) or Ctrl+Alt+P = private quick note box: one empty
  line, no tasks visible. Safe in front of anyone. Drop files/text on it too.
- Scribble left-right, click the bubble, or Ctrl+Alt+L = full list. Hotkeys are configurable.
- Type a thought + Enter = new task. Ctrl+V a snip in the top box = new task with image.
- Ctrl+V inside a task (title or details) = attach image / copied files to that task.
- Drop files onto a task card = attach (text = appended to details). Drop on empty list = new task.
- Hover an attachment = copy button. Double-click = open. Right-click = more.
- Up/down arrows (or Alt+Up / Alt+Down while typing in a task) = reorder.
- "urge" = feels urgent, can wait. Parked, no guilt.
- Tabs = separate lists. "+" makes one (default name = today's date). Double-click a tab to rename,
  right-click to delete, drag to reorder, Ctrl+Tab to switch.
- Focus timer (right-click the bubble): your own duration, shown as a calm ring, mm:ss or hidden.
  Finishing throws confetti; every session is logged to parking_lot_data/focus_log.jsonl.
- All app windows are hidden from screen share/recording by default (you still see them).

All data lives in ./parking_lot_data next to this script (tasks.json + attachments).
Nothing is ever hard-deleted: cleared tasks and removed files go to ./parking_lot_data/trash.
"""
import csv
import base64
from calendar import monthrange
import hashlib
import html
import http.server
import io
import json
import math
import random
import re
import secrets
import os
import shutil
import subprocess
import sys
import threading
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request
import weakref
import wave
from datetime import datetime, timedelta, timezone
from pathlib import Path

from PySide6.QtCore import QEasingCurve, QEvent, QLockFile, QProcess, QRect, QVariantAnimation, QMimeData, QObject, QPoint, QPointF, QRectF, Qt, QTimer, QUrl, Signal
from PySide6.QtGui import (QColor, QDesktopServices, QFont, QGuiApplication, QImage, QIntValidator, QKeySequence,
                           QPainter, QPen, QPixmap, QShortcut)
from PySide6.QtWidgets import (QApplication, QCheckBox, QDialog, QDialogButtonBox, QFormLayout, QFrame,
                               QGridLayout, QHBoxLayout, QKeySequenceEdit, QLabel, QLineEdit,
                               QDoubleSpinBox, QMenu, QMessageBox, QPushButton, QScrollArea, QTabBar,
                               QToolButton, QToolTip, QVBoxLayout, QWidget)
from PySide6.QtGui import QActionGroup, QConicalGradient, QLinearGradient, QPainterPath, QRadialGradient, QTextCursor
from PySide6.QtNetwork import QLocalServer, QLocalSocket
from PySide6.QtWidgets import QAbstractButton, QGraphicsOpacityEffect, QPlainTextEdit, QSizePolicy, QTextEdit
from PySide6.QtCore import QPropertyAnimation, QDate, QDateTime, QTime, QTimeZone
from PySide6.QtWidgets import QButtonGroup, QDateEdit, QDateTimeEdit, QTimeEdit, QSlider, QStackedWidget
from PySide6.QtCore import QSize
from PySide6.QtGui import QCursor, QFontMetrics
from PySide6.QtWidgets import QComboBox, QListWidget, QListWidgetItem, QSplitter
from PySide6.QtWidgets import QFileDialog
from PySide6.QtWidgets import QColorDialog
from PySide6.QtWidgets import QSpinBox, QSizeGrip

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = APP_DIR / "parking_lot_data"
MUSIC_DIR = APP_DIR / "music"         # songs the owner drops in; played on repeat from the circle's menu
ATT_DIR = DATA_DIR / "attachments"
TRASH_DIR = DATA_DIR / "trash"
BACKUP_DIR = DATA_DIR / "backups"
DB_FILE = DATA_DIR / "tasks.json"
LOG_FILE = DATA_DIR / "error.log"
# Rescue copy lives OUTSIDE OneDrive, so a locked/synced folder can never lose a save.
APP_NAME = "Park That Thought"   # display name only; files, folders and IDs keep the old "parking lot" names
APP_TAGLINE = "Park stray thoughts, files and images. Get back to work."
APP_VERSION = "1.1"
APP_AUTHOR = "G M Iqbal Mahmud"
GITHUB_URL = "https://github.com/gmiqbal/ParkThatThought"
UPDATE_URL = "https://raw.githubusercontent.com/gmiqbal/ParkThatThought/main/parking_lot.py"   # Restart / update
COFFEE_URL = ""        # fill in to turn on About > Buy me a coffee
RESCUE_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "ParkingLotRescue"
RESCUE_FILE = RESCUE_DIR / "tasks.rescue.json"
BACKUP_KEEP_DAYS = 14
# one running copy per data folder; a second launch asks the running one to show itself
SERVER_NAME = "ParkingLot-" + hashlib.md5(str(DATA_DIR).lower().encode()).hexdigest()[:12]


def log_error(msg):
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"{datetime.now():%Y-%m-%d %H:%M:%S}  {msg}\n")
    except Exception:
        pass

# Scribble gesture tuning. Raise REVERSALS if it opens by accident; lower it if it's hard to trigger.
SCRIBBLE_REVERSALS = 5        # direction changes needed
SCRIBBLE_WINDOW_S = 1.0       # ...within this many seconds
SCRIBBLE_MIN_SEG_PX = 25      # each stroke at least this long
SCRIBBLE_MAX_SEG_PX = 450     # a longer sweep is normal mouse use, resets the count
SCRIBBLE_HYST_PX = 10         # ignore hand jitter smaller than this
SCRIBBLE_COOLDOWN_S = 1.5
GESTURE_NEAR_PX = 320         # default "near the circle": the scribble ends within this many px of its centre
# scribble sensitivity, 1 (hard to set off) .. 5 (very easy): (direction changes needed, shortest stroke px)
SCRIBBLE_LEVELS = {1: (7, 45), 2: (6, 35), 3: (5, 25), 4: (4, 20), 5: (3, 15)}
SCRIBBLE_LEVEL_NAMES = {1: "Hard to set off", 2: "Firm", 3: "Balanced", 4: "Easy", 5: "Very easy"}
SCRIBBLE_TUNE = {"revs": 5, "min_seg": 25}   # set from the "scribble_level" setting
SCRIBBLE_MAX_TILT = 0.84      # sideways drift allowed per stroke (0.84 = about 40 degrees off vertical)

# Default global hotkeys (change them any time: right-click the circle > Hotkeys...).
DEFAULT_HOTKEY_QUICK = "Ctrl+Alt+P"   # private one-line quick note
DEFAULT_HOTKEY_PANEL = "Ctrl+Alt+L"   # full list
DEFAULT_FOCUS_MIN = 25
DEFAULT_BREAK_MIN = 5
DEFAULT_NAP_PRESETS = [15, 18, 23]
DEFAULT_CALENDAR_ALERTS = [30, 10, 5]


def meeting_bar_minimum(settings):
    """User chosen minimum width and height, with safe bounds for small screens."""
    try:
        width = max(120, min(600, int(settings.get("meeting_bar_min_width", 240))))
        height = max(32, min(180, int(settings.get("meeting_bar_min_height", 56))))
        return width, height
    except (TypeError, ValueError):
        return 240, 56


def meeting_bar_placement(settings):
    value = settings.get("meeting_bar_placement")
    return value if value in ("taskbar", "floating") else ("taskbar" if IS_WIN else "floating")


def meeting_bar_taskbar_strip(screen):
    """Qt screen coordinates for a horizontal Windows taskbar, if it reserves enough room."""
    if not IS_WIN or screen is None:
        return None
    full, work = screen.geometry(), screen.availableGeometry()
    top = work.top() - full.top()
    bottom = full.bottom() - work.bottom()
    if max(top, bottom) < 36:
        return None  # auto-hidden taskbar, or a vertical one
    if top >= bottom:
        return QRect(full.left(), full.top(), full.width(), top)
    return QRect(full.left(), work.bottom() + 1, full.width(), bottom)


def meeting_bar_background(settings):
    """A chosen solid color, or the theme's default surface."""
    color = QColor(str(settings.get("meeting_bar_bg") or ""))
    return color.name() if color.isValid() else C["surface_hi"]


def calendar_alert_minutes(settings):
    """Up to three quiet heads-ups before an event; zero disables a slot."""
    raw = settings.get("calendar_alert_minutes", DEFAULT_CALENDAR_ALERTS)
    if not isinstance(raw, list):
        return list(DEFAULT_CALENDAR_ALERTS)
    try:
        return sorted({max(0, min(240, int(n))) for n in raw[:3]} - {0}, reverse=True)
    except (TypeError, ValueError):
        return list(DEFAULT_CALENDAR_ALERTS)


def calendar_flow_minutes(settings):
    try:
        return max(1, min(60, int(settings.get("calendar_urgent_minutes", 5))))
    except (TypeError, ValueError):
        return 5


def meeting_glint_style(settings):
    style = settings.get("meeting_glint_style", "triple")
    return style if style in ("off", "sun", "triple", "prism") else "triple"


def nap_presets(settings):
    """Three editable break lengths, with safe defaults for older or malformed settings."""
    raw = settings.get("nap_presets", DEFAULT_NAP_PRESETS)
    if not isinstance(raw, list) or len(raw) != 3:
        return list(DEFAULT_NAP_PRESETS)
    try:
        return [max(1, min(120, int(n))) for n in raw]
    except (TypeError, ValueError):
        return list(DEFAULT_NAP_PRESETS)
NTFY_SERVER = "https://ntfy.sh"   # free push notifications to your phone (ntfy app), no account
FOCUS_LOG = DATA_DIR / "focus_log.jsonl"
THOUGHT_LOG = DATA_DIR / "thought_log.jsonl"   # append-only history of every thought, never pruned
EXPORT_DIR = DATA_DIR / "exports"
AI_NOTES = DATA_DIR / "ai_analyses.jsonl"   # AI analyses you saved back, fed into the next export

# Hide our windows from screen share / recording (you still see them). Toggle via bubble menu.
PRIVACY = {"hide_from_share": True}
IS_WIN = sys.platform.startswith("win")


def apply_share_privacy(w):
    """WDA_EXCLUDEFROMCAPTURE: window is invisible to Zoom/Teams/Meet share and screenshots (Win10 2004+)."""
    if not IS_WIN:
        return
    try:
        import ctypes
        hwnd = int(w.winId())
        mode = 0x11 if PRIVACY["hide_from_share"] else 0x0
        if not ctypes.windll.user32.SetWindowDisplayAffinity(hwnd, mode) and mode:
            ctypes.windll.user32.SetWindowDisplayAffinity(hwnd, 0x1)  # older Windows: shows black instead
    except Exception as e:
        log_error(f"share privacy failed: {e}")


def screen_for(w, point):
    """The screen under point. Also moves window w onto it first, so Windows sizes it with that screen's
    scaling (a window last shown on a TV at a different scale otherwise opens huge or off screen)."""
    screen = QGuiApplication.screenAt(point) or QGuiApplication.primaryScreen()
    try:
        if w is not None and not w.isVisible() and w.screen() is not screen:   # never re-create a shown window
            w.setScreen(screen)
    except (AttributeError, RuntimeError):
        pass
    return screen


def mouse_button_down():
    """Is a mouse button held anywhere on screen (e.g. dragging a file from Explorer)? Windows only."""
    if not IS_WIN:
        return False
    try:
        import ctypes
        u = ctypes.windll.user32
        return any(u.GetAsyncKeyState(vk) & 0x8000 for vk in (0x01, 0x02))   # VK_LBUTTON, VK_RBUTTON
    except Exception:
        return False


def _fg_pid(u, ctypes):
    fg = u.GetForegroundWindow()
    pid = ctypes.c_ulong(0)
    if fg:
        u.GetWindowThreadProcessId(ctypes.c_void_p(fg), ctypes.byref(pid))
    return fg, pid.value


def foreign_foreground():
    """The window you're in right now, if it belongs to another app (else None). Windows only."""
    if not IS_WIN:
        return None
    try:
        import ctypes
        u = ctypes.windll.user32
        u.GetForegroundWindow.restype = ctypes.c_void_p
        fg, pid = _fg_pid(u, ctypes)
        return fg if fg and pid != os.getpid() else None
    except Exception:
        return None


def foreground_app():
    """(app, window title) of the window you're in, e.g. ("code", "parking_lot.py - VS Code"), or None when
    it's ours or unknown. Used only by opt-in app tracking; stays on this PC. Windows only."""
    if not IS_WIN:
        return None
    try:
        import ctypes
        u, k = ctypes.windll.user32, ctypes.windll.kernel32
        u.GetForegroundWindow.restype = ctypes.c_void_p
        fg, pid = _fg_pid(u, ctypes)
        if not fg or pid == os.getpid():
            return None
        buf = ctypes.create_unicode_buffer(512)
        u.GetWindowTextW(ctypes.c_void_p(fg), buf, 512)
        title = buf.value.strip()
        app = ""
        k.OpenProcess.restype = ctypes.c_void_p
        h = k.OpenProcess(0x1000, False, pid)            # PROCESS_QUERY_LIMITED_INFORMATION
        if h:
            path, size = ctypes.create_unicode_buffer(1024), ctypes.c_ulong(1024)
            if k.QueryFullProcessImageNameW(ctypes.c_void_p(h), 0, path, ctypes.byref(size)):
                app = os.path.splitext(os.path.basename(path.value))[0]
            k.CloseHandle(ctypes.c_void_p(h))
        app = app.lower() or "unknown"
        return (app, title[:120]) if app != "unknown" or title else None
    except Exception:
        return None


class FocusReturn:
    """Remembers the app you were typing in when one of our windows took the keyboard, and gives it back when
    you close that window, so you can carry on typing (the other app keeps its own cursor position).
    Only if the keyboard is still ours at that moment: if you've already clicked into some other app, it stays."""

    def __init__(self):
        self.hwnd = None

    def remember(self, hwnd=None):
        h = hwnd or foreign_foreground()
        if h:
            self.hwnd = h

    def give_back(self):
        h, self.hwnd = self.hwnd, None
        if not (IS_WIN and h):
            return
        try:
            import ctypes
            u = ctypes.windll.user32
            u.GetForegroundWindow.restype = ctypes.c_void_p
            fg, pid = _fg_pid(u, ctypes)
            hw = ctypes.c_void_p(h)
            if pid == os.getpid() and u.IsWindow(hw) and u.IsWindowVisible(hw) and not u.IsIconic(hw):
                u.SetForegroundWindow(hw)
        except Exception as e:
            log_error(f"focus return failed: {e}")


def force_foreground(w):
    """Give keyboard focus to our window even when opened by a gesture/hotkey while another app is active.
    Windows blocks background apps from stealing focus, so try three methods and report success."""
    w.show()
    w.raise_()
    w.activateWindow()
    if not IS_WIN or QGuiApplication.platformName() == "offscreen":  # headless: no real window, no Alt taps
        return True
    try:
        import ctypes
        u, k = ctypes.windll.user32, ctypes.windll.kernel32
        u.GetForegroundWindow.restype = ctypes.c_void_p
        hwnd = ctypes.c_void_p(int(w.winId()))

        def ours():
            return u.GetForegroundWindow() == hwnd.value

        if ours():
            return True
        fg_tid = u.GetWindowThreadProcessId(ctypes.c_void_p(u.GetForegroundWindow()), None)
        me = k.GetCurrentThreadId()
        if fg_tid and fg_tid != me:                      # 1: borrow the active app's input queue
            u.AttachThreadInput(fg_tid, me, True)
            u.BringWindowToTop(hwnd)
            u.SetForegroundWindow(hwnd)
            u.SetFocus(hwnd)
            u.AttachThreadInput(fg_tid, me, False)
        if ours():
            return True
        u.keybd_event(0x12, 0, 0, 0)                     # 2: a synthetic Alt tap lifts the foreground lock
        u.keybd_event(0x12, 0, 0x2, 0)
        u.SetForegroundWindow(hwnd)
        if ours():
            return True
        u.SwitchToThisWindow(hwnd, True)                 # 3: last resort
        return ours()
    except Exception as e:
        log_error(f"focus failed: {e}")
        return False


# ---------------------------------------------------------------- caret for accessibility tools
class CaretSync(QObject):
    """Windows tools like the Text cursor indicator, Magnifier and screen readers follow the system caret.
    This keeps an invisible system caret where the text cursor really is (client-area logical pixels;
    Windows scales it), for every text
    field in the app. Windows only; does nothing elsewhere."""

    def __init__(self, app):
        super().__init__()
        self.ok = False
        self._pending = False
        self._made = None      # (hwnd, height) of the caret we created
        if not IS_WIN:
            return
        try:
            import ctypes
            from ctypes import wintypes
            u = ctypes.windll.user32
            u.CreateCaret.argtypes = [wintypes.HWND, wintypes.HBITMAP, ctypes.c_int, ctypes.c_int]
            u.SetCaretPos.argtypes = [ctypes.c_int, ctypes.c_int]
            self.u, self.wt = u, wintypes
            app.installEventFilter(self)
            app.focusChanged.connect(lambda old, new: self.schedule())
            self.ok = True
        except Exception as e:
            log_error(f"caret sync unavailable: {e}")

    def eventFilter(self, obj, e):
        if e.type() in (QEvent.KeyPress, QEvent.KeyRelease, QEvent.MouseButtonRelease, QEvent.InputMethod,
                        QEvent.Resize, QEvent.Move, QEvent.Show, QEvent.FocusIn):
            self.schedule()
        return False

    def schedule(self):
        if self.ok and not self._pending:
            self._pending = True
            QTimer.singleShot(0, self._sync)   # after Qt has updated its own caret

    def _sync(self):
        self._pending = False
        try:
            w = QApplication.focusWidget()
            if w is None or not w.testAttribute(Qt.WA_InputMethodEnabled):
                return
            rect = w.inputMethodQuery(Qt.ImCursorRectangle)
            if rect is None or not hasattr(rect, "isValid") or not rect.isValid():
                return
            rect = rect.toRect() if hasattr(rect, "toRect") else rect
            top = w.window()
            handle = top.windowHandle()
            if handle is None:
                return
            pt = w.mapTo(top, rect.topLeft())
            # Client-area coordinates in Qt's logical pixels. Windows applies the display scale to the
            # caret itself; multiplying by the scale here made the indicator drift further right as you typed.
            x, y = pt.x(), pt.y()
            h = max(1, rect.height())
            hwnd = self.wt.HWND(int(top.winId()))
            key = (int(top.winId()), h)
            if self._made != key:
                self.u.CreateCaret(hwnd, None, 1, h)  # stays hidden: Qt draws the visible one
                self._made = key
            self.u.SetCaretPos(x, y)
        except Exception as e:
            log_error(f"caret sync failed: {e}")
            self.ok = False


# ---------------------------------------------------------------- stay visible (except full screen)
SHELL_CLASSES = {"Progman", "WorkerW"}                       # the desktop (what "Show desktop" brings forward)
NOT_FULLSCREEN_CLASSES = SHELL_CLASSES | {"Shell_TrayWnd", "Shell_SecondaryTrayWnd", "XamlExplorerHostIslandWindow",
                                          "MultitaskingViewFrame", "ForegroundStaging", "Windows.UI.Core.CoreWindow"}


def notification_state_fullscreen(value):
    """Only exclusive D3D is unambiguous; busy and presentation settings can outlast a full-screen window."""
    return value == 3


def presence_decision(fg_class, fg_rect, fg_monitor_rect, same_monitor, is_ours, exclusive_fullscreen,
                      standard_maximized=False):
    """Pure rule, easy to test. Returns 'hide' (a full-screen app covers the circle's monitor),
    'raise' (the desktop was brought forward: put the circle back on top), or 'show'."""
    if fg_class in SHELL_CLASSES:
        return "raise"
    if is_ours or fg_class in NOT_FULLSCREEN_CLASSES or not same_monitor:
        return "show"
    covers = (fg_rect is not None and fg_monitor_rect is not None and
              fg_rect[0] <= fg_monitor_rect[0] and fg_rect[1] <= fg_monitor_rect[1] and
              fg_rect[2] >= fg_monitor_rect[2] and fg_rect[3] >= fg_monitor_rect[3])
    return "hide" if ((covers and not standard_maximized) or exclusive_fullscreen) else "show"


class PresenceGuard(QObject):
    """Keeps the circle on screen through Show Desktop (Win+D / touchpad swipe), and tucks it away while a
    full-screen app (movie, game, presentation) is in front on the same monitor. Windows only; polls 2x/s."""

    def __init__(self, bubble, own_windows):
        super().__init__()
        self.bubble = bubble
        self.own = own_windows            # callable -> list of our top-level widgets
        self.enabled_fs = True            # hide during full screen (setting)
        self.hidden_for_fs = False
        self.calendar_bar = None
        self.visibility_changed = lambda: None
        self.ok = False
        if not IS_WIN:
            return
        try:
            import ctypes
            from ctypes import wintypes
            self.ct, self.wt = ctypes, wintypes
            u = ctypes.windll.user32
            u.GetForegroundWindow.restype = wintypes.HWND
            u.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
            u.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
            u.MonitorFromWindow.argtypes = [wintypes.HWND, wintypes.DWORD]
            u.MonitorFromWindow.restype = wintypes.HMONITOR
            u.GetMonitorInfoW.argtypes = [wintypes.HMONITOR, ctypes.c_void_p]
            u.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                                       ctypes.c_int, wintypes.UINT]
            u.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
            u.IsWindowVisible.argtypes = [wintypes.HWND]
            u.IsIconic.argtypes = [wintypes.HWND]
            u.IsZoomed.argtypes = [wintypes.HWND]
            u.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
            self.u = u
            self.qt = QTimer(self)
            self.qt.setInterval(500)
            self.qt.timeout.connect(self._check)
            self.qt.start()
            self.ok = True
        except Exception as e:
            log_error(f"presence guard unavailable: {e}")

    def _monitor_rect(self, hwnd):
        ct, wt = self.ct, self.wt

        class MONITORINFO(ct.Structure):
            _fields_ = [("cbSize", wt.DWORD), ("rcMonitor", wt.RECT), ("rcWork", wt.RECT), ("dwFlags", wt.DWORD)]
        hmon = self.u.MonitorFromWindow(hwnd, 2)  # nearest
        mi = MONITORINFO()
        mi.cbSize = ct.sizeof(MONITORINFO)
        if not self.u.GetMonitorInfoW(hmon, ct.byref(mi)):
            return hmon, None
        r = mi.rcMonitor
        return hmon, (r.left, r.top, r.right, r.bottom)

    def _quns_d3d_fullscreen(self):
        try:
            v = self.ct.c_int(0)
            if self.ct.windll.shell32.SHQueryUserNotificationState(self.ct.byref(v)) == 0:
                return notification_state_fullscreen(v.value)
        except Exception:
            pass
        return False

    def _check(self):
        try:
            u, ct, wt = self.u, self.ct, self.wt
            fg = u.GetForegroundWindow()
            if not fg:
                return
            buf = ct.create_unicode_buffer(256)
            u.GetClassNameW(fg, buf, 256)
            rc = wt.RECT()
            fg_rect = (rc.left, rc.top, rc.right, rc.bottom) if u.GetWindowRect(fg, ct.byref(rc)) else None
            me = wt.HWND(int(self.bubble.winId()))
            fg_mon, mon_rect = self._monitor_rect(fg)
            my_mon, _ = self._monitor_rect(me)
            ours = any(w.isVisible() and int(w.winId()) == (fg or 0) for w in self.own())
            ordinary_maximized = bool(u.IsZoomed(fg) and (u.GetWindowLongW(fg, -16) & 0x00C00000))
            exclusive_fullscreen = self._quns_d3d_fullscreen()
            decision = presence_decision(buf.value, fg_rect, mon_rect, fg_mon == my_mon, ours,
                                         exclusive_fullscreen and fg_mon == my_mon, ordinary_maximized)
            if self.calendar_bar is not None:
                bar = self.calendar_bar
                bar.sync_taskbar_position()
                bar_mon, _ = self._monitor_rect(wt.HWND(int(bar.winId())))
                bar_decision = presence_decision(buf.value, fg_rect, mon_rect, fg_mon == bar_mon, ours,
                                                 exclusive_fullscreen and fg_mon == bar_mon, ordinary_maximized)
                bar.set_fullscreen_suppressed(bar_decision == "hide")
                if bar_decision != "hide" and bar.wants_visible():
                    if not bar.isVisible():
                        bar.update_meeting()
                    bh = wt.HWND(int(bar.winId()))
                    dock_refresh = (bar.placement == "taskbar" and bar._dock_signature and
                                    time.monotonic() - bar._last_dock_raise >= 2)
                    if bar_decision == "raise" or not u.IsWindowVisible(bh) or u.IsIconic(bh) or dock_refresh:
                        u.ShowWindow(bh, 4)
                        u.SetWindowPos(bh, wt.HWND(-1), 0, 0, 0, 0, 0x0001 | 0x0002 | 0x0010 | 0x0040)
                        if dock_refresh:
                            bar._last_dock_raise = time.monotonic()
            if decision == "hide" and self.enabled_fs:
                if not self.hidden_for_fs:
                    self.hidden_for_fs = True
                    self.bubble.hide()
                    self.visibility_changed()
                return
            if self.hidden_for_fs:
                self.hidden_for_fs = False
                self.bubble.show()
                self.visibility_changed()
            if decision == "raise" or not u.IsWindowVisible(me) or u.IsIconic(me):
                u.ShowWindow(me, 4)  # SW_SHOWNOACTIVATE
                u.SetWindowPos(me, wt.HWND(-1), 0, 0, 0, 0, 0x0001 | 0x0002 | 0x0010 | 0x0040)
                # HWND_TOPMOST, SWP_NOSIZE | SWP_NOMOVE | SWP_NOACTIVATE | SWP_SHOWWINDOW
        except Exception as e:
            log_error(f"presence check failed: {e}")
            self.qt.setInterval(5000)  # back off instead of spamming the log


_PYNPUT_KEYS = {"space": "<space>", "tab": "<tab>", "home": "<home>", "end": "<end>", "ins": "<insert>",
                "insert": "<insert>", "del": "<delete>", "delete": "<delete>", "pgup": "<page_up>",
                "pgdown": "<page_down>", "up": "<up>", "down": "<down>", "left": "<left>", "right": "<right>"}
_PYNPUT_MODS = {"ctrl": "<ctrl>", "alt": "<alt>", "shift": "<shift>", "meta": "<cmd>"}


def qt_to_pynput(seq):
    """'Ctrl+Alt+P' -> '<ctrl>+<alt>+p'. Returns None if unsupported or no modifier (too easy to hit)."""
    if not seq:
        return None
    parts = [p.strip().lower() for p in seq.split(",")[0].split("+") if p.strip()]
    out, has_mod = [], False
    for k in parts:
        if k in _PYNPUT_MODS:
            out.append(_PYNPUT_MODS[k])
            has_mod = True
        elif len(k) == 1:
            out.append(k)
        elif re.fullmatch(r"f([1-9]|1[0-9]|2[0-4])", k):
            out.append(f"<{k}>")
        elif k in _PYNPUT_KEYS:
            out.append(_PYNPUT_KEYS[k])
        else:
            return None
    if not has_mod or len(out) < 2:
        return None
    return "+".join(out)


class HotkeyManager(QObject):
    quick = Signal()
    panel = Signal()

    def __init__(self):
        super().__init__()
        self.h = None

    def apply(self, quick_seq, panel_seq):
        self.stop()
        mapping = {}
        for seq, sig in ((quick_seq, self.quick), (panel_seq, self.panel)):
            combo = qt_to_pynput(seq)
            if combo and combo not in mapping:
                mapping[combo] = sig.emit
            elif seq:
                log_error(f"hotkey not supported: {seq}")
        if not mapping:
            return
        try:
            from pynput import keyboard
            self.h = keyboard.GlobalHotKeys(mapping)
            self.h.daemon = True
            self.h.start()
        except Exception as e:
            log_error(f"hotkeys unavailable: {e}")

    def stop(self):
        if self.h:
            self.h.stop()
            self.h = None


IMG_EXT = {".png", ".jpg", ".jpeg", ".gif", ".bmp", ".webp"}

C = dict(bg="#1b1c1f", surface="#24262a", surface_hi="#2b2d32", field="#202226", border="#34363c",
         text="#ececec", dim="#a0a2a8", faint="#8a8d94", accent="#a13a47", accent_soft="#3a2226",
         accent_text="#e57a86",   # the accent as text or a thin icon: 4.5:1 or better on every surface
         urge="#6b93f0", urge_bg="#1d2638", done="#202125", card="#24262a",
         dist="#b48cff", dist_bg="#261f38", urgent="#ef5a5f", urgent_bg="#2e2327",
         glimmer="#4cc38a", glimmer_bg="#1b2b23", anti="#e5646e", anti_bg="#2e1f22",
         idea="#e8b64c", idea_bg="#2d2717",
         toast="#33363d", toast_border="#4a4d55", undo="#f3b4bc", cream="#f3e3c3", warn="#f0c16c",
         ok_soft="#80c2a1", timer="#f0d58a", brk="#4fb6a8", brk_bg="#1c3431", disabled="#45474d",
         rem_fg="#ffe0a4", rem_bg="#403627", rem_border="#8d6c3d", rem_hover="#55452e", glow="#262830",
         hint_bg="#2f3238", hint_border="#5a5e67")
DARK = dict(C)
# Light twin of every key. A dark value shared by two keys keeps one light value, and no light value repeats a
# dark one, so a stylesheet built in either theme can be recoloured by swapping hex codes (see apply_theme).
LIGHT = dict(DARK, bg="#f3f4f6", surface="#ffffff", surface_hi="#eaecef", field="#fafbfc", border="#d3d6dc",
             text="#1d1f23", dim="#50545c", faint="#5f636b", accent_soft="#f5e3e6", accent_text="#98303e",
             urge="#3a64c4", urge_bg="#e5ecfa", done="#eceef1", card="#ffffff",
             dist="#7448cc", dist_bg="#eee7fb", urgent="#c9272f", urgent_bg="#fbe6e7",
             glimmer="#177346", glimmer_bg="#e1f3e8", anti="#ad323d", anti_bg="#f8e5e7",
             idea="#8f6208", idea_bg="#faf0d6",
             toast="#fdfdfe", toast_border="#c9ccd3", undo="#8e2c39", cream="#7a4f12", warn="#9a6400",
             ok_soft="#2d8a5c", timer="#8a6a10", brk="#186e63", brk_bg="#dff1ee", disabled="#b9bcc3",
             rem_fg="#7a5410", rem_bg="#fbefd8", rem_border="#d9b77a", rem_hover="#f5e2bd", glow="#fefefe",
             hint_bg="#fcfcfd", hint_border="#b8bcc4")
THEME = {"mode": "system", "hooks": []}    # hooks: things that bake a colour outside a stylesheet re-run on a switch


def theme_dark():
    return QColor(C["bg"]).lightness() < 128


def veil(alpha):
    """The text colour at this alpha: a faint white veil on the dark theme, a faint shade on the light one."""
    c = QColor(C["text"])
    c.setAlpha(alpha)
    return c


def apply_theme(mode=None):
    """Light, dark or follow Windows. Recolours every open window in place: C and the shared stylesheets are
    rebuilt, then each widget's own stylesheet has its old theme's hex codes swapped for the new ones."""
    global STYLE, SETTINGS_STYLE
    if mode:
        THEME["mode"] = mode
    app = QApplication.instance()
    hints = app.styleHints() if app else None
    want = {"dark": Qt.ColorScheme.Dark, "light": Qt.ColorScheme.Light}.get(THEME["mode"], Qt.ColorScheme.Unknown)
    if hints is not None and THEME.get("asked") != want:
        THEME["asked"] = want
        try:
            hints.setColorScheme(want)     # native title bars and dialogs follow; Unknown = follow Windows
        except Exception as e:
            log_error(f"color scheme failed: {e}")
    system = hints.colorScheme() if hints is not None else Qt.ColorScheme.Unknown
    new = LIGHT if (want == Qt.ColorScheme.Light or
                    (want == Qt.ColorScheme.Unknown and system == Qt.ColorScheme.Light)) else DARK
    if C == new:
        return False
    swap = {C[k].lower(): new[k] for k in C if C[k].lower() != new[k].lower()}
    C.update(new)
    STYLE, SETTINGS_STYLE = make_style(), make_settings_style()
    rx = re.compile("|".join(map(re.escape, swap)), re.I)
    for w in (app.allWidgets() if app else []):
        css = w.styleSheet()
        if css:
            fixed = rx.sub(lambda m: swap[m.group(0).lower()], css)
            if fixed != css:
                w.setStyleSheet(fixed)
        w.update()
    for hook in list(THEME["hooks"]):
        try:
            hook()
        except Exception as e:
            log_error(f"theme hook failed: {e}")
    return True


URGENT_ICON = "!"             # really needs doing soon: sits at the top
DIST_ICON = "\u26A1\uFE0E"   # lightning: something hit you from outside
URGE_ICON = "\u2691"          # flag: an "itch", a pull from inside that feels urgent but can wait
# task flags in Tab order: (key, icon, word, tooltip). "urge" keeps its key in data; users see "itch".
GLIMMER_ICON = "+"            # a lift: a small moment of joy, calm or connection (key "glimmer" in the data)
ANTI_ICON = "\u2212"          # a drain: a small cue that put you on edge (key "antiglimmer" in the data)
IDEA_ICON = "\U0001F4A1"      # light bulb: an idea worth keeping (not a to-do)
FLAG_DEFS = [("urgent", URGENT_ICON, "urgent", "Urgent: really needs doing soon. Jumps to the top of the list"),
             ("distraction", DIST_ICON, "distraction", "Distraction: something from outside broke your focus"),
             ("urge", URGE_ICON, "itch", "Itch: feels urgent, but can wait"),
             ("glimmer", GLIMMER_ICON, "lift", "Lift: a small moment of joy, calm or connection. Worth noticing"),
             ("antiglimmer", ANTI_ICON, "drain",
              "Drain: a small moment that put you on edge or wore you down. Worth noticing"),
             ("idea", IDEA_ICON, "idea", "Idea: something worth keeping, not a to-do. Browse them later")]
FLAG_KEYS = [k for k, *_ in FLAG_DEFS]
BUILTIN_FLAG_DEFS = list(FLAG_DEFS)          # FLAG_DEFS / FLAG_KEYS / FLAG_CHIPS are rebuilt in place by configure_flags()
BUILTIN_FLAG_KEYS = set(FLAG_KEYS)
FLAG_COLORS = {}                             # custom flag key -> colour
CUSTOM_FLAG_COLORS = ["#e8b64c", "#4cc38a", "#52b8b6", "#6b93f0", "#b48cff", "#ef5a5f", "#e3905b", "#a0a2a8"]
# chip on a parked card: (text, tooltip, colour key)
FLAG_CHIPS = {
    "urgent": (f"{URGENT_ICON} urgent", "Really needs doing soon, so it sits at the top.", "urgent"),
    "distraction": (f"{DIST_ICON} distraction", "Something from outside broke your focus. Logged for your patterns.", "dist"),
    "urge": (f"{URGE_ICON} itch \u00B7 can wait", "An itch: feels urgent, but it's parked. You won't forget it.", "urge"),
    "glimmer": (f"{GLIMMER_ICON} lift", "A small good moment. Noticing them trains your brain to find more.", "glimmer"),
    "antiglimmer": (f"{ANTI_ICON} drain", "Something that put you on edge or wore you down. Noted, so you can spot the pattern.", "anti"),
    "idea": (f"{IDEA_ICON} idea", "An idea to keep. Search or filter by idea to find them all.", "idea"),
}


def configure_flags(settings):
    """Your flags, in your order: the built-in ones plus any you added (settings["custom_flags"], each
    {key, icon, word, tip, color}), ordered by settings["flag_order"]. Everything that loops over FLAG_DEFS,
    FLAG_KEYS or FLAG_CHIPS (buttons, chips, search, filter, history, the thought log, the AI export) follows."""
    custom = [c for c in settings.get("custom_flags", []) if c.get("key") and c.get("word")]
    defs = {k: (k, icon, word, tip) for k, icon, word, tip in BUILTIN_FLAG_DEFS}
    for c in custom:
        defs[c["key"]] = (c["key"], c.get("icon") or "\u2022", c["word"], c.get("tip") or c["word"])
        FLAG_COLORS[c["key"]] = c.get("color") or CUSTOM_FLAG_COLORS[0]
    order = [k for k in settings.get("flag_order", []) if k in defs]
    order += [k for k in defs if k not in order]
    FLAG_DEFS[:] = [defs[k] for k in order]
    FLAG_KEYS[:] = order
    for c in custom:
        FLAG_CHIPS[c["key"]] = (f"{defs[c['key']][1]} {c['word']}", defs[c["key"]][3], c["key"])


def toggle_numbered_flag(buttons, settings, number):
    """Alt+1..9 follows the visible flag order, including custom flags."""
    visible = numbered_flag_keys(buttons, settings)
    if 1 <= number <= len(visible):
        b = buttons[visible[number - 1]]
        b.setChecked(not b.isChecked())
        return True
    return False


def numbered_flag_keys(buttons, settings):
    """The same mapping drives the shortcut and its on-screen Alt guide."""
    return [k for k in FLAG_KEYS if flag_on(settings, k) and k in buttons][:9]


def custom_flag_css():
    """Colours for your own flags (the built-in ones are in STYLE)."""
    out = []
    for k, col in FLAG_COLORS.items():
        q = QColor(col)
        base = QColor(C["surface"])
        bg = QColor(*(int(a * 0.18 + b * 0.82) for a, b in ((q.red(), base.red()), (q.green(), base.green()),
                                                            (q.blue(), base.blue())))).name()
        out.append(f'QLabel#chip[kind="{k}"] {{ color: {col}; background: {bg}; border: 1px solid {col}; }}'
                   f'QToolButton#flag[kind="{k}"]:checked {{ color: {col}; background: {bg}; border-color: {col}; }}'
                   f'QFrame#card[stripe="{k}"] {{ border-left: 3px solid {col}; }}')
    return "\n".join(out)


def full_style():
    return STYLE + custom_flag_css()


INBOX_SOURCES = {"private_note", "private_note_paste", "private_note_drop", "circle_drop"}  # land in the first tab
FLAG_HINT_DELAY_MS = 350   # quick enough to feel instant when you want it, slow enough not to flicker past


class HintBubble(QWidget):
    """The flag hint: a small window that paints its own filled, rounded background, so it's always readable
    (a translucent QLabel's stylesheet background isn't painted on every Windows setup)."""
    PAD_X, PAD_Y = 8, 4

    def __init__(self):
        super().__init__(None, Qt.ToolTip | Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self._text = ""
        self.f = QFont()
        self.f.setPixelSize(12)

    def setText(self, text):
        self._text = text or ""
        fm = QFontMetrics(self.f)
        self.setFixedSize(fm.horizontalAdvance(self._text) + 2 * self.PAD_X + 2, fm.height() + 2 * self.PAD_Y + 2)
        self.update()

    def text(self):
        return self._text

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        p.setPen(QPen(QColor(C["hint_border"]), 1))
        p.setBrush(QColor(C["hint_bg"]))
        p.drawRoundedRect(r, 6, 6)
        p.setFont(self.f)
        p.setPen(QColor(C["text"]))
        p.drawText(r, Qt.AlignCenter, self._text)


class _AltFlagGuideHub(QObject):
    """One app-wide key watcher shared by both capture windows."""

    def __init__(self, app):
        super().__init__(app)
        self.guides = weakref.WeakKeyDictionary()
        app.installEventFilter(self)

    def register(self, guide):
        self.guides[guide.owner] = weakref.ref(guide)

    def eventFilter(self, obj, event):
        kind = event.type()
        if kind not in (QEvent.KeyPress, QEvent.KeyRelease, QEvent.Hide, QEvent.WindowDeactivate):
            return False
        owner = obj.window() if kind in (QEvent.KeyPress, QEvent.KeyRelease) and isinstance(obj, QWidget) else obj
        guide_ref = self.guides.get(owner) if isinstance(owner, QWidget) else None
        guide = guide_ref() if guide_ref else None
        if guide is None:
            return False
        if kind in (QEvent.Hide, QEvent.WindowDeactivate) and obj is owner:
            guide.hide()
        elif kind == QEvent.KeyPress and event.key() == Qt.Key_Alt and not event.isAutoRepeat():
            guide.show()
        elif kind == QEvent.KeyRelease and event.key() == Qt.Key_Alt:
            guide.hide()
        return False


class AltFlagNumber(QWidget):
    """A bright numeral with a fine dark edge, without a badge background."""

    def __init__(self, parent):
        super().__init__(parent)
        self._text = ""
        self.setFixedSize(17, 18)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)

    def setText(self, value):
        self._text = value
        self.update()

    def text(self):
        return self._text

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        font = QFont()
        font.setPixelSize(14)
        font.setBold(True)
        fm = QFontMetrics(font)
        glyph = QPainterPath()
        glyph.addText(QPointF((self.width() - fm.horizontalAdvance(self._text)) / 2,
                              (self.height() - fm.height()) / 2 + fm.ascent()), font, self._text)
        p.setPen(QPen(QColor("#111318"), 1.0, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        p.setBrush(QColor("#ffffff"))
        p.drawPath(glyph)


class AltFlagGuide(QObject):
    """Plain numbers inside flag buttons while Alt is held in a capture window."""

    def __init__(self, owner, buttons, settings):
        super().__init__(owner)
        self.owner, self.buttons, self.settings = owner, buttons, settings
        self.badges = []
        app = QApplication.instance()
        hub = getattr(app, "_ptt_alt_flag_guide_hub", None)
        if hub is None:
            hub = _AltFlagGuideHub(app)
            app._ptt_alt_flag_guide_hub = hub
        hub.register(self)

    def show(self):
        if not self.owner.isVisible():
            return
        if FLAG_HINT is not None:
            FLAG_HINT.timer.stop()
            FLAG_HINT.hide_label()
        buttons = self.buttons()
        keys = numbered_flag_keys(buttons, self.settings())
        for i, key in enumerate(keys):
            button = buttons[key]
            if not button.isVisible():
                continue
            if i >= len(self.badges):
                badge = AltFlagNumber(button)
                self.badges.append(badge)
            badge = self.badges[i]
            if badge.parentWidget() is not button:
                badge.setParent(button)
            badge.setText(str(i + 1))
            badge.setAccessibleName(f"Alt plus {i + 1} for {button.property('flagword')}")
            badge.move(button.width() - badge.width() - 1, 1)
            badge.show()
            badge.raise_()
        for badge in self.badges[len(keys):]:
            badge.hide()

    def hide(self):
        for badge in self.badges:
            badge.hide()

    def clear(self):
        """Discard child numbers before flag buttons are rebuilt."""
        for badge in self.badges:
            badge.hide()
            badge.deleteLater()
        self.badges.clear()


class _FlagHint(QObject):
    """One shared timer: hovering or Tabbing onto a flag shows what it is after a short pause."""

    def __init__(self):
        super().__init__()
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.setInterval(FLAG_HINT_DELAY_MS)
        self.timer.timeout.connect(self._show)
        self.target = None

    def arm(self, w):
        self.target = w
        self.timer.start()

    def disarm(self, w):
        if self.target is w:
            self.timer.stop()
            self.target = None
            self.hide_label()

    def _label(self):
        if getattr(self, "lbl", None) is None:
            self.lbl = HintBubble()
        return self.lbl

    def _show(self):
        w = self.target
        if w is None or not w.isVisible() or not (w.underMouse() or w.hasFocus()):
            return
        lbl = self._label()
        lbl.setText(w.property("flaghint"))
        # centred just under the flag, kept on screen
        g = w.mapToGlobal(QPoint(w.width() // 2, w.height()))
        area = (QGuiApplication.screenAt(g) or QGuiApplication.primaryScreen()).availableGeometry()
        x = max(area.left() + 2, min(g.x() - lbl.width() // 2, area.right() - lbl.width() - 2))
        y = g.y() + 5
        if y + lbl.height() > area.bottom():
            y = w.mapToGlobal(QPoint(0, 0)).y() - lbl.height() - 5    # no room below: show above
        lbl.move(x, y)
        lbl.show()
        lbl.raise_()
        apply_share_privacy(lbl)

    def hide_label(self):
        if getattr(self, "lbl", None) is not None:
            self.lbl.hide()


FLAG_HINT = None


TIPS = {"mode": "auto", "first_seen": 0.0}      # hover tips: "auto" (first week), "on", "off"
TIPS_DAYS = 7


def tips_on():
    if TIPS["mode"] == "on":
        return True
    if TIPS["mode"] == "off":
        return False
    return time.time() - TIPS["first_seen"] < TIPS_DAYS * 86400


class TipGate(QObject):
    """App-wide: swallows hover tooltips once you know your way around (after the first week, by default)."""

    def eventFilter(self, obj, e):
        if e.type() == QEvent.ToolTip and not tips_on():
            return True
        return False


def flag_focus_hint(obj, e):
    """Hover or Tab onto a flag: its name and meaning appear after FLAG_HINT_DELAY_MS (same for both)."""
    global FLAG_HINT
    if not (hasattr(obj, "property") and obj.property("flaghint")) or not tips_on():
        return
    if FLAG_HINT is None:
        FLAG_HINT = _FlagHint()
    t = e.type()
    if t == QEvent.Enter or (t == QEvent.FocusIn and e.reason() in (Qt.TabFocusReason, Qt.BacktabFocusReason)):
        FLAG_HINT.arm(obj)
    elif t in (QEvent.Leave, QEvent.FocusOut, QEvent.Hide, QEvent.MouseButtonPress):
        FLAG_HINT.disarm(obj)
    elif t == QEvent.ToolTip:
        return True    # our own hint replaces Qt's slower tooltip


def flag_enter_toggles(obj, e):
    """In the full list: Enter toggles a focused flag, Space does nothing. True if the event was handled."""
    if e.type() in (QEvent.KeyPress, QEvent.KeyRelease) and e.key() == Qt.Key_Space:
        return True                    # swallow both, so Qt's own Space-to-click never fires
    if e.type() == QEvent.KeyPress and e.key() in (Qt.Key_Return, Qt.Key_Enter):
        obj.toggle()
        return True
    return False


def flag_on(settings, key):
    """Each flag can be switched off in Settings > Flags (hidden everywhere; stored data is kept)."""
    return bool(settings.get("flags_on", {}).get(key, True))

def make_style():
    return f"""
QWidget#panel {{ background: {C['bg']}; color: {C['text']}; }}
QLabel#appTitle {{ color: {C['text']}; font-size: 15px; font-weight: 700; padding-left: 2px; }}
QLabel#appSub {{ color: {C['faint']}; font-size: 11px; padding-left: 2px; }}
QWidget#roundwin {{ background: transparent; color: {C['text']}; }}
QWidget#list, QWidget#listwrap {{ background: transparent; }}
QScrollArea {{ border: none; background: transparent; }}
QScrollBar:vertical {{ background: transparent; width: 8px; margin: 2px; }}
QScrollBar::handle:vertical {{ background: {C['border']}; border-radius: 3px; min-height: 30px; }}
QScrollBar::handle:vertical:hover {{ background: {C['faint']}; }}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical, QScrollBar::add-page:vertical,
QScrollBar::sub-page:vertical {{ height: 0; background: none; }}
QLabel {{ color: {C['text']}; background: transparent; }}
QLabel#hint {{ color: {C['faint']}; font-size: 11px; }}
QLabel#attachHint {{ color: {C['faint']}; font-size: 11px; padding-left: 2px; }}
QLabel#emptyTitle {{ color: {C['text']}; font-size: 15px; font-weight: 600; }}
QLabel#emptyText {{ color: {C['dim']}; font-size: 12px; }}
QLabel#chip {{ border-radius: 4px; padding: 0px 6px; font-size: 10px; font-weight: 600; }}
QLabel#chip[kind="urgent"] {{ color: {C['urgent']}; background: {C['urgent_bg']}; border: 1px solid {C['urgent']}; font-weight: 700; }}
QLabel#chip[kind="dist"] {{ color: {C['dist']}; background: {C['dist_bg']}; border: 1px solid {C['dist']}; }}
QLabel#chip[kind="urge"] {{ color: {C['urge']}; background: {C['urge_bg']}; border: 1px solid {C['urge']}; }}
QLabel#chip[kind="glimmer"] {{ color: {C['glimmer']}; background: {C['glimmer_bg']}; border: 1px solid {C['glimmer']}; }}
QLabel#chip[kind="anti"] {{ color: {C['anti']}; background: {C['anti_bg']}; border: 1px solid {C['anti']}; }}
QLabel#chip[kind="idea"] {{ color: {C['idea']}; background: {C['idea_bg']}; border: 1px solid {C['idea']}; }}
QToolButton#flag[kind="idea"]:checked {{ color: {C['idea']}; background: {C['idea_bg']}; border-color: {C['idea']}; }}
QFrame#card[stripe="idea"] {{ border-left: 3px solid {C['idea']}; }}
QToolButton#flag[kind="glimmer"] {{ color: {C['glimmer']}; font-weight: 700; }}
QToolButton#flag[kind="antiglimmer"] {{ color: {C['anti']}; font-weight: 700; }}
QToolButton#flag[kind="glimmer"]:checked {{ color: {C['glimmer']}; background: {C['glimmer_bg']}; border-color: {C['glimmer']}; font-weight: 700; }}
QToolButton#flag[kind="antiglimmer"]:checked {{ color: {C['anti']}; background: {C['anti_bg']}; border-color: {C['anti']}; font-weight: 700; }}
QFrame#card[stripe="glimmer"] {{ border-left: 3px solid {C['glimmer']}; }}
QFrame#card[stripe="anti"] {{ border-left: 3px solid {C['anti']}; }}
QFrame#card[tint="glimmer"] {{ background: {C['glimmer_bg']}; }}
QLabel#chipDist {{ color: {C['dist']}; background: {C['dist_bg']}; border: 1px solid {C['dist']};
    border-radius: 4px; padding: 0px 6px; font-size: 10px; font-weight: 600; }}
QToolButton#flag {{ color: {C['dim']}; border: 1px solid {C['border']}; border-radius: 10px; padding: 2px 9px;
    font-size: 11px; }}
QToolButton#flag:focus {{ border: 1px solid {C['text']}; }}
QToolButton#remChip {{ color: {C['dim']}; border: 1px solid {C['border']}; border-radius: 10px; padding: 2px 9px;
    font-size: 11px; }}
QToolButton#remChip:hover, QToolButton#remChip:focus {{ border-color: {C['text']}; }}
QToolButton#remChip[set="true"] {{ color: {C['accent_text']}; background: {C['accent_soft']}; border-color: {C['accent']};
    font-weight: 700; }}
QToolButton#flag[kind="distraction"]:checked {{ color: {C['dist']}; background: {C['dist_bg']}; border-color: {C['dist']}; }}
QToolButton#flag[kind="urgent"]:checked {{ color: {C['urgent']}; background: {C['urgent_bg']}; border-color: {C['urgent']}; font-weight: 700; }}
QToolButton#flag[kind="urge"]:checked {{ color: {C['urge']}; background: {C['urge_bg']}; border-color: {C['urge']}; }}
QToolButton#dist:checked {{ color: {C['dist']}; }}
QLabel#chipUrgent {{ color: {C['urgent']}; background: {C['urgent_bg']}; border: 1px solid {C['urgent']};
    border-radius: 4px; padding: 0px 6px; font-size: 10px; font-weight: 700; }}
QToolButton#act {{ color: {C['dim']}; font-size: 11px; padding: 2px 7px; border: 1px solid {C['border']};
    border-radius: 8px; background: {C['surface']}; }}
QToolButton#act:hover {{ color: {C['text']}; background: {C['surface_hi']}; border: 1px solid {C['faint']}; }}
QToolButton#act[good="true"] {{ color: {C['glimmer']}; }}
QToolButton#act[good="true"]:hover {{ border: 1px solid {C['glimmer']}; background: {C['glimmer_bg']}; }}
QToolButton#act[danger="true"] {{ color: {C['faint']}; }}
QToolButton#act[danger="true"]:hover {{ color: {C['anti']}; border: 1px solid {C['anti']}; background: {C['anti_bg']}; }}
QToolButton#act:focus {{ color: {C['text']}; background: {C['accent']}; border: 1px solid {C['accent']}; }}
QToolButton#morePill {{ background: {C['surface_hi']}; color: {C['dim']}; border: 1px solid {C['border']};
    border-radius: 10px; padding: 2px 10px; font-size: 11px; }}
QToolButton#morePill:hover {{ color: {C['text']}; border: 1px solid {C['faint']}; background: {C['surface']}; }}
QFrame#toast {{ background: {C['toast']}; border: 1px solid {C['toast_border']}; border-radius: 15px; }}
QLabel#toastText {{ color: {C['text']}; font-size: 12px; background: transparent; }}
QToolButton#toastUndo {{ color: {C['undo']}; font-size: 12px; font-weight: 700; padding: 2px 10px; border-radius: 10px;
    border: 1px solid transparent; background: transparent; }}
QToolButton#toastUndo:hover {{ background: {C['accent_soft']}; border: 1px solid {C['accent']}; color: white; }}
QFrame#sections {{ border-top: 1px solid {C['border']}; }}
QFrame#workShelf {{ background: {C['surface']}; border: 1px solid {C['border']}; border-radius: 9px; }}
QToolButton#workToggle {{ color: {C['text']}; font-size: 12px; font-weight: 700; text-align: left;
    padding: 4px 2px; }}
QToolButton#workToggle:hover {{ background: transparent; color: {C['cream']}; }}
QToolButton#workAdd {{ color: {C['text']}; background: {C['surface_hi']}; font-size: 18px; font-weight: 600;
    min-width: 24px; max-width: 24px; min-height: 24px; max-height: 24px; }}
QLabel#workNext {{ color: {C['warn']}; font-size: 11px; }}
QFrame#workRow {{ background: {C['surface_hi']}; border-radius: 6px; }}
QLabel#workTitle {{ color: {C['text']}; font-size: 12px; font-weight: 600; }}
QLabel#workWhen, QLabel#workGap, QLabel#workEmpty {{ color: {C['dim']}; font-size: 11px; }}
QLabel#workGap {{ padding-left: 31px; }}
QLabel#workEmpty {{ padding: 7px 4px; }}
QToolButton#workDone {{ color: {C['ok_soft']}; font-size: 19px; min-width: 22px; }}
QToolButton#workEdit, QToolButton#workFinished {{ color: {C['dim']}; font-size: 11px; }}
QToolButton#workFinished {{ text-align: left; }}
QLabel#chipUrge {{ color: {C['urge']}; background: {C['urge_bg']}; border: 1px solid {C['urge']};
    border-radius: 4px; padding: 0px 6px; font-size: 10px; font-weight: 600; }}
QLabel#dropHint {{ color: {C['cream']}; background: {C['accent_soft']}; border: 1px dashed {C['accent']};
    border-radius: 6px; padding: 6px; font-size: 12px; }}
QLabel#timerChip {{ color: {C['timer']}; font-size: 12px; }}
QFrame#timerBar {{ background: {C['surface']}; border-radius: 8px; }}
QToolButton#timerBtn {{ color: {C['text']}; font-size: 12px; padding: 3px 8px; }}
QToolButton#startFocus {{ color: white; background: {C['accent']}; border: none; border-radius: 10px;
    padding: 4px 11px 4px 8px; font-size: 12px; font-weight: 600; }}
QToolButton#startFocus:hover {{ background: #b8465a; }}
QToolButton#startBreak {{ color: {C['brk']}; background: transparent; border: 1px solid {C['brk']}; border-radius: 10px;
    padding: 3px 11px 3px 8px; font-size: 12px; font-weight: 600; }}
QToolButton#startBreak:hover {{ background: {C['brk_bg']}; }}
QToolButton#timerBtn:hover {{ background: {C['border']}; }}
QDoubleSpinBox#minSpin {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
    border-radius: 6px; padding: 4px 4px; font-size: 13px; min-width: 40px; max-width: 48px;
    selection-background-color: {C['accent']}; }}
QDoubleSpinBox#minSpin:hover {{ border: 1px solid {C['faint']}; }}
QDoubleSpinBox#minSpin:focus {{ border: 1px solid {C['accent']}; }}
QLabel#unit {{ color: {C['dim']}; font-size: 12px; }}
QLabel#ok {{ color: {C['glimmer']}; font-size: 12px; }}
QLabel#bad {{ color: {C['idea']}; font-size: 12px; }}
QSpinBox, QComboBox {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
    border-radius: 7px; padding: 3px 6px; min-height: 18px; selection-background-color: {C['accent']}; }}
QSpinBox:hover, QComboBox:hover {{ border-color: {C['faint']}; }}
QSpinBox:focus, QComboBox:focus {{ border-color: {C['accent_text']}; }}
QSpinBox::up-button, QSpinBox::down-button {{ width: 0; border: none; }}
QComboBox::drop-down {{ border: none; width: 16px; }}
QComboBox QAbstractItemView {{ background: {C['surface_hi']}; color: {C['text']}; border: 1px solid {C['border']};
    selection-background-color: {C['accent']}; outline: none; }}
QLineEdit, QPlainTextEdit {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
    border-radius: 8px; padding: 5px; selection-background-color: {C['accent']}; }}
QLineEdit:focus {{ border: 1px solid {C['accent']}; }}
QLineEdit#quick {{ padding: 9px 10px; font-size: 13px; }}
QPlainTextEdit#quick {{ padding: 5px 6px; font-size: 13px; }}
QPlainTextEdit#quick:focus {{ border: 1px solid {C['accent']}; }}
QPlainTextEdit#qdetails {{ font-size: 12px; padding: 2px 6px; }}
QPlainTextEdit#qdetails:focus {{ border: 1px solid {C['accent']}; }}
QTextEdit {{ background: transparent; color: {C['text']}; border: none; selection-background-color: {C['accent']}; }}
QTextEdit#title {{ font-size: 13px; font-weight: 600; }}
QTextEdit#details {{ background: transparent; border: none; font-size: 12px; color: {C['dim']}; }}
QTextEdit#details:focus {{ background: {C['field']}; border-radius: 5px; color: {C['text']}; }}
QFrame#card {{ background: {C['surface']}; border: 1px solid transparent; border-radius: 10px; }}
QFrame#card[tint="urge"] {{ background: {C['urge_bg']}; }}
QFrame#card[tint="urgent"] {{ background: {C['urgent_bg']}; }}
QFrame#card[stripe="urge"] {{ border-left: 3px solid {C['urge']}; }}
QFrame#card[stripe="dist"] {{ border-left: 3px solid {C['dist']}; }}
QFrame#card[stripe="urgent"] {{ border-left: 3px solid {C['urgent']}; }}
QFrame#card[done="true"] {{ background: {C['done']}; }}
QFrame#card[drag="true"] {{ border: 1px dashed {C['accent']}; }}
QFrame#actions {{ background: {C['bg']}; border: 1px solid {C['border']}; border-radius: 11px; }}
QToolButton {{ background: transparent; color: {C['dim']}; border: none; padding: 3px 6px; border-radius: 5px; }}
QToolButton:hover {{ color: {C['text']}; background: {C['border']}; }}
QToolButton:disabled {{ color: {C['disabled']}; }}
QToolButton#urge:checked {{ color: {C['urge']}; }}
QToolButton#copy {{ background: {C['accent']}; color: white; font-weight: bold; }}
QToolButton#section {{ color: {C['dim']}; font-size: 12px; font-weight: 600; padding: 4px 2px; }}
QToolButton#link {{ color: {C['faint']}; font-size: 11px; }}
QToolButton#link:hover {{ color: {C['text']}; background: transparent; }}
QToolButton#help, QToolButton#addTab {{ font-size: 16px; color: {C['dim']}; border-radius: 6px; }}
QToolButton#help:hover, QToolButton#addTab:hover {{ color: {C['text']}; background: {C['surface_hi']}; }}
QToolButton#send {{ color: white; background: {C['accent']}; border: none; border-radius: 11px; padding: 3px 12px;
    font-size: 12px; font-weight: 600; }}
QToolButton#send:hover {{ background: #b8465a; }}
QToolButton#send:disabled {{ color: {C['faint']}; background: {C['surface_hi']}; }}
QToolButton#filterChip {{ color: {C['text']}; background: {C['accent_soft']}; border: 1px solid {C['accent']};
    border-radius: 9px; padding: 1px 8px; font-size: 11px; }}
QToolButton#filterChip:hover {{ background: {C['accent']}; }}
QFrame#tile {{ background: {C['field']}; border: 1px solid {C['border']}; border-radius: 6px; }}
QPushButton {{ background: {C['surface']}; color: {C['text']}; border: 1px solid {C['border']};
    border-radius: 6px; padding: 4px 10px; }}
QPushButton:hover {{ background: {C['surface_hi']}; }}
QCheckBox {{ color: {C['text']}; }}
QTabBar::tab {{ background: transparent; color: {C['dim']}; padding: 6px 10px; border: none;
    border-bottom: 2px solid transparent; max-width: 150px; }}
QTabBar::tab:selected {{ color: {C['text']}; border-bottom: 2px solid {C['accent']}; }}
QTabBar::tab:hover {{ color: {C['text']}; }}
QLabel#tabCount {{ background: {C['surface_hi']}; color: {C['dim']}; border: 1px solid {C['border']};
    border-radius: 8px; font-size: 10px; font-weight: 600; padding: 0px 5px; min-width: 6px; max-height: 15px; }}
QFrame#helpPop {{ background: {C['surface_hi']}; border: 1px solid {C['border']}; border-radius: 10px; }}
QMenu {{ background: {C['surface_hi']}; color: {C['text']}; border: 1px solid {C['border']}; padding: 4px; }}
QMenu::item {{ padding: 5px 18px; border-radius: 4px; }}
QMenu::item:selected {{ background: {C['accent']}; }}
QMenu::item:disabled {{ color: {C['faint']}; }}
QMenu::separator {{ height: 1px; background: {C['border']}; margin: 4px 6px; }}
"""


STYLE = make_style()


# ---------------------------------------------------------------- storage
class Store:
    def __init__(self):
        for d in (DATA_DIR, ATT_DIR, TRASH_DIR, BACKUP_DIR):
            d.mkdir(parents=True, exist_ok=True)
        for stale in DATA_DIR.glob("tasks.*.tmp"):
            try:
                stale.unlink()
            except Exception:
                pass
        self.data = self._load_newest()
        self.data.setdefault("settings", {})
        if not isinstance(self.data.get("important_work"), list):
            self.data["important_work"] = []
        self._migrate()
        configure_flags(self.data["settings"])
        self.context_fn = lambda: {"in_focus": False}   # replaced by main() with the focus timer's state
        self._backfill_log()
        self._dirty = False
        self._fails = 0
        self.on_status = lambda ok: None
        self._save_thread = None
        self._save_result = None
        self._timer = QTimer()
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._begin_save)
        self._save_poll = QTimer()
        self._save_poll.setInterval(100)
        self._save_poll.timeout.connect(self._finish_async_save)
        self.save()  # re-sync tasks.json if we loaded from rescue/backup

    def _load_newest(self):
        """Read tasks.json, the rescue copy and the latest backup; keep the newest valid one."""
        candidates = [DB_FILE, RESCUE_FILE] + sorted(BACKUP_DIR.glob("tasks-*.json"))[-1:]
        best = None
        for p in candidates:
            if not p.exists():
                continue
            for attempt in range(5):  # OneDrive may briefly lock the file
                try:
                    d = json.loads(p.read_text(encoding="utf-8"))
                    if isinstance(d, dict) and (isinstance(d.get("lists"), list) or isinstance(d.get("tasks"), list)):
                        if best is None or d.get("saved_at", 0) > best.get("saved_at", 0):
                            best = d
                    break
                except PermissionError:
                    time.sleep(0.2)
                except Exception as e:
                    log_error(f"could not read {p}: {e}")
                    try:
                        shutil.copy2(p, TRASH_DIR / f"broken-{int(time.time())}-{p.name}")
                    except Exception:
                        pass
                    break
        return best or {"lists": [], "settings": {}}

    def _migrate(self):
        """Old single-list files become an 'Inbox' tab."""
        d = self.data
        if "lists" not in d:
            d["lists"] = [{"id": "inbox", "name": "Inbox", "tasks": d.get("tasks", [])}]
        d.pop("tasks", None)
        if not d["lists"]:
            d["lists"].append({"id": "inbox", "name": "Inbox", "tasks": []})
        if self.settings.get("current") not in [l["id"] for l in d["lists"]]:
            self.settings["current"] = d["lists"][0]["id"]
        # Existing installations have already learned the app; only brand-new data gets the intro pool.
        self.settings.setdefault("checkin_count", len(FIRST_CHECKINS) if d.get("saved_at") else 0)

    # ---- lists (tabs)
    @property
    def lists(self):
        return self.data["lists"]

    def current(self):
        return next(l for l in self.lists if l["id"] == self.settings["current"])

    def inbox(self):
        """The first tab. Quick notes and drops on the circle always land here; drag a tab first to change it."""
        return self.lists[0]

    def discard_new(self, t):
        """Take back a task that was never confirmed (e.g. its attachment failed). Not logged, never saved."""
        l = self.list_of(t)
        if t in l["tasks"]:
            l["tasks"].remove(t)

    def move_to_list(self, t, target):
        """Move a note to another tab (to the top, like a new note). Returns what undo_move_to_list() needs."""
        src = self.list_of(t)
        if src is target:
            return None
        i = next(k for k, x in enumerate(src["tasks"]) if x is t)
        src["tasks"].pop(i)
        target["tasks"].insert(0, t)
        self.log_event("moved_list", t, **{"from": src["name"]})
        self.save()
        return src, i

    def undo_move_to_list(self, t, token):
        src, i = token
        now = self.list_of(t)
        now["tasks"][:] = [x for x in now["tasks"] if x is not t]
        src["tasks"].insert(min(i, len(src["tasks"])), t)
        self.log_event("moved_list", t, undo=True, **{"from": now["name"]})
        self.save()

    def set_current(self, list_id):
        self.settings["current"] = list_id
        self.save()

    def add_list(self, name):
        l = {"id": uuid.uuid4().hex[:8], "name": name, "tasks": []}
        self.lists.append(l)
        self.set_current(l["id"])
        return l

    def rename_list(self, l, name):
        l["name"] = name
        self.save()

    def delete_list(self, l):
        """Tasks go to trash/cleared_tasks.jsonl, attachments to trash. Last list can't be deleted."""
        if len(self.lists) <= 1:
            return False
        prev = self.settings["current"]
        self.settings["current"] = l["id"]
        for t in l["tasks"]:
            if not t["done"]:
                self.log_event("abandoned", t, note="list deleted while open")
            t["done"] = True
        self.clear_done(reason="list_deleted")
        self.lists.remove(l)
        self.settings["current"] = prev if prev != l["id"] else self.lists[0]["id"]
        self.save()
        return True

    def open_count(self):
        """What the circle shows: open thoughts still in play (Later ones are tucked away)."""
        return sum(1 for l in self.lists for t in l["tasks"] if not t["done"] and not t.get("later"))

    @property
    def tasks(self):
        return self.current()["tasks"]

    @property
    def settings(self):
        return self.data["settings"]

    @property
    def important_work(self):
        return self.data["important_work"]

    def add_important_work(self, title, due):
        item = {"id": uuid.uuid4().hex[:12], "title": title.strip(), "due": due.isoformat(timespec="minutes"),
                "created_at": datetime.now().isoformat(timespec="seconds"), "done_at": None}
        self.important_work.append(item)
        self.save()
        return item

    def edit_important_work(self, item, title, due):
        item["title"], item["due"] = title.strip(), due.isoformat(timespec="minutes")
        self.save()

    def set_important_done(self, item, done):
        item["done_at"] = datetime.now().isoformat(timespec="seconds") if done else None
        self.save()

    def save(self):
        self._dirty = True
        self._timer.start(400)

    def _write_snapshot(self, text):
        try:
            self._write_atomic(DB_FILE, text)
        except Exception as e:
            log_error(f"save failed: {e}")
            try:
                RESCUE_DIR.mkdir(parents=True, exist_ok=True)
                self._write_atomic(RESCUE_FILE, text)
            except Exception as e2:
                log_error(f"rescue save failed too: {e2}")
            return False
        self._daily_backup(text)
        return True

    def _begin_save(self):
        if self._save_thread is not None:
            if self._save_thread.is_alive():
                return                 # the completion poll will send any newer edits next
            self._finish_async_save()
        if not self._dirty:
            return
        self.data["saved_at"] = time.time()
        text = json.dumps(self.data, indent=2, ensure_ascii=False)
        self._dirty = False             # edits after this snapshot mark it dirty again
        self._save_result = None
        def write():
            self._save_result = self._write_snapshot(text)
        self._save_thread = threading.Thread(target=write, daemon=True)
        self._save_thread.start()
        self._save_poll.start()

    def _finish_async_save(self):
        if self._save_thread is None or self._save_thread.is_alive():
            return
        self._save_poll.stop()
        result = self._save_result
        self._save_thread = None
        self._save_result = None
        self._finish_save_result(result)

    def _finish_save_result(self, ok):
        if not ok:
            self._fails += 1
            self._dirty = True
            self._timer.start(min(2000 * self._fails, 30000))
            self.on_status(False)
            return False
        if self._fails:
            log_error("save recovered")
        self._fails = 0
        self.on_status(True)
        if self._dirty:
            self._timer.start(400)
        return True

    def _write_atomic(self, path, text):
        tmp = path.with_name(f"{path.stem}.{os.getpid()}.tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        for attempt in range(6):  # 0.1+0.2+...+0.6 s total max
            try:
                os.replace(tmp, path)
                return
            except PermissionError:
                time.sleep(0.1 * (attempt + 1))
        raise PermissionError(f"{path.name} stayed locked")

    def save_now(self):
        """Never loses data: retries, falls back to a rescue copy outside OneDrive, keeps retrying."""
        self._timer.stop()
        if self._save_thread is not None:
            self._save_thread.join()
            self._finish_async_save()
        if not self._dirty:
            return True
        self.data["saved_at"] = time.time()
        text = json.dumps(self.data, indent=2, ensure_ascii=False)
        ok = self._write_snapshot(text)
        self._dirty = not ok
        return self._finish_save_result(ok)

    def _daily_backup(self, text):
        try:
            today = BACKUP_DIR / f"tasks-{datetime.now():%Y%m%d}.json"
            today.write_text(text, encoding="utf-8")
            for old in sorted(BACKUP_DIR.glob("tasks-*.json"))[:-BACKUP_KEEP_DAYS]:
                old.unlink()
        except Exception as e:
            log_error(f"backup failed: {e}")

    def flush_on_quit(self):
        for _ in range(10):
            if self.save_now():
                return
            time.sleep(0.5)

    def new_task(self, title="", source="list", log=True):
        """source: how it came in (list, private_note, *_paste, *_drop). log=False when the caller
        still has to confirm the task (e.g. an attachment), then it calls log_captured().
        Captures from outside the list (quick note, circle drop) go to the inbox (first tab);
        notes typed or dropped into the list go to the tab you're looking at."""
        try:
            ctx = self.context_fn()
        except Exception:
            ctx = {"in_focus": False}
        t = {"id": uuid.uuid4().hex[:10], "title": title, "desc": "", "urge": False, "done": False,
             "created": datetime.now().isoformat(timespec="seconds"), "attachments": [],
             "source": source, "focus": ctx}
        (self.inbox() if source in INBOX_SOURCES else self.current())["tasks"].insert(0, t)
        self.save()
        if log:
            self.log_captured(t)
        return t

    def all_tasks(self):
        return (t for group in self.lists for t in group["tasks"])

    # ---- thought log (for finding patterns later)
    def list_of(self, t):
        return next((l for l in self.lists if t in l["tasks"]), self.current())

    def log_event(self, event, t, ts=None, **extra):
        row = {"ts": ts or datetime.now().isoformat(timespec="seconds"), "event": event, "id": t["id"],
               "title": t["title"], "list": self.list_of(t)["name"]}
        row.update(extra)
        line = json.dumps(row, ensure_ascii=False) + "\n"
        for target in (THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl"):
            for attempt in range(4):
                try:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with open(target, "a", encoding="utf-8") as f:
                        f.write(line)
                    return
                except Exception as e:
                    log_error(f"thought log write failed ({target}): {e}")
                    time.sleep(0.15)

    def log_captured(self, t):
        extra = {}
        media = media_now() if self.settings.get("music_log", False) else None
        if media is not None:
            extra["music"] = media           # {playing, app}: never the song title
        self.log_event("captured", t, ts=t.get("created"), source=t.get("source", "list"),
                       focus=t.get("focus") or {"in_focus": False},
                       **{k: bool(t.get(k)) for k in FLAG_KEYS}, **extra)

    def start_itch_action(self, t):
        """Remember when an itch was acted on, without changing the focus timer."""
        if t.get("itch_started_at"):
            return False
        t["itch_started_at"] = datetime.now().isoformat(timespec="seconds")
        self.save()
        return True

    def cancel_itch_action(self, t):
        if not t.pop("itch_started_at", None):
            return False
        self.save()
        return True

    def record_itch_action(self, t, minutes):
        """Keep a plain duration on the note and in its thought history. No score or verdict."""
        minutes = int(minutes)
        if not 1 <= minutes <= 1440:
            return False
        started = t.pop("itch_started_at", "")
        ended = datetime.now().isoformat(timespec="seconds")
        t.setdefault("itch_actions", []).append({"at": ended, "minutes": minutes, "started_at": started})
        self.save()
        self.log_event("itch_acted", t, ts=ended, minutes=minutes, started_at=started)
        return True

    def undo_itch_action(self, t):
        actions = t.get("itch_actions") or []
        if not actions:
            return False
        action = actions.pop()
        self.save()
        self.log_event("itch_action_undone", t, minutes=action.get("minutes", 0))
        return True

    def let_go(self, t, kind="let_go"):
        """Remove a note without destroying anything: the task goes to a trash log, its files to the trash
        folder, and the thought log records it. kind="let_go": released without action (a fear, a passed itch),
        counted in your patterns. kind="deleted": a mistake or a test note, ignored by the AI export and the
        session numbers. Returns what undo_let_go() needs."""
        l = self.list_of(t)
        idx = l["tasks"].index(t)
        self.log_event(kind, t, details=t.get("desc", ""), was_later=bool(t.get("later")), was_done=bool(t.get("done")),
                       **{k: bool(t.get(k)) for k in FLAG_KEYS})
        try:
            with open(TRASH_DIR / ("deleted_tasks.jsonl" if kind == "deleted" else "let_go_tasks.jsonl"),
                      "a", encoding="utf-8") as f:
                f.write(json.dumps(t, ensure_ascii=False) + "\n")
        except Exception as e:
            log_error(f"let-go trash log failed: {e}")
        moved = None
        d = ATT_DIR / t["id"]
        if d.exists():
            dest = TRASH_DIR / f"{int(time.time())}-{t['id']}"
            try:
                shutil.move(str(d), str(dest))
                moved = dest
            except Exception as e:
                log_error(f"move to trash failed ({d}): {e}")
        l["tasks"].remove(t)
        self.save()
        return (l, idx, moved, kind)

    def undo_let_go(self, t, token):
        l, idx, moved, kind = token
        if moved and moved.exists():
            try:
                shutil.move(str(moved), str(ATT_DIR / t["id"]))
            except Exception as e:
                log_error(f"undo move failed ({moved}): {e}")
        if l not in self.lists:
            l = self.current()
        l["tasks"].insert(min(idx, len(l["tasks"])), t)
        self.log_event("delete_undone" if kind == "deleted" else "let_go_undone", t)
        self.save()

    def _backfill_log(self):
        """First run with logging: record the tasks that already exist, so history starts complete."""
        if THOUGHT_LOG.exists():
            return
        for l in self.lists:
            for t in l["tasks"]:
                self.log_event("captured", t, ts=t.get("created"), source=t.get("source", "before_logging"),
                               focus=t.get("focus") or {"in_focus": None})

    def _task_dir(self, t):
        d = ATT_DIR / t["id"]
        d.mkdir(parents=True, exist_ok=True)
        return d

    def _unique(self, d, name):
        dest = d / name
        stem, suf, n = dest.stem, dest.suffix, 1
        while dest.exists():
            dest = d / f"{stem}-{n}{suf}"
            n += 1
        return dest

    @staticmethod
    def _rel(dest):
        try:
            return str(dest.relative_to(DATA_DIR))
        except ValueError:
            return str(dest)  # rescue location: keep absolute

    def add_image(self, t, img):
        name = f"snip-{datetime.now():%Y%m%d-%H%M%S}.png"
        for folder in (lambda: self._task_dir(t), lambda: RESCUE_DIR / "attachments" / t["id"]):
            try:
                d = folder()
                d.mkdir(parents=True, exist_ok=True)
                dest = self._unique(d, name)
                if img.save(str(dest), "PNG"):
                    t["attachments"].append({"kind": "image", "name": dest.name, "path": self._rel(dest)})
                    self.save()
                    return True
                log_error(f"image save failed at {dest}")
            except Exception as e:
                log_error(f"image save failed: {e}")
        return False

    def add_path(self, t, src):
        src = Path(src)
        if src.is_dir():  # folders are linked, not copied
            t["attachments"].append({"kind": "folder", "name": src.name, "path": str(src)})
            self.save()
            return True
        if not src.is_file():
            return False
        kind = "image" if src.suffix.lower() in IMG_EXT else "file"
        for attempt in range(3):
            try:
                dest = self._unique(self._task_dir(t), src.name)
                shutil.copy2(src, dest)
                t["attachments"].append({"kind": kind, "name": dest.name, "path": self._rel(dest)})
                self.save()
                return True
            except Exception as e:
                log_error(f"copy failed ({src}): {e}")
                time.sleep(0.3)
        # could not copy: link the original instead, so nothing is lost
        t["attachments"].append({"kind": kind, "name": src.name, "path": str(src), "linked": True})
        self.save()
        return True

    @staticmethod
    def abs_path(a):
        p = Path(a["path"])
        return p if p.is_absolute() else DATA_DIR / p

    def remove_attachment(self, t, a):
        t["attachments"].remove(a)
        p = self.abs_path(a)
        if a["kind"] != "folder" and not a.get("linked") and p.exists():  # never touch your originals
            try:
                shutil.move(str(p), str(TRASH_DIR / f"{int(time.time())}-{p.name}"))
            except Exception as e:
                log_error(f"move to trash failed ({p}): {e}")
        self.save()

    def clear_done(self, reason="cleared"):
        """Move completed notes to trash. Returns what undo_clear() needs."""
        stamp = int(time.time())
        token = []
        l = self.current()
        with open(TRASH_DIR / "cleared_tasks.jsonl", "a", encoding="utf-8") as log:
            for t in [t for t in self.tasks if t["done"]]:
                idx = l["tasks"].index(t)
                dest = TRASH_DIR / f"{stamp}-{t['id']}"
                log.write(json.dumps(t, ensure_ascii=False) + "\n")
                self.log_event(reason, t, details=t.get("desc", ""),
                               attachments=[a["kind"] for a in t.get("attachments", [])], urge=t.get("urge", False))
                d = ATT_DIR / t["id"]
                moved = None
                if d.exists():
                    try:
                        shutil.move(str(d), str(dest))
                        moved = dest
                    except Exception as e:
                        log_error(f"move to trash failed ({d}): {e}")
                token.append((t, idx, moved))
                self.tasks.remove(t)
        self.save()
        return (l, token)

    def undo_clear(self, token):
        l, items = token
        if l not in self.lists:
            l = self.current()
        for t, idx, moved in sorted(items, key=lambda x: x[1]):
            if moved and moved.exists():
                try:
                    shutil.move(str(moved), str(ATT_DIR / t["id"]))
                except Exception as e:
                    log_error(f"undo move failed ({moved}): {e}")
            l["tasks"].insert(min(idx, len(l["tasks"])), t)
            self.log_event("clear_undone", t)
        self.save()


# ---------------------------------------------------------------- export for AI
AI_PROMPT = """# Park That Thought export: my parked thoughts

I use Park That Thought, a capture-now, decide-later tool. When a thought pulls at me (often during a
focus session), I park it in a couple of seconds and go back to work. Each row below is one parked thought.

Please help me understand my patterns. Be concrete and kind, and base everything on the data:
1. Recurring themes, people, projects or worries. Group similar thoughts.
2. When I get pulled away most: time of day, weekday, and how many minutes into a focus session.
   Also how often I ask for more break time, how much I request, how late I return from breaks,
   whether that changes by time of day, and how I answer check-ins (ignoring or snoozing a lot
   can itself be a signal).
3. "urge" (shown to me as "itch") means it felt urgent but could wait (a pull from inside); "urgent" means
   it really needed doing soon. Some itches have optional acted-on counts and minutes. Describe those
   without judging them or treating them as a failure. Done is a separate note state.
4. "distraction" means something from outside broke my focus (a person, a ping, noise). What kinds, when,
   and how far into sessions? Which could I prevent (phone away, door closed, notifications off)?
5. What I keep parking but never act on, clear without doing, or let go. Recurring let-go thoughts (the same
   fear or worry coming back) are worth naming gently.
6. Lifts (small moments of joy, calm or connection) and drains (small moments that put me on edge or wore me
   down): when and around what they show up, and whether drains cluster before distractions or itches.
   Suggest ways to get more of the lifts.
7. Anything that hints at a trigger (fatigue, avoidance of hard work, social worry, tools, curiosity).
8. Suggest 1 or 2 small, specific experiments for my next week.
9. If Important work is present, use my chosen work and its deadlines to suggest a realistic next
   step for today. The list is a current snapshot, not a record of what I worked on; a nearer
   deadline does not necessarily mean the work matters more to me.
10. Where my focus time goes: minutes by what each round was for, which apps and windows pulled me away
   (the ones I marked distracting, and unmarked ones that look like it), and how my calendar shapes my day
   (focus before or after meetings, days too packed to focus).

Column guide: captured_at (local time), timer_state (what the timer was doing when I parked it:
focus = in a focus session, paused = focus session on pause, break = on a break, break_over = the break
had ended but I hadn't come back yet, none = no timer at all, unknown = older data), focus_minute (minutes into the
session when the thought came), focus_planned_min, source (how it was captured: private_note = the
quick private box, list = typed in the full list, *_paste / *_drop = pasted or dropped), outcome
(open, done, cleared = done then removed, later = kept for someday, let go = released without action,
usually a fear, a worry, a distraction or an itch that passed; abandoned = removed without doing; notes I deleted
as mistakes or tests are already left out), hours_to_resolve
(capture to done). itch_acted_count and itch_acted_minutes are optional records of acting on that
parked itch, entered at the start/end or afterward. They are observations, not scores. In the sessions table, kind is focus, break, break_extension (each time I chose
"A few more min"), or break_return (when I came back). A break_extension row records the requested
minutes in planned_min and minutes past the previous break in extension_after_overrun_min; the
following break row records the actual timer. late_back_min applies only to break_return rows.
Thoughts parked in break_over time can hint at what kept
me from coming back; thoughts with timer_state none show what my mind does outside sessions.
kind = checkin rows are friendly check-ins while I wasn't focusing; the note says what was asked and how I
answered (focus = started a session, working = I was working but forgot the timer, so that time was logged
as focus, break, fine, snooze = not now, timeout = ignored). focus_adjust rows take time I was away out of a
session (away_min). my_flags lists any flags I made myself (their names say what they mean). The music column (only when I turned music logging on) says whether media was playing
when I parked the thought, and from which app: does music change how often thoughts surface, or which kind?
In the sessions table, "for" is what I said a focus round or break was for (a project, Meal, Call, Rest, Walk),
and "apps" (only when I turned app tracking on) lists the apps and window titles I was in during a focus round
with minutes, marked distracting when I said so for that round (the same app can help in another round). Calendar events, when present, are my own
calendar for the export period plus the next two weeks (when = past, now or upcoming).
"""


def read_jsonl(*paths):
    rows, seen = [], set()
    for p in paths:
        try:
            with open(p, encoding="utf-8") as f:
                for line in f:
                    try:
                        r = json.loads(line)
                    except Exception:
                        continue
                    key = json.dumps(r, sort_keys=True)
                    if key not in seen:
                        seen.add(key)
                        rows.append(r)
        except FileNotFoundError:
            pass
    return rows


def deleted_ids(events=None):
    """Notes you deleted (and didn't undo). Kept in the log and trash, left out of every analysis."""
    if events is None:
        events = read_jsonl(THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl")
    gone = set()
    for ev in sorted(events, key=lambda r: r.get("ts", "")):
        if ev.get("event") == "deleted":
            gone.add(ev.get("id"))
        elif ev.get("event") == "delete_undone":
            gone.discard(ev.get("id"))
    return gone


def timer_state_of(f):
    """Timer state for an exported thought; older log lines (before 'state' existed) are inferred."""
    if not f:
        return "unknown"
    if f.get("state"):
        return f["state"]
    if f.get("in_focus") is True:
        return "paused" if f.get("paused") else "focus"
    if f.get("on_break"):
        return "break"
    return "none" if f.get("in_focus") is False else "unknown"


def thought_rows(store):
    """Every thought ever parked (minus deleted ones), rebuilt from the thought log with the current state on
    top: one dict per thought (title, list, captured_at, *_ever flags, outcome, resolved_at...). Used by the
    AI export and the History window."""
    events = read_jsonl(THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl")
    events.sort(key=lambda r: r.get("ts", ""))
    skip = deleted_ids(events)            # deleted notes (tests, mistakes) never reach the analysis
    events = [ev for ev in events if ev.get("id") not in skip]
    rows = {}
    for ev in events:
        tid = ev.get("id")
        if not tid:
            continue
        r = rows.setdefault(tid, {"id": tid, "captured_at": ev.get("ts"), "title": ev.get("title", ""),
                                  "list": ev.get("list", ""), "source": "unknown", "focus": {},
                                  "details": "", "attachments": "", "urge": False, "urge_ever": False,
                                  "dist_ever": False, "urgent_ever": False, "later": False,
                                  "glimmer_ever": False, "antiglimmer_ever": False, "idea_ever": False,
                                  "itch_acted_count": 0, "itch_acted_minutes": 0,
                                  "music": None, "flags_ever": [],
                                  "outcome": "open", "resolved_at": ""})
        kind = ev.get("event")
        if kind == "captured":
            r.update(captured_at=ev.get("ts"), source=ev.get("source", "unknown"), focus=ev.get("focus") or {})
            r["urge_ever"] = r["urge_ever"] or bool(ev.get("urge"))
            r["dist_ever"] = r["dist_ever"] or bool(ev.get("distraction"))
            r["urgent_ever"] = r["urgent_ever"] or bool(ev.get("urgent"))
            r["glimmer_ever"] = r["glimmer_ever"] or bool(ev.get("glimmer"))
            r["antiglimmer_ever"] = r["antiglimmer_ever"] or bool(ev.get("antiglimmer"))
            r["idea_ever"] = r["idea_ever"] or bool(ev.get("idea"))
            r["music"] = ev.get("music")
            r["flags_ever"] = sorted(set(r["flags_ever"]) | {k for k, v in ev.items() if v is True and k not in
                                                            ("undo",)})
        elif kind.endswith("_on") and kind[:-3] not in ("glimmer", "antiglimmer", "idea", "urgent", "later",
                                                       "urge", "distraction"):
            r["flags_ever"] = sorted(set(r["flags_ever"]) | {kind[:-3]})
        elif kind in ("glimmer_on", "antiglimmer_on", "idea_on"):
            r[kind[:-3] + "_ever"] = True
        elif kind == "urgent_on":
            r["urgent_ever"] = True
        elif kind == "later_on":
            r["later"] = True
        elif kind == "later_off":
            r["later"] = False
        elif kind == "let_go":
            r.update(outcome="let go", resolved_at=ev.get("ts"), title=ev.get("title", r["title"]),
                     details=ev.get("details", r["details"]))
        elif kind == "clear_undone":
            if r["outcome"] == "cleared":
                r["outcome"] = "done"
        elif kind == "let_go_undone":
            r.update(outcome="open", resolved_at="")
        elif kind == "distraction_on":
            r["dist_ever"] = True
        elif kind == "done":
            r.update(outcome="done", resolved_at=ev.get("ts"))
        elif kind == "reopened":
            r.update(outcome="open", resolved_at="")
        elif kind == "urge_on":
            r.update(urge=True, urge_ever=True)
        elif kind == "urge_off":
            r["urge"] = False
        elif kind == "itch_acted":
            r["itch_acted_count"] += 1
            try:
                r["itch_acted_minutes"] += max(0, int(ev.get("minutes", 0)))
            except (TypeError, ValueError):
                pass
        elif kind == "itch_action_undone":
            r["itch_acted_count"] = max(0, r["itch_acted_count"] - 1)
            try:
                r["itch_acted_minutes"] = max(0, r["itch_acted_minutes"] - max(0, int(ev.get("minutes", 0))))
            except (TypeError, ValueError):
                pass
        elif kind in ("cleared", "list_deleted"):
            if r["outcome"] == "done":
                r["outcome"] = "cleared"
            r.update(title=ev.get("title", r["title"]), details=ev.get("details", r["details"]),
                     attachments=", ".join(ev.get("attachments", [])) or r["attachments"])
        elif kind == "abandoned":
            r["outcome"] = "abandoned"
    # current state wins for thoughts that still exist
    for l in store.lists:
        for t in l["tasks"]:
            r = rows.get(t["id"])
            if not r:
                continue
            r.update(title=t["title"], list=l["name"], details=t.get("desc", ""), urge=t.get("urge", False),
                     attachments=", ".join(a["kind"] for a in t.get("attachments", [])))
            r["urge_ever"] = r["urge_ever"] or t.get("urge", False)
            r["dist_ever"] = r["dist_ever"] or t.get("distraction", False)
            r["urgent_ever"] = r["urgent_ever"] or t.get("urgent", False)
            r["glimmer_ever"] = r["glimmer_ever"] or t.get("glimmer", False)
            r["antiglimmer_ever"] = r["antiglimmer_ever"] or t.get("antiglimmer", False)
            r["idea_ever"] = r["idea_ever"] or t.get("idea", False)
            r["flags_ever"] = sorted(set(r["flags_ever"]) | {k for k in FLAG_KEYS if t.get(k)})
            actions = t.get("itch_actions") or []
            if len(actions) > r["itch_acted_count"]:
                r["itch_acted_count"] = len(actions)
                r["itch_acted_minutes"] = sum(max(0, int(a.get("minutes", 0))) for a in actions
                                               if isinstance(a, dict))
            if not t["done"]:
                r.update(outcome="later" if t.get("later") else "open", resolved_at="")
    return list(rows.values())


def build_ai_export(store, days=None, include_analyses=True, calendar_events=None):
    """One Markdown document: instructions, earlier AI analyses of the same period (if saved), a summary,
    thoughts as CSV, focus sessions as CSV, calendar events (when connected). Returns (text, number_of_thoughts)."""
    rows = {r["id"]: r for r in thought_rows(store)}
    cutoff = (datetime.now().timestamp() - days * 86400) if days else None

    def when(iso):
        try:
            return datetime.fromisoformat(iso)
        except Exception:
            return None
    out = [r for r in rows.values() if when(r["captured_at"]) and
           (cutoff is None or when(r["captured_at"]).timestamp() >= cutoff)]
    out.sort(key=lambda r: r["captured_at"])

    buf = io.StringIO()
    w = csv.writer(buf, lineterminator="\n")
    w.writerow(["captured_at", "weekday", "hour", "list", "source", "timer_state", "focus_minute",
                "focus_planned_min", "title", "details", "attachments", "urgent", "distraction", "urge", "itch_acted_count", "itch_acted_minutes", "lift", "drain", "idea", "my_flags", "music", "outcome", "resolved_at",
                "hours_to_resolve"])
    n_focus = n_done = n_urge = n_urge_done = n_dist = n_dist_focus = 0
    states = {}
    for r in out:
        cap = when(r["captured_at"])
        f = r["focus"] or {}
        tstate = timer_state_of(f)
        states[tstate] = states.get(tstate, 0) + 1
        infocus = "yes" if tstate in ("focus", "paused") else "no"
        n_focus += infocus == "yes"
        resolved = when(r["resolved_at"]) if r["resolved_at"] else None
        hours = round((resolved - cap).total_seconds() / 3600, 1) if resolved else ""
        done = r["outcome"] in ("done", "cleared")
        n_done += done
        n_urge += r["urge_ever"]
        n_dist += r["dist_ever"]
        n_dist_focus += r["dist_ever"] and infocus == "yes"
        n_urge_done += r["urge_ever"] and done
        w.writerow([cap.strftime("%Y-%m-%d %H:%M"), cap.strftime("%a"), cap.hour, r["list"], r["source"], tstate,
                    f.get("minute", ""), f.get("planned", ""), r["title"], r["details"].replace("\r", ""),
                    r["attachments"], "yes" if r["urgent_ever"] else "no", "yes" if r["dist_ever"] else "no", "yes" if r["urge_ever"] else "no",
                    r["itch_acted_count"], r["itch_acted_minutes"],
                    "yes" if r["glimmer_ever"] else "no", "yes" if r["antiglimmer_ever"] else "no",
                    "yes" if r["idea_ever"] else "no",
                    ", ".join(w for k, _i, w, _t in FLAG_DEFS if k not in BUILTIN_FLAG_KEYS and k in r["flags_ever"]),
                    "" if not r.get("music") else (f"playing ({r['music'].get('app') or '?'})"
                                                   if r["music"].get("playing") else "not playing"),
                    r["outcome"],
                    resolved.strftime("%Y-%m-%d %H:%M") if resolved else "", hours])

    sessions = [x for x in read_jsonl(FOCUS_LOG, RESCUE_DIR / "focus_log.rescue.jsonl")
                if cutoff is None or (when(x.get("end", "")) and when(x["end"]).timestamp() >= cutoff)]
    sbuf = io.StringIO()
    sw = csv.writer(sbuf, lineterminator="\n")
    sw.writerow(["kind", "start", "end", "planned_min", "actual_min", "completed", "late_back_min",
                 "extension_after_overrun_min", "note", "for", "apps"])
    picked = {x.get("session_start"): set(x.get("distracting") or []) for x in sessions
              if x.get("kind") == "app_marks"}       # later rows win: the last press on the card
    sessions = [x for x in sessions if x.get("kind") != "app_marks"]

    def apps_cell(x):
        marked = picked.get(x.get("start"), set())
        return "; ".join(f"{a['app']}" + (" (distracting)" if a["app"] in marked else "")
                         + (f" [{a['title']}]" if a.get("title") else "") + f" {a['min']} min"
                         for a in x.get("apps") or [])
    for x in sessions:
        k = x.get("kind", "focus")
        if k == "break_return":
            sw.writerow([k, x.get("break_ended", ""), x.get("end", ""), "", "", "", x.get("overrun_min", ""), "", ""])
        elif k == "break_extension":
            sw.writerow([k, x.get("break_ended", ""), x.get("end", ""), x.get("requested_min", ""),
                         "", "", "", x.get("overrun_min", ""), "Requested more break time"])
        elif k == "checkin":
            sw.writerow([k, x.get("start", ""), x.get("end", ""), "", "", "", "", "",
                         f"asked: {x.get('message', '')} | answered: {x.get('response', '')}"])
        else:
            sw.writerow([k, x.get("start", ""), x.get("end", ""), x.get("planned_min", ""), x.get("focused_min", ""),
                         "yes" if x.get("completed") else "no", "", "", x.get("note", ""), x.get("on", ""),
                         apps_cell(x)])
    checkins = [x for x in sessions if x.get("kind") == "checkin"]
    focus_s = [x for x in sessions if x.get("kind", "focus") == "focus"]
    by_for, by_app, dist_app = {}, {}, {}
    for x in sessions:
        if x.get("on") and x.get("kind", "focus") in ("focus", "break"):
            key = (x.get("kind", "focus"), x["on"])
            by_for[key] = by_for.get(key, 0) + (x.get("focused_min", 0) or 0)
        for a in x.get("apps") or []:
            by_app[a["app"]] = by_app.get(a["app"], 0) + a["min"]
            if a["app"] in picked.get(x.get("start"), ()):
                dist_app[a["app"]] = dist_app.get(a["app"], 0) + a["min"]
    for_line = ", ".join(f"{t} {round(m)} min" + (" (break)" if k == "break" else "")
                         for (k, t), m in sorted(by_for.items(), key=lambda kv: -kv[1])[:12])
    app_line = ", ".join(f"{a} {round(m)} min" + (f" ({round(dist_app[a])} distracting)" if a in dist_app else "")
                         for a, m in sorted(by_app.items(), key=lambda kv: -kv[1])[:12])
    cal_buf = io.StringIO()
    cw = csv.writer(cal_buf, lineterminator="\n")
    cw.writerow(["title", "start", "end", "minutes", "calendar", "when"])
    now_aware = datetime.now().astimezone()
    seen_events = set()
    for e in sorted(calendar_events or [], key=lambda e: e["start"]):
        if (cutoff and e["end"].timestamp() < cutoff) or (e["title"], e["start"]) in seen_events:
            continue
        seen_events.add((e["title"], e["start"]))
        cw.writerow([e["title"], e["start"].strftime("%Y-%m-%d %H:%M"), e["end"].strftime("%Y-%m-%d %H:%M"),
                     round((e["end"] - e["start"]).total_seconds() / 60), e.get("calendar_name", ""),
                     "past" if e["end"] <= now_aware else "now" if e["start"] <= now_aware else "upcoming"])
    returns = [x.get("overrun_min", 0) for x in sessions if x.get("kind") == "break_return"]
    extensions = [x for x in sessions if x.get("kind") == "break_extension"]

    span = f"last {days} days" if days else "all time"
    pct = (lambda a, b: f"{round(100 * a / b)}%" if b else "n/a")
    summary = (f"## Summary ({span}, exported {datetime.now():%Y-%m-%d %H:%M})\n\n"
               f"- Thoughts parked: {len(out)}\n"
               f"- During a focus session: {n_focus} ({pct(n_focus, len(out))})\n"
               f"- By timer state: " + ", ".join(f"{k.replace('_', ' ')} {states.get(k, 0)}" for k in
                                               ("focus", "paused", "break", "break_over", "none", "unknown")
                                               if states.get(k)) + "\n"
               f"- Done: {n_done} ({pct(n_done, len(out))})\n"
               f"- Marked urge: {n_urge}, of which done: {n_urge_done} ({pct(n_urge_done, n_urge)})\n"
               f"- Itch actions recorded: {sum(r['itch_acted_count'] for r in out)}, "
               f"minutes: {sum(r['itch_acted_minutes'] for r in out)}\n"
               f"- Marked distraction: {n_dist}, during a focus session: {n_dist_focus}\n"
               f"- Let go (released without action): {sum(1 for r in out if r['outcome'] == 'let go')}, "
               f"moved to later: {sum(1 for r in out if r['outcome'] == 'later')}, "
               f"marked urgent: {sum(1 for r in out if r['urgent_ever'])}\n"
               f"- Lifts: {sum(1 for r in out if r['glimmer_ever'])}, "
               f"drains: {sum(1 for r in out if r['antiglimmer_ever'])}, "
               f"ideas: {sum(1 for r in out if r['idea_ever'])}\n"
               f"- Focus sessions: {len(focus_s)}, completed: {sum(1 for x in focus_s if x.get('completed'))}, "
               f"focused minutes: {round(sum(x.get('focused_min', 0) for x in focus_s))}\n"
               f"- Breaks returned from: {len(returns)}, average minutes late: "
               f"{round(sum(returns) / len(returns), 1) if returns else 'n/a'}\n"
               f"- Break extensions requested: {len(extensions)}, extra minutes requested: "
               f"{round(sum(x.get('requested_min', 0) for x in extensions), 1)}\n"
               f"- Check-ins answered: {len(checkins)} ("
               + ", ".join(f"{k}: {sum(1 for x in checkins if x.get('response') == k)}"
                           for k in ("focus", "break", "fine", "snooze", "timeout")) + ")\n"
               + (f"- Time by what it was for: {for_line}\n" if for_line else "")
               + (f"- Apps during focus (tracked): {app_line}\n" if app_line else ""))
    workbuf = io.StringIO()
    ww = csv.writer(workbuf, lineterminator="\n")
    ww.writerow(["title", "due_at", "status", "hours_from_export", "hours_until_next_deadline", "completed_at"])
    work_now = datetime.now()
    calendar_active = bool(store.settings.get("google_calendar_auth") or store.settings.get("google_calendar_feed")
                           or store.settings.get("google_calendar_feeds"))
    active_work = sorted((i for i in store.important_work if not i.get("done_at") and not calendar_active),
                         key=lambda i: work_due(i) or datetime.max)
    finished_work = [i for i in store.important_work if i.get("done_at") and not calendar_active]
    for index, item in enumerate(active_work + finished_work):
        due = work_due(item)
        next_due = work_due(active_work[index + 1]) if index + 1 < len(active_work) else None
        ww.writerow([item.get("title", ""), item.get("due", ""),
                     "finished" if item.get("done_at") else "open",
                     round((due.timestamp() - work_now.timestamp()) / 3600, 1) if due else "",
                     round((next_due.timestamp() - due.timestamp()) / 3600, 1) if due and next_due else "",
                     item.get("done_at") or ""])
    earlier = analyses_section(days) if include_analyses else ""
    text = (AI_PROMPT + "\n" + earlier + summary + "\n## Thoughts (CSV)\n\n```csv\n" + buf.getvalue() + "```\n\n"
            "## Focus sessions (CSV)\n\n```csv\n" + sbuf.getvalue() + "```\n\n"
            "## Important work (current snapshot, CSV)\n\n```csv\n" + workbuf.getvalue() + "```\n"
            + ("\n## Calendar events (CSV)\n\n```csv\n" + cal_buf.getvalue() + "```\n"
               if len(seen_events) else ""))
    return text, len(out)


# ---------------------------------------------------------------- saved AI analyses
def span_label(days):
    return f"last {days:g} days" if days else "everything"


def load_analyses():
    """Saved AI analyses, oldest first. Each: id, saved_at, covers_from ('' = from the start), covers_to,
    days (None = everything), text."""
    rows = []
    try:
        with open(AI_NOTES, encoding="utf-8") as f:
            for line in f:
                try:
                    r = json.loads(line)
                except Exception:
                    continue
                if isinstance(r, dict) and r.get("text"):
                    rows.append(r)
    except FileNotFoundError:
        pass
    rows.sort(key=lambda r: r.get("saved_at", ""))
    return rows


def save_analyses(rows):
    AI_NOTES.parent.mkdir(parents=True, exist_ok=True)
    tmp = AI_NOTES.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        for r in sorted(rows, key=lambda r: r.get("saved_at", "")):
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    for i in range(10):                 # OneDrive or antivirus can hold the file for a moment
        try:
            os.replace(tmp, AI_NOTES)
            return True
        except OSError:
            time.sleep(0.2)
    log_error("saving ai_analyses.jsonl failed")
    return False


def analyses_for(days):
    """Analyses whose period overlaps the last `days` days (all of them when days is None)."""
    rows = load_analyses()
    if not days:
        return rows
    cutoff = datetime.now() - timedelta(days=days)

    def end(r):
        try:
            return datetime.fromisoformat(r.get("covers_to") or r.get("saved_at"))
        except Exception:
            return datetime.now()
    return [r for r in rows if end(r) >= cutoff]


def analyses_section(days):
    rows = analyses_for(days)
    if not rows:
        return ""
    out = ["## My earlier AI analyses of this period\n",
           "I already asked an AI about part of this period and saved the answers below, oldest first. "
           "Please build on them instead of starting over: say what is new or has changed since the latest one, "
           "check whether the experiments suggested there seem to have worked (compare before and after in the "
           "data), correct anything the new data contradicts, and don't repeat points that still hold. "
           "Only thoughts and sessions after an analysis's end date are new to it.\n"]
    for r in rows:
        frm = (r.get("covers_from") or "")[:10] or "the start"
        to = (r.get("covers_to") or r.get("saved_at", ""))[:10]
        out.append(f"### Analysis saved {r.get('saved_at', '')[:16].replace('T', ' ')} "
                   f"(covered {span_label(r.get('days'))}: {frm} to {to})\n")
        body = r["text"].strip()
        body = re.sub(r"(?m)^(#{1,3}) ", lambda m: "#" * min(6, len(m.group(1)) + 3) + " ", body)  # keep headings under ours
        out.append(body + "\n")
    return "\n".join(out) + "\n"


class AnalysesDialog(QDialog):
    """Saved AI analyses: pick one on the left, read or edit it on the right, or add a new one."""

    def __init__(self, store):
        super().__init__(None, Qt.WindowStaysOnTopHint)
        self.store = store
        self.setWindowTitle("AI analyses")
        self.setObjectName("panel")
        self.setStyleSheet(STYLE + f"""
            QListWidget {{ background: {C['surface']}; color: {C['text']}; border: 1px solid {C['border']};
                border-radius: 8px; padding: 4px; outline: none; }}
            QListWidget::item {{ padding: 6px 6px; border-radius: 6px; }}
            QListWidget::item:selected {{ background: {C['accent']}; color: white; }}
            QListWidget::item:hover:!selected {{ background: {C['surface_hi']}; }}""")
        self.resize(760, 520)
        self.rows = []
        self._new = None              # a draft not saved yet
        lay = QVBoxLayout(self)
        lay.setSpacing(8)
        intro = QLabel("Paste the AI's answer here after you analyze your thoughts. The next time you copy for AI, "
                       "analyses from the same period go along with it, so the AI builds on them instead of "
                       "starting over.")
        intro.setObjectName("hint")
        intro.setWordWrap(True)
        lay.addWidget(intro)
        split = QSplitter(Qt.Horizontal)
        self.list = QListWidget()
        self.list.currentRowChanged.connect(self._show)
        split.addWidget(self.list)
        right = QWidget()
        rv = QVBoxLayout(right)
        rv.setContentsMargins(0, 0, 0, 0)
        row = QHBoxLayout()
        row.addWidget(QLabel("Covers:"))
        self.covers = QComboBox()
        row.addWidget(self.covers, 1)
        rv.addLayout(row)
        self.meta = QLabel("")
        self.meta.setObjectName("hint")
        rv.addWidget(self.meta)
        self.text = QPlainTextEdit()
        self.text.setPlaceholderText("Paste the AI's analysis here")
        rv.addWidget(self.text, 1)
        split.addWidget(right)
        split.setSizes([220, 540])
        lay.addWidget(split, 1)
        btns = QHBoxLayout()
        self.add_btn = QPushButton("New")
        self.add_btn.clicked.connect(lambda: self.start_new())
        self.del_btn = QPushButton("Delete")
        self.del_btn.clicked.connect(self._delete)
        self.save_btn = QPushButton("Save")
        self.save_btn.clicked.connect(self._save)
        close = QPushButton("Close")
        close.clicked.connect(self.close)
        btns.addWidget(self.add_btn)
        btns.addWidget(self.del_btn)
        btns.addStretch(1)
        btns.addWidget(self.save_btn)
        btns.addWidget(close)
        lay.addLayout(btns)

    # ---- helpers
    def _cover_options(self):
        """(label, (days, from, to)). The first is what you copied last, when there is one."""
        now = datetime.now()
        opts = []
        last = self.store.settings.get("last_ai_export")
        if last:
            frm = (last.get("from") or "")[:10] or "the start"
            opts.append((f"What I copied last ({span_label(last.get('days'))}, {frm} to {last.get('to', '')[:10]})",
                         (last.get("days"), last.get("from", ""), last.get("to", ""))))
        for d in (7, 30):
            opts.append((f"Last {d} days", (d, (now - timedelta(days=d)).isoformat(timespec="seconds"),
                                              now.isoformat(timespec="seconds"))))
        opts.append(("Everything", (None, "", now.isoformat(timespec="seconds"))))
        return opts

    def reload(self, select_id=None):
        self.rows = list(reversed(load_analyses()))      # newest first
        self.list.blockSignals(True)
        self.list.clear()
        if self._new is not None:
            self.list.addItem(QListWidgetItem("New analysis (not saved)"))
        for r in self.rows:
            when = r.get("saved_at", "")[:16].replace("T", " ")
            self.list.addItem(QListWidgetItem(f"{when}\n{span_label(r.get('days'))}"))
        self.list.blockSignals(False)
        idx = 0
        if select_id:
            idx = next((i for i, r in enumerate(self.rows) if r["id"] == select_id), 0) + (self._new is not None)
        if self.list.count():
            self.list.setCurrentRow(idx)
            self._show(idx)
        else:
            self.start_new(clipboard=False)

    def _current(self):
        i = self.list.currentRow()
        if self._new is not None:
            return self._new if i == 0 else (self.rows[i - 1] if 0 < i <= len(self.rows) else None)
        return self.rows[i] if 0 <= i < len(self.rows) else None

    def _show(self, i):
        r = self._current()
        self.covers.clear()
        if r is None:
            self.text.clear()
            self.meta.setText("")
            return
        if r is self._new:
            for label, val in self._cover_options():
                self.covers.addItem(label, val)
            self.covers.setEnabled(True)
            self.meta.setText("Not saved yet")
        else:
            frm = (r.get("covers_from") or "")[:10] or "the start"
            self.covers.addItem(f"{span_label(r.get('days'))}, {frm} to {(r.get('covers_to') or '')[:10]}")
            self.covers.setEnabled(False)
            self.meta.setText(f"Saved {r.get('saved_at', '')[:16].replace('T', ' ')}"
                              + (f", edited {r['edited_at'][:16].replace('T', ' ')}" if r.get("edited_at") else ""))
        self.text.setPlainText(r.get("text", ""))
        self.del_btn.setText("Discard" if r is self._new else "Delete")

    def start_new(self, clipboard=True):
        """A fresh draft. Takes the clipboard if it looks like an AI answer (not our own export)."""
        text = ""
        if clipboard:
            clip = QGuiApplication.clipboard().text() or ""
            if clip.strip() and not clip.lstrip().startswith("# Park That Thought export"):
                text = clip.strip()
        self._new = {"text": text}
        self.reload()
        self.list.setCurrentRow(0)
        self._show(0)
        self.text.setFocus()

    # ---- actions
    def _save(self):
        r = self._current()
        txt = self.text.toPlainText().strip()
        if r is None:
            return
        if not txt:
            self.meta.setText("Nothing to save yet. Paste the AI's answer first.")
            return
        rows = load_analyses()
        now = datetime.now().isoformat(timespec="seconds")
        if r is self._new:
            days, frm, to = self.covers.currentData() or (None, "", now)
            new = {"id": uuid.uuid4().hex[:10], "saved_at": now, "covers_from": frm, "covers_to": to,
                   "days": days, "text": txt}
            rows.append(new)
            sel = new["id"]
            self._new = None
        else:
            for x in rows:
                if x.get("id") == r.get("id"):
                    x["text"], x["edited_at"] = txt, now
            sel = r.get("id")
        if save_analyses(rows):
            self.reload(sel)
            self.meta.setText(self.meta.text() + "  \u2713 saved")
        else:
            self.meta.setText("Couldn't save (file busy?). Try again in a moment.")

    def _delete(self):
        r = self._current()
        if r is None:
            return
        if r is self._new:
            self._new = None
            self.reload()
            return
        if QMessageBox.question(self, "Delete analysis", "Delete this saved analysis? This can't be undone.") \
                != QMessageBox.Yes:
            return
        save_analyses([x for x in load_analyses() if x.get("id") != r.get("id")])
        self.reload()

    def open_dialog(self, new=False):
        self._new = None
        self.reload()
        if new:
            self.start_new()
        self.show()
        apply_share_privacy(self)
        self.raise_()
        self.activateWindow()


# ---------------------------------------------------------------- scribble gesture
class _Axis:
    """Scribble detector along one axis (0 = x / left-right, 1 = y / up-down). Tilt is allowed."""

    def __init__(self, axis):
        self.axis = axis
        self.dir = 0
        self.anchor = None
        self.extreme = None
        self.revs = []

    def step(self, p, now):
        a, o = self.axis, 1 - self.axis
        if self.anchor is None:
            self.anchor = self.extreme = p
            return False
        if self.dir == 0:
            if abs(p[a] - self.anchor[a]) >= SCRIBBLE_HYST_PX:
                self.dir = 1 if p[a] > self.anchor[a] else -1
                self.extreme = p
            return False
        if (p[a] - self.extreme[a]) * self.dir > 0:      # still going the same way
            self.extreme = p
            return False
        if abs(self.extreme[a] - p[a]) < SCRIBBLE_HYST_PX:  # jitter
            return False
        seg = abs(self.extreme[a] - self.anchor[a])      # real reversal
        drift = abs(self.extreme[o] - self.anchor[o])
        self.anchor, self.extreme, self.dir = self.extreme, p, -self.dir
        if seg > SCRIBBLE_MAX_SEG_PX or drift > seg * SCRIBBLE_MAX_TILT:
            self.revs = []                               # long sweep or wrong direction: normal mouse use
            return False
        if seg < SCRIBBLE_TUNE["min_seg"]:
            return False
        self.revs = [t for t in self.revs if now - t <= SCRIBBLE_WINDOW_S] + [now]
        if len(self.revs) >= SCRIBBLE_TUNE["revs"]:
            self.revs = []
            return True
        return False


class ScribbleDetector(QObject):
    """One global mouse listener, two gestures: up-down = quick note, left-right = full list."""
    vertical = Signal()
    horizontal = Signal()

    def __init__(self):
        super().__init__()
        self.enabled = True
        self.available = False
        self.axes = {1: _Axis(1), 0: _Axis(0)}
        self.last_fire = 0.0
        try:
            from pynput import mouse
            self.listener = mouse.Listener(on_move=self._on_move)
            self.listener.daemon = True
            self.listener.start()
            self.available = True
        except Exception as e:  # no pynput or no display: app still works, bubble click only
            self.listener = None
            print("Scribble gesture unavailable:", e)

    def feed(self, x, y):
        self._on_move(x, y)

    def _on_move(self, x, y):
        if not self.enabled:
            return
        now = time.monotonic()
        for axis, sig in ((1, self.vertical), (0, self.horizontal)):
            if self.axes[axis].step((x, y), now) and now - self.last_fire >= SCRIBBLE_COOLDOWN_S:
                self.last_fire = now
                for ax in self.axes.values():
                    ax.revs = []
                sig.emit()
                return

    def stop(self):
        if self.listener:
            self.listener.stop()


# ---------------------------------------------------------------- focus timer
class FocusTimer(QObject):
    """One countdown, either a focus session or a break. State lives in settings['timer'] so it survives
    a restart. When a break ends, an 'overrun' clock starts (settings['break_over_at']) and counts up until
    you're back, so a long break is visible instead of silent.
    Every session is appended to parking_lot_data/focus_log.jsonl."""
    tick = Signal()
    finished = Signal(str, float)  # kind ("focus" | "break"), planned minutes
    started = Signal()
    ended = Signal()        # finished or stopped
    away_back = Signal(float, bool, str)   # minutes away during focus, still the same session, session start
    overrun_return = Signal(float)           # input resumed after being away while a break was over
    AWAY_S = 300            # no keyboard or mouse for this long during focus counts as "away"

    def __init__(self, store):
        super().__init__()
        self.store = store
        self._away_from = self._away_cap = self._away_session = None
        self._overrun_away = False
        self.apps, self.last_apps, self._app_ticks = {}, [], 0
        self.qt = QTimer()
        self.qt.setInterval(1000)
        self.qt.timeout.connect(self._tick)
        st = self.state
        if st:
            if not st.get("paused_left") and time.time() >= st["end"]:
                self._log(True, note="finished while app was closed")  # quiet, no confetti
                was_break = self.kind == "break"
                end = st["end"]
                self._clear()
                if was_break:
                    self.store.settings["break_over_at"] = end
                    self.store.settings["break_over_min"] = st["minutes"]
                    self.store.save()
                    self.qt.start()
            else:
                self.qt.start()
        elif self.overrun_since:
            self.qt.start()

    @property
    def kind(self):
        return (self.state or {}).get("kind", "focus")

    @property
    def overrun_since(self):
        return self.store.settings.get("break_over_at")

    def overrun_min(self):
        t = self.overrun_since
        return max(0.0, (time.time() - t) / 60) if t else 0.0

    def overrun_label(self):
        length = self.store.settings.get("break_over_min")
        prefix = f"{fmt_min(length)} min break" if length else "Break"
        return f"{prefix} ended {int(self.overrun_min())} min ago"

    def clear_overrun(self, record_return=True):
        """Stop the amber counter; log a return only when the user actually comes back."""
        t = self.overrun_since
        if not t:
            return
        if record_return:
            self._write({"kind": "break_return", "end": datetime.now().isoformat(timespec="seconds"),
                         "break_ended": datetime.fromtimestamp(t).isoformat(timespec="seconds"),
                         "overrun_min": round(self.overrun_min(), 1)})
        self.store.settings.pop("break_over_at", None)
        self.store.settings.pop("break_over_min", None)
        self._overrun_away = False
        self.store.save()
        if not self.running:
            self.qt.stop()
        self.tick.emit()

    @property
    def state(self):
        return self.store.settings.get("timer")

    @property
    def running(self):
        return bool(self.state)

    @property
    def paused(self):
        return bool(self.state and self.state.get("paused_left") is not None)

    def remaining(self):
        st = self.state
        if not st:
            return 0
        if st.get("paused_left") is not None:
            return st["paused_left"]
        return max(0.0, st["end"] - time.time())

    def progress(self):
        """1.0 = full time left, 0.0 = done."""
        st = self.state
        return self.remaining() / (st["minutes"] * 60) if st else 0.0

    def start(self, minutes, kind="focus"):
        if self.running:
            self.stop()
        self.clear_overrun()
        now = time.time()
        self.store.settings["timer"] = {"minutes": minutes, "started": now, "end": now + minutes * 60,
                                        "paused_left": None, "kind": kind}
        self.apps, self._app_ticks = {}, 0
        self.store.save()
        self.qt.start()
        self.tick.emit()
        self.started.emit()

    def set_on(self, text):
        """What this round is for ("thesis", "Meal"). Focus tags are remembered for next time."""
        text = " ".join(str(text or "").split())[:80]
        st = self.state
        if not st or not text:
            return
        st["on"] = text
        if st.get("kind", "focus") == "focus":
            recent = [t for t in self.store.settings.get("recent_tags", []) if t.lower() != text.lower()]
            self.store.settings["recent_tags"] = [text] + recent[:4]
        self.store.save()
        self.tick.emit()

    APP_SAMPLE_S = 5

    def _sample_app(self):
        """Opt-in: every few seconds of an unpaused focus round, note which app and window you're in.
        Idle stretches don't count (the away check handles those)."""
        if not (self.store.settings.get("track_apps", True) and self.running and self.kind == "focus"
                and not self.paused):
            return
        self._app_ticks += 1
        if self._app_ticks % self.APP_SAMPLE_S or idle_seconds() >= 60:
            return
        fg = foreground_app()
        if fg:
            self.apps[fg] = self.apps.get(fg, 0) + self.APP_SAMPLE_S

    def app_minutes(self, top=12):
        """[{app, title, min}] for this round, biggest first."""
        rows = sorted(self.apps.items(), key=lambda kv: -kv[1])[:top]
        return [{"app": a, "title": t, "min": round(s / 60, 1)} for (a, t), s in rows]

    def extend_break(self, minutes):
        """Record each explicit 'A few more min' choice without calling it a return from break."""
        t = self.overrun_since
        self._write({"kind": "break_extension", "end": datetime.now().isoformat(timespec="seconds"),
                     "break_ended": datetime.fromtimestamp(t).isoformat(timespec="seconds") if t else "",
                     "overrun_min": round(self.overrun_min(), 1) if t else 0,
                     "requested_min": minutes})
        self.clear_overrun(record_return=False)
        self.start(minutes, "break")

    def pause(self):
        if self.running and not self.paused:
            self.state["paused_left"] = self.remaining()
            self.store.save()
            self.tick.emit()

    def resume(self):
        if self.paused:
            self.state["end"] = time.time() + self.state["paused_left"]
            self.state["paused_left"] = None
            self.store.save()
            self.tick.emit()

    def stop(self):
        if self.running:
            if self._away_from is not None and self._away_cap is None:
                self._away_cap = time.time()
            self._log(False)
            self._clear()

    def _watch_away(self):
        """Notice when you leave mid-focus (no input for AWAY_S) and when you're back, so the time away can be
        taken out of the session instead of counting as focus. Windows only (idle time is 0 elsewhere)."""
        now, idle = time.time(), idle_seconds()
        if self._away_from is None:
            if self.running and self.kind == "focus" and not self.paused and idle >= self.AWAY_S:
                self._away_session = self.state["started"]
                self._away_from = max(now - idle, self._away_session)
                self._away_cap = None
            return
        if idle < 5:
            end = self._away_cap or (now - idle)
            mins = max(0.0, (end - self._away_from) / 60)
            same = bool(self.running and self.state.get("started") == self._away_session)
            start_iso = datetime.fromtimestamp(self._away_session).isoformat(timespec="seconds")
            self._away_from = self._away_cap = None
            if mins >= self.AWAY_S / 60:
                self.away_back.emit(round(mins, 1), same, start_iso)

    def _watch_overrun_return(self):
        """Ask once on input after an idle stretch; do not infer or record what the user did away."""
        if self.running or not self.overrun_since:
            self._overrun_away = False
            return
        idle = idle_seconds()
        if idle >= 60:
            self._overrun_away = True
        elif self._overrun_away and idle < 5 and self.overrun_min() >= 1:
            self._overrun_away = False
            self.overrun_return.emit(self.overrun_min())

    def drifted_max(self):
        """Whole minutes of the running focus round that can still be taken out (time so far minus earlier trims)."""
        st = self.state
        if not st or self.kind != "focus":
            return 0
        return int(max(0.0, st["minutes"] * 60 - self.remaining() - st.get("away_s", 0)) // 60)

    def take_out(self, minutes):
        """You drifted (phone, a rabbit hole): take those minutes out of this round's focus time. Returns
        the minutes taken, capped at the focus time so far."""
        minutes = max(0, min(int(minutes or 0), self.drifted_max()))
        if minutes:
            self.trim_away(minutes, True, "")
            self.tick.emit()
        return minutes

    def trim_away(self, minutes, same_session, start_iso):
        """Take time away out of a focus session: the running one (its log row will say so), or a logged one
        (a focus_adjust row; the log itself is append-only)."""
        if same_session and self.running:
            self.state["away_s"] = self.state.get("away_s", 0) + minutes * 60
            self.store.save()
        else:
            self._write({"kind": "focus_adjust", "session_start": start_iso,
                         "end": datetime.now().isoformat(timespec="seconds"), "away_min": round(minutes, 1)})

    def _tick(self):
        self._watch_away()
        self._watch_overrun_return()
        self._sample_app()
        if not self.running:
            if self.overrun_since:
                self.tick.emit()  # amber "+N" keeps counting
            elif self._away_from is None:
                self.qt.stop()
            return
        if not self.paused and self.remaining() <= 0:
            if self._away_from is not None and self._away_cap is None:
                self._away_cap = time.time()     # the session ended while you were away
            m, kind = self.state["minutes"], self.kind
            self.last_session = {"kind": kind, "start": self.state["started"], "end": time.time(), "minutes": m,
                                 "on": self.state.get("on", "")}
            self._log(True)
            self._clear()
            if kind == "break":
                self.store.settings["break_over_at"] = time.time()
                self.store.settings["break_over_min"] = m
                self.store.save()
                self.qt.start()
                self.tick.emit()  # show "Break ended" right away
            self.finished.emit(kind, float(m))
            return
        self.tick.emit()

    def _clear(self):
        self.store.settings.pop("timer", None)
        self.store.save()
        if self._away_from is None:
            self.qt.stop()                  # otherwise keep ticking until you're back from being away
        self.tick.emit()
        self.ended.emit()

    def _log(self, completed, note=None):
        st = self.state
        away = st.get("away_s", 0)
        focused = max(0.0, st["minutes"] * 60 - self.remaining() - away)
        row = {"kind": st.get("kind", "focus"),
               "start": datetime.fromtimestamp(st["started"]).isoformat(timespec="seconds"),
               "end": datetime.now().isoformat(timespec="seconds"),
               "planned_min": st["minutes"], "focused_min": round(focused / 60, 1), "completed": completed}
        if away:
            row["away_min"] = round(away / 60, 1)
        if note:
            row["note"] = note
        if st.get("on"):
            row["on"] = st["on"]
        self.last_apps = self.app_minutes()
        if self.last_apps and row["kind"] == "focus":
            row["apps"] = self.last_apps
        self.apps = {}
        self._write(row)

    @staticmethod
    def _write(row):
        line = json.dumps(row) + "\n"
        for target in (FOCUS_LOG, RESCUE_DIR / "focus_log.rescue.jsonl"):
            for attempt in range(5):
                try:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with open(target, "a", encoding="utf-8") as f:
                        f.write(line)
                    return
                except Exception as e:
                    log_error(f"focus log write failed ({target}): {e}")
                    time.sleep(0.2)

    @staticmethod
    def today_stats():
        n, mins, today = 0, 0.0, datetime.now().date().isoformat()
        try:
            with open(FOCUS_LOG, encoding="utf-8") as f:
                for line in f:
                    try:
                        r = json.loads(line)
                    except Exception:
                        continue
                    if r.get("kind") == "focus_adjust" and str(r.get("session_start", "")).startswith(today):
                        mins -= r.get("away_min", 0)     # time away taken out after the session ended
                        continue
                    if r.get("kind", "focus") != "focus":
                        continue
                    if r.get("end", "").startswith(today):
                        mins += r.get("focused_min", 0)
                        n += 1 if r.get("completed") else 0
        except FileNotFoundError:
            pass
        return n, round(max(0.0, mins))

    @staticmethod
    def today_by_tag():
        """[(tag, whole minutes)] of today's tagged focus, biggest first."""
        today, by = datetime.now().date().isoformat(), {}
        for r in read_jsonl(FOCUS_LOG):
            if r.get("kind", "focus") == "focus" and r.get("on") and str(r.get("end", "")).startswith(today):
                by[r["on"]] = by.get(r["on"], 0) + r.get("focused_min", 0)
        return sorted(((t, round(m)) for t, m in by.items() if m >= 1), key=lambda x: -x[1])


def send_phone_push(topic, title, message, priority=4, on_done=None):
    """Push via ntfy in a background thread. on_done(ok, info) is called from that thread, so pass a
    Qt signal's emit (queued to the GUI thread), never a widget method. Failures also go to error.log."""
    if not topic:
        return
    import threading
    import urllib.request

    def go():
        try:
            req = urllib.request.Request(f"{NTFY_SERVER}/{topic}", data=message.encode("utf-8"), method="POST",
                                         headers={"Title": title, "Priority": str(priority), "Tags": "hourglass"})
            urllib.request.urlopen(req, timeout=10).read()
            ok, info = True, ""
        except Exception as e:
            log_error(f"phone push failed: {e}")
            ok, info = False, str(e)
        if on_done:
            try:
                on_done(ok, info)
            except Exception:
                pass
    threading.Thread(target=go, daemon=True).start()


def fmt_min(m):
    """25.0 -> '25', 0.5 -> '0.5'"""
    m = round(float(m), 1)
    return str(int(m)) if m == int(m) else str(m)


def short_text(text, n):
    text = str(text or "")
    return text if len(text) <= n else text[:n - 1].rstrip() + "…"


class MinSpin(QDoubleSpinBox):
    """Minutes field: plain number, halves allowed (0.5 = 30 s, handy for testing)."""

    def textFromValue(self, v):
        return fmt_min(v)


def fmt_mmss(sec):
    sec = int(round(sec))
    return f"{sec // 60}:{sec % 60:02d}"


class Confetti(QWidget):
    """Full-screen, click-through celebration. Hidden from screen share like everything else."""
    COLORS = ["#8c2f39", "#d4a017", "#2e6b4f", "#1f6f78", "#b5532b", "#f3e3c3", "#5b8def"]

    def __init__(self):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool
                         | Qt.WindowTransparentForInput)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.timer = QTimer(self)
        self.timer.setInterval(16)
        self.timer.timeout.connect(self._step)
        self.parts, self.t0, self.lines = [], 0.0, []

    def burst(self, origin, lines):
        screen = QGuiApplication.screenAt(origin) or QGuiApplication.primaryScreen()
        g = screen.geometry()
        self.setGeometry(g)
        ox, oy = origin.x() - g.left(), origin.y() - g.top()
        toward = -1 if ox > g.width() / 2 else 1
        self.parts = []
        for _ in range(170):  # from the circle
            self.parts.append([ox, oy, toward * random.uniform(2, 16) + random.uniform(-4, 4),
                               random.uniform(-22, -6), random.choice(self.COLORS),
                               random.uniform(5, 10), random.uniform(0, 360), random.uniform(-12, 12)])
        for _ in range(110):  # gentle rain from the top
            self.parts.append([random.uniform(0, g.width()), random.uniform(-200, 0), random.uniform(-1.5, 1.5),
                               random.uniform(1, 4), random.choice(self.COLORS),
                               random.uniform(5, 9), random.uniform(0, 360), random.uniform(-8, 8)])
        self.lines = lines
        self.t0 = time.monotonic()
        self.show()
        apply_share_privacy(self)
        self.timer.start()

    def _step(self):
        if time.monotonic() - self.t0 > 4.0:
            self.timer.stop()
            self.hide()
            return
        for p in self.parts:
            p[3] += 0.45        # gravity
            p[2] *= 0.99        # air
            p[0] += p[2]
            p[1] += p[3]
            p[6] += p[7]
        self.update()

    def paintEvent(self, e):
        el = time.monotonic() - self.t0
        fade = max(0.0, min(1.0, (4.0 - el) / 1.0))
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        for x, y, _, _, col, size, rot, _ in self.parts:
            c = QColor(col)
            c.setAlphaF(fade)
            p.save()
            p.translate(x, y)
            p.rotate(rot)
            p.fillRect(QRectF(-size / 2, -size / 4, size, size / 2), c)
            p.restore()
        if self.lines:
            f = QFont()
            f.setPointSize(26)
            f.setBold(True)
            p.setFont(f)
            y = self.height() * 0.3
            for i, text in enumerate(self.lines):
                if i == 1:
                    f.setPointSize(14)
                    f.setBold(False)
                    p.setFont(f)
                r = QRectF(0, y, self.width(), 60)
                shadow = QColor(0, 0, 0, int(160 * fade))
                p.setPen(shadow)
                p.drawText(r.translated(2, 2), Qt.AlignHCenter | Qt.AlignTop, text)
                col = QColor("#f3e3c3")
                col.setAlphaF(fade)
                p.setPen(col)
                p.drawText(r, Qt.AlignHCenter | Qt.AlignTop, text)
                y += 52 if i == 0 else 30


# ---------------------------------------------------------------- boosts and check-ins
# said when a focus session starts. START_NUDGES help you begin (for people who put things off);
# FLOW_BOOSTS are for people who don't. The "procrastinator" setting picks the mix.
START_NUDGES = [
    "Be curious, not perfect.", "Just the first tiny step.", "What's interesting here?",
    "Small enough to start. Go.", "Explore, don't grind.", "Stuck? Make it smaller.",
    "Curiosity beats worry.", "One thing. Just this.", "Play with it for 5 minutes.",
    "Messy first draft allowed.", "You don't have to feel ready.", "Wonder first, judge later.",
    "Tiny step, then another.", "Poke at it. See what happens.", "Ask it a question.",
    "Done beats perfect today.", "Start ugly. Fix later.", "Get curious about the hard part.",
    "Open the file. That's the whole first step.", "Two minutes counts. Start the two minutes.",
    "Motivation shows up after you start, not before.", "Lower the bar until you can step over it.",
    "You're not writing it. You're just sketching it.", "Bad version first. Good version is a sequel.",
    "Pick the easiest corner of the hard thing.", "Nobody's grading this draft.",
]
FLOW_BOOSTS = [
    "Deep work mode. See you at the break.", "Phone face down, brain face up.", "One thing, all the way in.",
    "Clock's running. Thoughts go in the lot.", "Go get it.", "The lot is open for stray thoughts.",
    "Heads down. The circle has your back.", "Quiet mode on. Park anything that knocks.",
    "Make this block count.", "Clear runway. Take off.", "You know the plan. Run it.",
    "Stray thought? Park it, don't chase it.", "Single-tasking like it's a sport.",
    "The world can wait a few minutes.", "Let's make future you smug.", "Focus on. Tabs off.",
]
FOCUS_BOOSTS = START_NUDGES + FLOW_BOOSTS   # kept for anything that still wants the whole pool
# said when you start another focus round soon after the last one ({n} = rounds today, counting this one)
STREAK_BOOSTS = [
    "Round {n}. You're on a roll.", "Round {n}. At this point it's a habit.", "{n} rounds today. Machine mode.",
    "Back again? Round {n}. Love to see it.", "Round {n}. Your focus is showing off now.",
    "Round {n}. The distractions have filed a complaint.", "Round {n}. Consistency is the cheat code.",
    "{n} rounds in. Your to-do list is getting scared.", "Round {n}. Momentum is a real thing and you have it.",
    "Round {n}. Keep stacking these.", "Round {n}. You're killing it. Politely.",
    "Round {n}. Somebody's in the zone.",
]
# a one or two word pop on the circle when a quick note is saved
SAVED_WORDS = ["Saved!", "Gotcha!", "Parked.", "Noted!", "Caught it.", "Got it!", "In the lot.", "Filed!",
               "Safe here.", "Done. Go.", "Stashed!", "Kept."]

_RECENT = {}


def pick_fresh(items, key):
    """random.choice that avoids repeating the last several picks from the same pool."""
    items = list(items)
    if not items:
        return None
    seen = _RECENT.setdefault(key, [])
    fresh = [x for x in items if x not in seen] or items
    x = random.choice(fresh)
    seen.append(x)
    del seen[:-max(1, len(items) // 2)]
    return x


def focus_rounds_today(gap_min=45):
    """(rounds of focus today, whether the last one ended within gap_min minutes): for streak lines."""
    rows = [r for r in read_jsonl(FOCUS_LOG) if r.get("kind", "focus") == "focus" and r.get("focused_min", 0) >= 1]
    today = datetime.now().date().isoformat()
    rows = [r for r in rows if str(r.get("end", "")).startswith(today)]
    if not rows:
        return 0, False
    try:
        last = max(datetime.fromisoformat(r["end"]) for r in rows)
    except Exception:
        return len(rows), False
    return len(rows), (datetime.now() - last).total_seconds() <= gap_min * 60


def boost_line(procrastinator="sometimes"):
    """The line said when a focus session starts."""
    n, recent = focus_rounds_today()
    if recent and n >= 1:
        return pick_fresh(STREAK_BOOSTS, "streak").format(n=n + 1)
    pool = {"yes": START_NUDGES, "no": FLOW_BOOSTS}.get(procrastinator, START_NUDGES + FLOW_BOOSTS)
    return pick_fresh(pool, "boost")


# (emoji, animation, text). Animations: shake (nervous, tilted vibrating head), bounce, wiggle, float, tilt.
CHECKINS = [
    ("\U0001F440", "tilt", "Hey. Still doing the thing you meant to do?"),
    ("\U0001F914", "tilt", "Quick check: scrolling, or choosing?"),
    ("\U0001F6CB\uFE0F", "float", "Is this rest or avoidance? Both are allowed. Just notice which."),
    ("\U0001F9E9", "wiggle", "Stuck? What's the smallest next step? Now make it smaller."),
    ("\U0001F300", "wiggle", "Worry loop? Try getting curious about it instead of fighting it."),
    ("\u2728", "float", "What would make the next 10 minutes a little more interesting?"),
    ("\U0001F4A7", "bounce", "You've been on for a while. Water? Window? Stretch?"),
    ("\U0001FAB4", "float", "Feeling tense? Name it, then touch one real thing near you."),
    ("\U0001F4F1", "shake", "Doom-scroll check. Put it down for one slow breath."),
    ("\U0001F52A", "wiggle", "Too big to start? Slice it until it's almost silly."),
    ("\U0001F50D", "tilt", "Curious question: what's the interesting part of the thing you're avoiding?"),
    ("\U0001F9D8", "float", "Checking on you. Shoulders up by your ears?"),
    ("\U0001F5C2\uFE0F", "wiggle", "Lots of tabs, few things finished? Pick one."),
    ("\U0001F9ED", "tilt", "Is this the plan, or did the plan wander off?"),
    ("\U0001F44B", "wiggle", "Hi, it's your circle. Want to start a small focus round?"),
    ("\U0001F343", "float", "If your mind is spiralling, a 5 minute break is a real option."),
    ("\U0001F439", "shake", "Your to-do list is getting nervous. Want to show it who's boss?"),
    ("\U0001F422", "float", "Slow start is still a start. One tiny round?"),
    ("\U0001F9C3", "bounce", "Hydration check. Your brain is mostly water and open tabs."),
    ("\U0001F643", "tilt", "Scrolling feels like rest but rarely is. Want a real 5 minute one?"),
    ("\U0001F440", "shake", "Hmm. Is this the thing, or a thing next to the thing?"),
    ("\U0001F95C", "bounce", "Low battery? A snack and a stretch count as productivity."),
    ("\U0001F6AA", "wiggle", "The hard task is behind a door. Just open it and look. No need to walk in yet."),
    ("\U0001F9ED", "float", "Quick compass check: is this where you meant to be?"),
    ("\U0001F4A1", "bounce", "Got an idea brewing? Park it, then pick one thing."),
    ("\U0001F3AF", "tilt", "What's the one thing that would make today feel done?"),
    ("\U0001F9F9", "wiggle", "Busy work or real work? No judgment, just asking."),
    ("\U0001F440", "float", "Eyes tired? Look at something far away for 20 seconds."),
    ("\U0001F4AC", "tilt", "Been chatting a while? Totally fine. Just checking it's on purpose."),
    ("\U0001F97A", "wiggle", "The task you're avoiding asked about you. It misses you."),
    ("\U0001F570\uFE0F", "float", "Time check. Where did the last half hour go?"),
    ("\U0001F6B6", "bounce", "Legs asleep? A 2 minute walk resets more than you'd think."),
    ("\U0001F9E0", "tilt", "Your brain has been busy. Want to give it one clear job?"),
    ("\U0001F32C\uFE0F", "float", "One slow breath out. Longer than the breath in. Okay, carry on."),
    ("\U0001F4CC", "bounce", "Anything rattling around up there? Park it and get it off your mind."),
    ("\U0001F9ED", "tilt", "Another task took priority? You can choose when to return to the plan."),
]
FIRST_CHECKINS = [
    ("\U0001F44B", "wiggle", "Quick check: is this what you meant to be doing?"),
    ("\U0001F3AF", "tilt", "Want to focus for a few minutes, or keep doing this?"),
    ("\U0001F552", "float", "You've been at the computer a while. How would you like to use the next bit?"),
    ("\U0001F4AD", "bounce", "A thought pulling you away? Park it here and return when you're ready."),
]
BOOST_FACES = ["\U0001F680", "\U0001F50D", "\U0001F331", "\U0001F3AF", "\U0001F9EA", "\u270F\uFE0F", "\U0001F4AA", "\u26A1"]


def idle_seconds():
    """Seconds since the last keyboard/mouse input (Windows); 0 elsewhere."""
    if not IS_WIN:
        return 0.0
    try:
        import ctypes
        from ctypes import wintypes

        class LASTINPUTINFO(ctypes.Structure):
            _fields_ = [("cbSize", wintypes.UINT), ("dwTime", wintypes.DWORD)]
        li = LASTINPUTINFO()
        li.cbSize = ctypes.sizeof(LASTINPUTINFO)
        if ctypes.windll.user32.GetLastInputInfo(ctypes.byref(li)):
            return max(0.0, (ctypes.windll.kernel32.GetTickCount() - li.dwTime) / 1000.0)
    except Exception:
        pass
    return 0.0


def mic_or_camera_in_use():
    """True while any app is using the microphone or camera (a call or meeting, most likely).
    Reads Windows' privacy 'last used' records: LastUsedTimeStop == 0 means still in use."""
    if not IS_WIN:
        return False
    try:
        import winreg
    except Exception:
        return False
    base = r"Software\Microsoft\Windows\CurrentVersion\CapabilityAccessManager\ConsentStore"
    for cap in ("microphone", "webcam"):
        for sub in ("", "\\NonPackaged"):
            try:
                key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, base + "\\" + cap + sub)
            except OSError:
                continue
            i = 0
            while True:
                try:
                    name = winreg.EnumKey(key, i)
                except OSError:
                    break
                i += 1
                if name == "NonPackaged":
                    continue
                try:
                    with winreg.OpenKey(key, name) as app_key:
                        start, _ = winreg.QueryValueEx(app_key, "LastUsedTimeStart")
                        stop, _ = winreg.QueryValueEx(app_key, "LastUsedTimeStop")
                        if start and stop == 0:
                            return name.replace("#", "\\").split("\\")[-1].split("_")[0] or "an app"
                except OSError:
                    continue
    return False


def windows_notification_is_quiet(state):
    # QUNS_BUSY (4) is broad enough to suppress check-ins during ordinary activity.
    return state in (1, 2, 3, 6, 7)


def windows_says_quiet():
    """True for explicit Windows quiet states; full screen is handled by PresenceGuard."""
    if not IS_WIN:
        return False
    try:
        import ctypes
        v = ctypes.c_int(0)
        if ctypes.windll.shell32.SHQueryUserNotificationState(ctypes.byref(v)) == 0:
            return windows_notification_is_quiet(v.value)
    except Exception:
        pass
    return False


class EmojiFace(QWidget):
    """A big emoji that moves a little, so the circle feels alive: shake (a nervous, tilted, vibrating head),
    bounce, wiggle, float, tilt. It pops in, plays for a few seconds, then rests (shake and float keep going
    gently while it's on screen)."""

    def __init__(self, px=30):
        super().__init__()
        self.px = px
        self.setFixedSize(int(px * 1.6), int(px * 1.6))
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.emoji, self.anim = "", "bounce"
        self._t0 = time.monotonic()
        self.tick = QTimer(self)
        self.tick.setInterval(33)
        self.tick.timeout.connect(self._step)

    def set(self, emoji, anim="bounce"):
        self.emoji, self.anim = emoji or "", anim or "bounce"
        if not emoji:
            self.hide()
        elif self.parentWidget() is not None:   # a parentless widget would pop up as its own window
            self.show()
        self._t0 = time.monotonic()
        if emoji:
            self.tick.start()
        self.update()

    def _step(self):
        t = time.monotonic() - self._t0
        if not self.isVisible() or (t > 3.0 and self.anim not in ("shake", "float")):
            self.tick.stop()
        self.update()

    def hideEvent(self, e):
        self.tick.stop()
        super().hideEvent(e)

    def paintEvent(self, e):
        if not self.emoji:
            return
        t = time.monotonic() - self._t0
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        pop = 1.0 if t > 0.35 else 0.45 + 0.55 * math.sin(t / 0.35 * math.pi / 2) * 1.08   # pop in
        dx = dy = rot = 0.0
        decay = max(0.0, 1.0 - t / 3.0)
        if self.anim == "shake":            # nervous: head tilted, vibrating in short bursts
            burst = 1.0 if (t % 2.2) < 0.9 else 0.15
            rot = -12 + 5 * math.sin(t * 55) * burst
            dx = 1.4 * math.sin(t * 70) * burst
        elif self.anim == "bounce":
            dy = -7 * abs(math.sin(t * 6.5)) * decay
        elif self.anim == "wiggle":
            rot = 16 * math.sin(t * 10) * decay
        elif self.anim == "float":
            dy = 2.5 * math.sin(t * 2.6)
            rot = 3 * math.sin(t * 1.7)
        elif self.anim == "tilt":           # curious head tilt, then a small nod
            rot = -16 * min(1.0, t * 3) + 4 * math.sin(t * 5) * decay
        c = self.width() / 2
        p.translate(c + dx, c + dy)
        p.rotate(rot)
        p.scale(pop, pop)
        f = QFont()
        f.setFamilies(["Segoe UI Emoji", "Apple Color Emoji", "Noto Color Emoji", "Segoe UI Symbol"])
        f.setPixelSize(self.px)
        p.setFont(f)
        p.setPen(QColor(C["text"]))    # colour emoji ignore this; a black-and-white fallback would be invisible in black
        p.drawText(QRectF(-c, -c, 2 * c, 2 * c), Qt.AlignCenter, self.emoji)


class SpeechBubble(QWidget):
    """A small speech bubble that pops out of the circle, with optional buttons."""
    closed = Signal(str)   # the response ("timeout" if it faded away)

    def __init__(self):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setStyleSheet(STYLE + f"""
            QLabel#say {{ color: {C['text']}; font-size: 12px; }}
            QPushButton#chip {{ background: {C['surface']}; border: 1px solid {C['border']}; border-radius: 10px;
                padding: 5px 11px; font-size: 12px; min-height: 14px; }}
            QPushButton#chip:hover {{ background: {C['accent']}; border-color: {C['accent']}; }}
            QPushButton#chip:focus {{ border-color: {C['text']}; }}""")
        self.tail_right = True
        lay = QVBoxLayout(self)
        lay.setContentsMargins(14, 10, 22, 10)
        lay.setSpacing(8)
        self.label = QLabel()
        self.label.setObjectName("say")
        self.label.setTextFormat(Qt.PlainText)
        self.label.setWordWrap(True)
        self.label.setFixedWidth(230)
        self.face = EmojiFace(26)
        self.face.hide()
        top = QHBoxLayout()
        top.setSpacing(6)
        top.addWidget(self.face, 0, Qt.AlignTop)
        top.addWidget(self.label, 1)
        lay.addLayout(top)
        self.btn_row = QVBoxLayout()           # rows of chips, wrapped to fit
        self.btn_row.setSpacing(5)
        lay.addLayout(self.btn_row)
        self.minute_row = QWidget(self)
        minute_lay = QHBoxLayout(self.minute_row)
        minute_lay.setContentsMargins(0, 0, 0, 0)
        minute_lay.setSpacing(5)
        self.minute_edit = QLineEdit(self.minute_row)
        self.minute_edit.setPlaceholderText("Custom minutes")
        self.minute_edit.setAccessibleName("Custom timer minutes")
        self.minute_validator = QIntValidator(1, 600, self.minute_edit)
        self.minute_edit.setValidator(self.minute_validator)
        self.minute_edit.textChanged.connect(self._minute_text_changed)
        self.minute_edit.returnPressed.connect(self._submit_minutes)
        minute_lay.addWidget(self.minute_edit, 1)
        self.minute_start = QPushButton("Start", self.minute_row)
        self.minute_start.setObjectName("chip")
        self.minute_start.setEnabled(False)
        self.minute_start.clicked.connect(self._submit_minutes)
        minute_lay.addWidget(self.minute_start)
        lay.addWidget(self.minute_row)
        self.minute_row.hide()
        self._minute_prefix = None
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(lambda: None if self.underMouse() else self._finish("timeout"))
        self.anim = QVariantAnimation(self)
        self.anim.valueChanged.connect(lambda v: self.setWindowOpacity(float(v)))
        self._btns = []

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(1, 1, -9, -1) if self.tail_right else QRectF(self.rect()).adjusted(9, 1, -1, -1)
        path = QPainterPath()
        path.addRoundedRect(r, 12, 12)
        cy = min(r.bottom() - 14, max(r.top() + 14, self._tail_y))
        tail = QPainterPath()
        if self.tail_right:
            tail.moveTo(r.right() - 1, cy - 7)
            tail.lineTo(r.right() + 8, cy)
            tail.lineTo(r.right() - 1, cy + 7)
        else:
            tail.moveTo(r.left() + 1, cy - 7)
            tail.lineTo(r.left() - 8, cy)
            tail.lineTo(r.left() + 1, cy + 7)
        path = path.united(tail)
        p.setBrush(QColor(C["surface_hi"]))
        p.setPen(QPen(QColor(C["accent"]), 1.2))
        p.drawPath(path)

    def say(self, circle_rect, text, buttons=(), timeout_ms=7000, emoji=None, anim="bounce",
            minute_input=None):
        """buttons: [(label, response_key)]; clicking closes the bubble and emits closed(response_key).
        emoji: an optional animated face beside the text. minute_input: (response prefix, maximum minutes)."""
        self.timer.stop()
        self.face.set(emoji, anim)
        self._minute_prefix = minute_input[0] if minute_input else None
        self.minute_edit.clear()
        if minute_input:
            self.minute_validator.setTop(minute_input[1])
            self.minute_edit.setAccessibleName(f"Custom {minute_input[0]} minutes")
        self.minute_row.setVisible(bool(minute_input))
        for b in self._btns:
            b.setParent(None)
            b.deleteLater()
        self._btns = []
        self.label.setText(text)
        screen = screen_for(self, circle_rect.center())
        area = screen.availableGeometry()
        while self.btn_row.count():                     # old rows (and stretches) out
            it = self.btn_row.takeAt(0)
            if it.layout():
                it.layout().setParent(None)
        max_row = min(320, area.width() // 3)           # chips wrap instead of stretching past the screen
        row, row_w, widest = None, 0, 0
        for label, key in buttons:
            b = QPushButton(label, self)
            b.setObjectName("chip")
            b.setCursor(Qt.PointingHandCursor)
            b.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Fixed)    # a lone chip on a row stays chip-sized
            if len(self._btns) < 9:
                b.setToolTip(f"Key {len(self._btns) + 1}")
            b.clicked.connect(lambda _=False, k=key: self._finish(k))
            bw = b.sizeHint().width()
            if row is None or (row_w and row_w + 5 + bw > max_row):
                row = QHBoxLayout()
                row.setSpacing(5)
                row.setAlignment(Qt.AlignLeft)
                self.btn_row.addLayout(row)
                row_w = 0
            row.addWidget(b)
            row_w += (5 if row_w else 0) + bw
            widest = max(widest, row_w)
            self._btns.append(b)
        text_w = max(230, widest - (self.face.width() + 6 if emoji else 0))
        self.label.setFixedWidth(text_w)
        self.label.setMinimumHeight(self.label.heightForWidth(text_w))
        self.tail_right = circle_rect.center().x() > area.center().x()
        lay = self.layout()
        lay.setContentsMargins(14, 10, 22, 10) if self.tail_right else lay.setContentsMargins(22, 10, 14, 10)
        self.adjustSize()
        w, h = self.width(), self.height()
        x = circle_rect.left() - w - 2 if self.tail_right else circle_rect.right() + 2
        y = circle_rect.center().y() - h // 2
        x = max(area.left(), min(x, area.right() - w))
        y = max(area.top(), min(y, area.bottom() - h))
        self._tail_y = circle_rect.center().y() - y
        self.move(x, y)
        self.setWindowOpacity(0.0)
        self.show()
        apply_share_privacy(self)
        self.anim.stop()
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.setDuration(260)
        self.anim.start()
        self.timer.start(timeout_ms)

    def keyPressEvent(self, e):
        n = e.key() - Qt.Key_1
        if 0 <= n < min(9, len(self._btns)) and not self.minute_edit.hasFocus():
            self._btns[n].click()
        elif e.key() == Qt.Key_Escape:
            self._finish("dismiss")
        else:
            super().keyPressEvent(e)

    def take_keys(self):
        """The list hotkey lands here while a question shows: number keys pick, Esc closes."""
        self.timer.stop()
        force_foreground(self)
        (self._btns[0] if self._btns else self.minute_edit).setFocus()

    def _minute_text_changed(self):
        self.minute_start.setEnabled(self.minute_edit.hasAcceptableInput())

    def _submit_minutes(self):
        if self._minute_prefix and self.minute_edit.hasAcceptableInput():
            self._finish(f"{self._minute_prefix}_{self.minute_edit.text()}")

    def _finish(self, key):
        self.timer.stop()
        if self.isVisible():
            self.hide()
            self.closed.emit(key)


# ---------------------------------------------------------------- background noise
NOISE_KINDS = [("brown", "Brown noise", "Deep, soft rumble. The usual pick for ADHD focus"),
               ("pink", "Pink noise", "Balanced, like steady rain. Good all-rounder"),
               ("white", "White noise", "Bright hiss. Best at masking voices and chatter")]
NOISE_VOLUMES = [("low", "Low", 0.12), ("mid", "Medium", 0.25), ("high", "High", 0.45)]
NOISE_RATE = 22050
NOISE_LOOP_S = 12


def make_noise(kind, seconds=NOISE_LOOP_S, rate=NOISE_RATE, seed=7):
    """A seamless loop of noise as 16-bit mono PCM bytes. Pure Python (no numpy): made once, then looped."""
    import array
    rnd = random.Random(seed)
    n = int(seconds * rate)
    fade = rate // 2                     # half a second crossfade, so the loop point can't be heard
    total = n + fade
    out = [0.0] * total
    if kind == "brown":
        b = 0.0
        for i in range(total):
            b = (b + 0.02 * rnd.uniform(-1, 1)) / 1.02
            out[i] = b * 3.5
    elif kind == "pink":                 # Paul Kellet's filter
        b0 = b1 = b2 = b3 = b4 = b5 = b6 = 0.0
        for i in range(total):
            w = rnd.uniform(-1, 1)
            b0 = 0.99886 * b0 + w * 0.0555179
            b1 = 0.99332 * b1 + w * 0.0750759
            b2 = 0.96900 * b2 + w * 0.1538520
            b3 = 0.86650 * b3 + w * 0.3104856
            b4 = 0.55000 * b4 + w * 0.5329522
            b5 = -0.7616 * b5 - w * 0.0168980
            out[i] = (b0 + b1 + b2 + b3 + b4 + b5 + b6 + w * 0.5362) * 0.11
            b6 = w * 0.115926
    else:
        for i in range(total):
            out[i] = rnd.uniform(-1, 1) * 0.35      # about as loud as the other two
    for i in range(fade):                # blend the tail into the head
        k = i / fade
        out[i] = out[i] * k + out[n + i] * (1 - k)
    pcm = array.array("h", (max(-32767, min(32767, int(x * 32767))) for x in out[:n]))
    return pcm.tobytes()


class NoisePlayer(QObject):
    """Plays a looped noise through the default speakers with Qt's own audio module (part of PySide6, so no new
    dependency). If audio isn't available, it just stays quiet."""

    def __init__(self):
        super().__init__()
        self.sink = self.dev = None
        self.kind = None
        self._cache = {}

    @property
    def playing(self):
        return self.sink is not None

    def play(self, kind="brown", volume=0.25):
        self.stop()
        try:
            from PySide6.QtCore import QBuffer, QByteArray, QIODevice
            from PySide6.QtMultimedia import QAudioFormat, QAudioSink, QMediaDevices

            class Loop(QIODevice):
                def __init__(self, data):
                    super().__init__()
                    self.data, self.pos = data, 0

                def readData(self, maxlen):
                    out = bytearray()
                    while len(out) < maxlen:
                        chunk = self.data[self.pos:self.pos + (maxlen - len(out))]
                        out += chunk
                        self.pos = (self.pos + len(chunk)) % len(self.data)
                    return bytes(out)

                def writeData(self, data):
                    return 0

                def bytesAvailable(self):
                    return 1 << 20

                def isSequential(self):
                    return True

            if kind not in self._cache:
                self._cache[kind] = make_noise(kind)
            fmt = QAudioFormat()
            fmt.setSampleRate(NOISE_RATE)
            fmt.setChannelCount(1)
            fmt.setSampleFormat(QAudioFormat.Int16)
            out = QMediaDevices.defaultAudioOutput()
            if out.isNull():
                return False
            self.dev = Loop(self._cache[kind])
            self.dev.open(QIODevice.ReadOnly)
            self.sink = QAudioSink(out, fmt, self)
            self.sink.setVolume(float(volume))
            self.sink.start(self.dev)
            self.kind = kind
            return True
        except Exception as e:
            log_error(f"noise: {e}")
            self.stop()
            return False

    def set_volume(self, v):
        if self.sink:
            self.sink.setVolume(float(v))

    def stop(self):
        if self.sink:
            try:
                self.sink.stop()
            except Exception:
                pass
            self.sink.deleteLater()
        if self.dev:
            self.dev.close()
        self.sink = self.dev = None
        self.kind = None


class MusicPlayer:
    """Plays one song from MUSIC_DIR on repeat with Qt's own media player (part of PySide6, no new dependency)."""
    EXTS = {".mp3", ".m4a", ".aac", ".wav", ".flac", ".ogg", ".opus", ".wma"}

    def __init__(self):
        self.player = self.out = None
        self.track = None

    def tracks(self):
        try:
            return sorted((f for f in MUSIC_DIR.iterdir() if f.suffix.lower() in self.EXTS), key=lambda f: f.name.lower())
        except OSError:
            return []

    def play(self, path):
        try:
            if self.player is None:
                from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
                self.player, self.out = QMediaPlayer(), QAudioOutput()
                self.player.setAudioOutput(self.out)
                self.player.setLoops(QMediaPlayer.Loops.Infinite)
            self.player.setSource(QUrl.fromLocalFile(str(path)))
            self.player.play()
            self.track = Path(path)
            return True
        except Exception as e:
            log_error(f"music: {e}")
            self.track = None
            return False

    def stop(self):
        if self.player:
            self.player.stop()
        self.track = None


# ---------------------------------------------------------------- what's playing (Windows media session)
MEDIA_PS = r"""
Add-Type -AssemblyName System.Runtime.WindowsRuntime
$as = ([System.WindowsRuntimeSystemExtensions].GetMethods() | ? { $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' })[0]
[Windows.Media.Control.GlobalSystemMediaTransportControlsSessionManager,Windows.Media.Control,ContentType=WindowsRuntime] | Out-Null
$t = $as.MakeGenericMethod([Windows.Media.Control.GlobalSystemMediaTransportControlsSessionManager]).Invoke($null, @([Windows.Media.Control.GlobalSystemMediaTransportControlsSessionManager]::RequestAsync()))
$t.Wait(3000) | Out-Null
$s = $t.Result.GetCurrentSession()
if ($s) { "$($s.SourceAppUserModelId)|$($s.GetPlaybackInfo().PlaybackStatus)" } else { "|none" }
"""
MEDIA_STATE = {}          # {"app": "Spotify.exe", "playing": True, "at": time.time()} while the watcher is on


def media_now():
    """What the watcher last saw, if it's fresh (under 2 minutes old). Only the app and whether it's playing:
    never the song title."""
    st = MEDIA_STATE
    if not st or time.time() - st.get("at", 0) > 120:
        return None
    return {"playing": st["playing"], "app": st["app"]}


class MediaWatch(QObject):
    """Every minute (when the setting is on), asks Windows what media session is current and whether it's
    playing, using the built-in PowerShell and Windows' own media API (the same one behind the volume flyout).
    Nothing leaves the computer. Each new thought gets {playing, app} in the thought log."""

    def __init__(self, store):
        super().__init__()
        self.store = store
        self.proc = None
        self.t = QTimer(self)
        self.t.setInterval(60000)
        self.t.timeout.connect(self.poll)
        self.apply()

    def apply(self):
        on = IS_WIN and self.store.settings.get("music_log", False)
        if on and not self.t.isActive():
            self.t.start()
            QTimer.singleShot(1000, self.poll)
        elif not on:
            self.t.stop()
            MEDIA_STATE.clear()

    def poll(self):
        if self.proc is not None:
            return
        self.proc = QProcess(self)
        self.proc.finished.connect(self._done)
        self.proc.start("powershell", ["-NoProfile", "-NonInteractive", "-WindowStyle", "Hidden",
                                       "-Command", MEDIA_PS])

    @staticmethod
    def parse(text):
        line = (text or "").strip().splitlines()[-1:] or [""]
        app, _, status = line[0].partition("|")
        app = app.split("!")[0].split("_")[0] if "!" in app else app
        return {"app": app, "playing": status.strip() == "Playing", "at": time.time()}

    def _done(self, *_):
        try:
            out = bytes(self.proc.readAllStandardOutput()).decode("utf-8", "ignore")
            MEDIA_STATE.update(self.parse(out))
        except Exception as e:
            log_error(f"media watch: {e}")
        self.proc.deleteLater()
        self.proc = None


PEEKS = {"water": (["\U0001F4A7", "\U0001F964", "\U0001F9CA", "\U0001F6B0", "\U0001F375", "\U0001F433", "\U0001F335"],
                   ["Sip of water?", "Water break?", "Hydrate?", "Drink some water", "Thirsty brain?",
                    "One sip. Go.", "Bottle check", "Water, then back", "Brain wants water", "Tiny sip?",
                    "Refill time?", "Stay watered, plant"]),
         "eyes": (["\U0001F440", "\U0001F989", "\U0001F52D", "\U0001F333", "\U0001FA9F", "\U0001F60C", "\U0001F426"],
                  ["Look far away, 20 s", "Rest your eyes", "Eyes off screen", "Look out the window",
                   "Blink a few times", "Find something far", "20 s of distance", "Unfocus for a bit",
                   "Eyes: tiny break", "Look at a tree?", "Soft gaze, 20 s", "Screen can wait 20 s"])}


def focus_peek_step(clock, state, remaining, settings, can_show, now=None, idle=0.0):
    """Count focus across rounds (or, with peek_when "always", any active screen time outside breaks);
    leave quiet-time cues pending until they can be shown."""
    now = time.time() if now is None else now
    focusing = bool(state) and state.get("kind") == "focus" and state.get("paused_left") is None
    always = settings.get("peek_when", "focus") == "always"
    last, clock["tick_at"] = float(clock.get("tick_at", now)), now
    if not focusing and not always:
        return None
    gain = 0.0
    if focusing:
        session = state.get("started")
        if clock.get("session") != session:
            clock["session"], clock["session_elapsed"] = session, 0.0
        elapsed = max(0.0, float(state["minutes"]) * 60 - max(0.0, remaining))
        previous = max(0.0, float(clock.get("session_elapsed", 0)))
        gain = max(0.0, elapsed - previous)
        clock["session_elapsed"] = elapsed
    if always:                          # time at the keyboard; away (60 s idle) and breaks don't count
        on_break = bool(state) and state.get("kind") == "break"
        gain = 0.0 if on_break or idle >= 60 else max(0.0, min(60.0, now - last))
    clock["seconds"] = max(0.0, float(clock.get("seconds", 0))) + gain
    shown = clock.setdefault("shown", {})
    if not isinstance(shown, dict):
        shown = clock["shown"] = {}
    for kind, key, every in (("eyes", "peek_eyes", 20), ("water", "peek_water", 40)):
        due = int(clock["seconds"] // (every * 60))
        already = max(0, int(shown.get(kind, 0)))
        if not settings.get(key, True):
            shown[kind] = due
            continue
        if (due > already and (remaining > 60 or not focusing) and
                now - float(clock.get("last_shown_at", 0)) >= 90 and can_show()):
            shown[kind] = due
            clock["last_shown_at"] = now
            return kind
    return None


def peek_scale(width_mm, width_px):
    """How big and far a peek moves. About 1 on a 14 to 16 inch laptop, up to 1.8 on a 32 inch or ultrawide
    monitor, where a small cue at the far edge goes unseen. Uses the screen's physical width when Windows
    knows it, else its width in pixels."""
    size = width_mm / 400 if width_mm > 100 else width_px / 1600
    return max(1.0, min(1.8, size))


EYE_REST_S = 20       # the 20-20-20 rule (American Academy of Ophthalmology): every 20 min, 20 ft away, 20 s
PEEK_SOUND_LEAD_MS = 350


class PeekBuddy(QWidget):
    """A tiny character that peeks out from behind the circle (water, eyes), says two words, and ducks back.
    A soft tone plays just before it. The eye peek stays out with a 20 s look-away countdown beside it.
    On big screens it is larger, travels farther and bounces twice. Clicks pass through; never takes focus."""

    def __init__(self, bubble, settings=None):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.bubble = bubble
        self.settings = settings if settings is not None else {}
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        self.face = EmojiFace(22)
        self.face.setParent(self)
        lay.addWidget(self.face)
        self.adjustSize()
        self.tip = HintBubble()
        self.left = 0
        self.count = QTimer(self)
        self.count.setInterval(1000)
        self.count.timeout.connect(self._count_step)
        self.anim = QVariantAnimation(self)
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.setDuration(5200)
        self.anim.valueChanged.connect(self._step)
        self.anim.finished.connect(self._done)

    def peek(self, kind):
        if self.settings.get("peek_sound", True):
            threading.Thread(target=play_reminder_tone, args=("peek",), daemon=True).start()
            QTimer.singleShot(PEEK_SOUND_LEAD_MS, lambda: self._show(kind))   # hear it, then see it
        else:
            self._show(kind)

    def _show(self, kind):
        faces, words = PEEKS[kind]
        emoji = pick_fresh(faces, "peekface_" + kind)
        g = self.bubble.geometry()
        screen = screen_for(self, g.center())
        area = screen.availableGeometry()
        self.scale = peek_scale(screen.physicalSize().width(), area.width())
        self.face.px = round(22 * self.scale)
        self.face.setFixedSize(int(self.face.px * 1.6), int(self.face.px * 1.6))
        self.resize(self.face.size())
        self._dir = -1 if g.center().x() > area.center().x() else 1     # peek toward the middle of the screen
        self._home = QPoint(g.center().x() - self.width() // 2, g.center().y() - self.height() // 2)
        self._out = self._home + QPoint(self._dir * round((g.width() // 2 + 6) * self.scale), -g.height() // 4)
        guide = kind == "eyes" and self.settings.get("eye_guide", False)
        self.face.set(emoji, "bounce" if self.scale >= 1.3 else random.choice(["wiggle", "bounce", "tilt"]))
        self.count.stop()
        self.tip.hide()
        self.anim.stop()
        self.anim.setDuration((EYE_REST_S + 3) * 1000 if guide else 5200)
        self._step(0.0)
        self.show()
        apply_share_privacy(self)
        self.bubble.raise_()                    # it comes out from behind the circle
        self.bubble.hop()
        self.anim.start()
        if self.scale >= 1.3:                   # a second bounce where one is easy to miss
            QTimer.singleShot(1500, lambda: self.isVisible() and (self.face.set(self.face.emoji, "bounce"),
                                                                  self.bubble.hop()))
        if guide:
            self.left = EYE_REST_S
            QTimer.singleShot(700, self._count_step)
        else:
            QTimer.singleShot(700, lambda: self.bubble.pop_word(pick_fresh(words, "peek_" + kind), 3200))

    def _count_step(self):
        if not self.isVisible():
            self.count.stop()
            return
        if self.left > 0:          # ponytail: one still line, no per-second ticking (it pulled the eye back)
            self.tip.setText(f"Look at something 20 ft (6 m) away for {EYE_REST_S} s")
            self.left = 0
            self.count.start(EYE_REST_S * 1000)
        else:
            self.count.stop()
            self.tip.setText("Done. Welcome back.")
        area = screen_for(self.tip, self._out).availableGeometry()
        x = self._out.x() + (self.width() + 4 if self._dir > 0 else -self.tip.width() - 4)
        y = self._out.y() + (self.height() - self.tip.height()) // 2
        self.tip.move(max(area.left(), min(x, area.right() - self.tip.width())),
                      max(area.top(), min(y, area.bottom() - self.tip.height())))
        if not self.tip.isVisible():
            self.tip.show()
            apply_share_privacy(self.tip)

    def _done(self):
        self.count.stop()
        self.tip.hide()
        self.hide()

    def _step(self, v):
        ms = float(v) * self.anim.duration()
        left = self.anim.duration() - ms
        k = min(1.0, ms / 600) if ms < 600 else (1.0 if left > 700 else max(0.0, left / 700))
        k = 1 - (1 - k) ** 3                    # ease out
        self.move(self._home + (self._out - self._home) * k)


# back from being away mid-focus ({m} = minutes). The circle only knows the keyboard and mouse went quiet.
AWAY_LINES = [
    ("\u23F8\uFE0F", "No keyboard or mouse for {m} min during this round. Keep that time in it?"),
]
# the moment a break ends: short, a little cheeky, never guilt
BREAK_END_LINES = [
    ("\u23F0", "Break's up. Your work missed you. A little."),
    ("\U0001F514", "Ding. Recess is over."),
    ("\U0001F680", "Recharged? Let's go."),
    ("\U0001F9C3", "Break done. Refill the water, then round two?"),
    ("\U0001F3AC", "Intermission's over. Back to the main feature."),
    ("\U0001F43E", "Paws off the phone. Break's done."),
    ("\U0001F9E0", "Brain's rested. Time to use it."),
    ("\U0001F6CB\uFE0F", "The couch says stay. The circle says go."),
    ("\U0001F3C1", "Pit stop over. Back on track?"),
    ("\U0001F31F", "Fresh eyes, fresh start. Ready?"),
    ("\U0001F44B", "Welcome back. Or at least, you should be."),
    ("\U0001F4AA", "Break: done. You: ready. Probably."),
    ("\U0001F375", "Last sip. Then back to it."),
    ("\U0001F3AF", "Break's over. One small thing first?"),
]
# a break that got extended is over ({parts} = "5 + 5", {total} = 10)
EXTENDED_BREAK_LINES = [
    ("\U0001F9EE", "{parts} min of break. That's {total}. Now what?"),
    ("\U0001F6CB\uFE0F", "Break, then bonus break: {parts} = {total} min. The couch is winning. Your move."),
    ("\U0001F440", "{parts}. I did the math: {total} min. Round two of work?"),
    ("\U0001F570\uFE0F", "{parts} = {total} min across {n} breaks. Impressive stamina. Back to it?"),
    ("\U0001F36A", "\"Just a few more\" became {parts} = {total} min. Happens. One small step now?"),
    ("\U0001F422", "{parts} = {total} min. Slow and steady, but mostly steady. Ready?"),
    ("\U0001F3AC", "Break, then the sequel: {parts} = {total} min. Now the main feature?"),
    ("\U0001F9D8", "{parts} = {total} min recharged. You should be at 110%. Prove it?"),
    ("\U0001F4E3", "Encore over. {parts} = {total} min. Take a bow, then back to work?"),
    ("\U0001F9ED", "{parts} = {total} min off the map. Want back on it?"),
    ("\U0001F95C", "{parts} = {total} min. Snack break has become a lifestyle. Tiny round?"),
    ("\U0001F44B", "Still counting: {parts} = {total} min. What's next?"),
]
# the break is over and you're not back yet ({m} = minutes since it ended)
OVERRUN_LINES = [
    ("\u23F0", "Break ended {m} min ago. Your work is starting to wonder where you went."),
    ("\U0001F440", "Psst. The break's been over for {m} min. One tiny round?"),
    ("\U0001F6CB\uFE0F", "That break is now {m} min into overtime. The couch is very persuasive, I know."),
    ("\U0001F4E3", "Friendly reminder: break's over, {m} min ago. Ready when you are."),
    ("\U0001F422", "{m} min past the break. Slow start is still a start. Want 10 minutes?"),
    ("\U0001F9ED", "The plan said back {m} min ago. Want to rejoin it?"),
    ("\U0001F343", "Break ran {m} min long. No guilt. Just a nudge back."),
    ("\U0001F3AC", "Intermission ended {m} min ago. The second half is waiting."),
    ("\U0001F4F1", "{m} min over. If it's a scroll hole, this is your rope."),
    ("\U0001F44B", "Still there? Break's been done for {m} min. I'll keep your seat warm."),
    ("\U0001F9E0", "Your brain's rested for {m} bonus minutes. Put it to work?"),
    ("\U0001F36A", "{m} min of extra break. Treat's over. Back to it?"),
]


class NudgeManager(QObject):
    """Friendly check-ins while you're at the computer but not in a focus session, and a boost line when
    a focus session starts. Stays quiet: when turned off or paused, during any timer, in full screen,
    while the mic or camera is in use (calls/meetings), and when Windows reports presenting/quiet time."""
    wants_focus = Signal(float)
    wants_break = Signal(float)
    wants_more_break = Signal(float)          # "a few more min": start a break of this many minutes

    def __init__(self, store, timer, bubble, speech, guard_fn, calendar=None):
        super().__init__()
        self.store, self.timer, self.bubble, self.speech = store, timer, bubble, speech
        self.calendar = calendar
        self.guard_fn = guard_fn           # -> PresenceGuard or None
        self.active_s = 0.0
        self._last_tick = time.monotonic()
        saved = store.settings.get("nudge_active")        # screen time counted before a restart (loading updates)
        if isinstance(saved, list) and len(saved) == 2 and time.time() - saved[1] < 600:
            self.active_s = float(saved[0])
        self._asked = None
        self._focus_event_span = None
        self.speech.closed.connect(self._answered)
        self.tick = QTimer(self)
        self.tick.setInterval(30000)
        self.tick.timeout.connect(self._tick)
        self.tick.start()

    # settings
    def _st(self, k, d):
        return self.store.settings.get(k, d)

    def enabled(self):
        return self._st("nudge_on", True) and time.time() >= self._st("nudge_paused_until", 0)

    def quiet_reason(self):
        g = self.guard_fn()
        if g is not None and g.hidden_for_fs:
            return "full screen"
        if not self.bubble.isVisible():
            return "circle hidden"
        if self.calendar and self._st("nudge_calendar_on", True):
            now = datetime.now().astimezone()
            if any(e["start"] <= now < e["end"] for e in self.calendar.events):
                return "calendar event in progress"
        who = mic_or_camera_in_use()
        if who:
            return f"mic or camera in use ({who})" if isinstance(who, str) else "mic or camera in use"
        if windows_says_quiet():
            return "Windows quiet/presenting"
        return None

    def _tick(self):
        now = time.monotonic()
        elapsed = max(0.0, min(60.0, now - self._last_tick))
        self._last_tick = now
        if self.timer.running or self.timer.overrun_since or not self.enabled():
            self.active_s = 0.0
            self.store.settings["nudge_active"] = [0, time.time()]
            return
        idle = idle_seconds()
        if idle > 600:            # away time does not count, but prior screen time still does
            self.store.settings["nudge_active"] = [round(self.active_s), time.time()]
            return
        if idle < 120:            # only count time you're actually using the computer
            self.active_s += elapsed
        self.store.settings["nudge_active"] = [round(self.active_s), time.time()]   # saved with the next save
        if self.active_s >= float(self._st("nudge_every_min", 45)) * 60 and not self.quiet_reason():
            self.check_in()

    def status(self):
        """One line on what check-ins are doing right now (Settings and the circle's menu show it)."""
        if not self._st("nudge_on", True):
            return "Check-ins are off"
        until = self._st("nudge_paused_until", 0)
        if until > time.time():
            return "Check-in messages paused " + self.paused_text(until)
        if self.timer.running:
            return "Quiet during a timer"
        if self.timer.overrun_since:
            return "Break's over: break reminders instead"
        q = self.quiet_reason()
        if q:
            return f"Quiet now: {q}"
        left = max(0, float(self._st("nudge_every_min", 45)) * 60 - self.active_s)
        return f"Next check-in after about {max(1, round(left / 60))} more min of screen time"

    def check_in(self, preview=False):
        self._active_min = max(1, int(round(self.active_s / 60))) if not preview else 0
        self._focus_event_span = None
        if not preview:
            self.active_s = 0.0
        count = max(0, int(self._st("checkin_count", 0)))
        pool = FIRST_CHECKINS if count < len(FIRST_CHECKINS) else CHECKINS
        face, anim, msg = pick_fresh(pool, "checkin_first" if pool is FIRST_CHECKINS else "checkin")
        work = self._checkin_work(preview)
        calendar_event = self._checkin_calendar(preview) if not work else None
        if work:
            due = work_due(work)
            title = work.get("title", "").strip()
            if len(title) > 54:
                title = title[:51].rstrip() + "..."
            now = datetime.now()
            timing = (f"Due in {short_span(due.timestamp() - now.timestamp())}"
                      if due.timestamp() >= now.timestamp() else work_time_left(due, now))
            msg = f"You marked {title} as important. {timing}. Want a focus round?"
            face, anim = "\U0001F3AF", "tilt"
        elif calendar_event:
            title = calendar_event["title"].strip()
            if len(title) > 54:
                title = title[:51].rstrip() + "..."
            span = short_span((calendar_event["start"] - datetime.now().astimezone()).total_seconds())
            msg = f"{title} starts in {span}. Want a focus round before then?"
            self._focus_event_span = span
            face, anim = "\U0001F4C5", "tilt"
        if not preview:
            self.store.settings["checkin_count"] = count + 1
            if work:
                self.store.settings["nudge_work_last"] = [work.get("id"), time.time()]
            if calendar_event:
                self.store.settings["nudge_calendar_last"] = [self._calendar_key(calendar_event), time.time()]
            self.store.save()
        # The popup may show an event title, but the focus log and AI export never retain it.
        self._asked = None if preview else ("A calendar event is coming up. Want a focus round?"
                                            if calendar_event else msg)
        self.bubble.hop()
        self._checkin_view = (msg, face, anim)
        self.speech.say(self.bubble.geometry(), msg, emoji=face, anim=anim, buttons=
                         [("Start focus", "focus"), ("Take a break", "break"), ("Forgot the timer", "working"),
                          ("More", "checkin_more")], timeout_ms=30000)

    def more_choices(self, asked):
        """The rarer check-in answers, one tap away so the first view stays short."""
        msg, face, anim = getattr(self, "_checkin_view", ("What's happening?", None, "bounce"))
        self._asked = asked
        self.bubble.hop()
        self.speech.say(self.bubble.geometry(), msg, emoji=face, anim=anim, buttons=
                         [("Urgent task came up", "urgent_detour"), ("Another task for now", "other_task"),
                          ("I'm on track", "fine"), ("Ask me later", "snooze")], timeout_ms=30000)

    def _checkin_work(self, preview=False):
        """Name the nearest open work sometimes, without turning every check-in into the same reminder."""
        if self.calendar and self.calendar.connected:
            return None  # the connected calendar is the user's deadline source
        if not self._st("nudge_work_on", True):
            return None
        choices = sorted((i for i in self.store.important_work if not i.get("done_at") and
                          i.get("title", "").strip() and work_due(i)), key=lambda i: work_due(i))
        if not choices:
            return None
        nearest = choices[0]
        last = self._st("nudge_work_last", None)
        if not preview and isinstance(last, list) and len(last) == 2 and last[0] == nearest.get("id"):
            try:
                if time.time() - float(last[1]) < 2 * 3600:
                    return None
            except (TypeError, ValueError):
                pass
        return nearest

    @staticmethod
    def _calendar_key(event):
        return hashlib.sha256((event["title"] + event["start"].isoformat()).encode()).hexdigest()[:12]

    def _checkin_calendar(self, preview=False):
        if not self.calendar or not self._st("nudge_calendar_on", True):
            return None
        now = datetime.now().astimezone()
        candidates = [e for e in self.calendar.events if 20 * 60 <= (e["start"] - now).total_seconds() <= 24 * 3600]
        if not candidates:
            return None
        nearest = candidates[0]
        last = self._st("nudge_calendar_last", None)
        if not preview and isinstance(last, list) and len(last) == 2 and last[0] == self._calendar_key(nearest):
            try:
                if time.time() - float(last[1]) < 2 * 3600:
                    return None
            except (TypeError, ValueError):
                pass
        return nearest

    def ask_other_task(self, urgent=False):
        line = ("Something urgent needs your attention. When should I check if you're ready to return "
                "to what you planned?" if urgent else "Got it. When should I check if you're ready to return?")
        self._say_followup(line,
                           [("10 min", "other_10"), ("20 min", "other_20"), ("30 min", "other_30"),
                            ("No extra check", "other_0")], "__other_task__", emoji="\U0001F9ED",
                           timeout_ms=30000)

    def ask_focus_minutes(self, event_span=None):
        """Use the same focus lengths for regular, calendar, work, and break-return check-ins."""
        prompt = (f"Event starts in {event_span}. How long for this focus round?" if event_span
                  else "How long for this focus round?")
        self._say_followup(prompt,
                           [(f"{m} min", f"focus_{m}") for m in (5, 10, 25, 50)] + [("Cancel", "focus_cancel")],
                           "__focus_length__", emoji="\u23F1\uFE0F", timeout_ms=30000,
                           minute_input=("focus", 600))

    def ask_break_minutes(self):
        self._say_followup("How long for a break?",
                           [(f"{m} min", f"break_{m}") for m in (5, 10, 15, 25)] + [("Cancel", "break_cancel")],
                           "__break_length__", emoji="\u2615", timeout_ms=30000,
                           minute_input=("break", 600))

    def back_from_break(self, minutes):
        """Input resumed after a long break; offer a way forward without asking for an activity log."""
        if self.quiet_reason() or self.speech.isVisible():
            return
        self._say_followup(f"Welcome back. The break ended {fmt_min(round(minutes))} min ago. What next?",
                           [("Start focus", "focus"), ("I'm back", "back"), ("A few more min", "more")],
                           "__overrun__", emoji="\U0001F44B", timeout_ms=45000)

    def ask_worked_minutes(self):
        """'I was working, forgot the timer': screen time can include scrolling, so ask how long it was work."""
        most = getattr(self, "_active_min", 0) or int(self._st("nudge_every_min", 45))
        opts = [m for m in (10, 20, 30, 45, 60, 90) if m < most - 4][:4]
        chips = [(f"{m} min", f"worked_{m}") for m in opts] + [(f"All {most} min", f"worked_{most}"),
                                                                 ("Skip", "worked_0")]
        self._say_followup("Nice. Roughly how long were you actually working? I'll log that as focus.",
                           chips, "__worked__", emoji="\u23F1\uFE0F", timeout_ms=45000,
                           minute_input=("worked", max(1, most)))

    def log_forgotten_focus(self, minutes):
        """'I was working, forgot the timer': the screen time before the check-in goes in as a focus session."""
        end = datetime.now()
        FocusTimer._write({"kind": "focus", "start": (end - timedelta(minutes=minutes)).isoformat(timespec="seconds"),
                           "end": end.isoformat(timespec="seconds"), "planned_min": minutes,
                           "focused_min": float(minutes), "completed": True, "note": "logged after the fact"})

    def _say_followup(self, text, buttons, tag, emoji="\U0001F44D", timeout_ms=20000, minute_input=None):
        self._asked = tag
        self.bubble.hop()
        self.speech.say(self.bubble.geometry(), text, buttons, emoji=emoji, anim="bounce", timeout_ms=timeout_ms,
                        minute_input=minute_input)

    def away_back(self, minutes, same_session, start_iso):
        """Back after being away mid-focus: offer to take that time out of the session."""
        if self.quiet_reason():
            return
        self._away = (minutes, same_session, start_iso)
        face, line = pick_fresh(AWAY_LINES, "away")
        self._say_followup(line.format(m=fmt_min(round(minutes))),
                           [("Keep it", "keep"), ("Take it out", "trim")], "__away__", emoji=face)

    break_parts = None       # minutes of each break in a row ([5, 5] after "a few more min")

    def break_over(self, minutes=None):
        """The moment a break ends: one short line from the circle, with the ways back. After an extended break it
        adds them up ("5 + 5 min of break. That's 10. Now what?")."""
        if self.break_parts is None:
            self.break_parts = []
        if minutes:
            self.break_parts.append(minutes)
        if self.quiet_reason():
            return
        parts = self.break_parts
        if len(parts) >= 2:
            face, line = pick_fresh(EXTENDED_BREAK_LINES, "break_ext")
            line = line.format(parts=" + ".join(fmt_min(p) for p in parts), total=fmt_min(sum(parts)), n=len(parts))
        else:
            face, line = pick_fresh(BREAK_END_LINES, "break_end")
        self._say_followup(line, [("Start focus", "focus"), ("I'm back", "back"), ("A few more min", "more")],
                           "__overrun__", emoji=face, timeout_ms=45000)
        return line

    def ask_more_break(self):
        """How much longer? A few quick picks, or your own number."""
        self._say_followup("How many more minutes?", [(f"{m} min", f"more_{m}") for m in (2, 5, 10, 15)]
                           + [("Cancel", "more_cancel")], "__more__", emoji="\u23F3", timeout_ms=30000,
                           minute_input=("more", 120))

    def overrun_nudge(self, minutes):
        """The break is over and you're not back: ask again every few minutes (Settings > Focus & breaks)."""
        if self.quiet_reason():
            return
        face, line = pick_fresh(OVERRUN_LINES, "overrun")
        self._say_followup(line.format(m=int(round(minutes))),
                           [("Start focus", "focus"), ("I'm back", "back"), ("A few more min", "more")],
                           "__overrun__", emoji=face, timeout_ms=45000)

    def ask_style(self):
        """First run: one question so the start-of-focus lines fit (nudges to start, or keep-you-in-flow)."""
        self.store.settings["procrastinator_asked"] = True
        self.store.save()
        self._say_followup("Hi! One question so start lines fit you. When a focus round starts, what helps more?",
                           [("A push to start", "style_yes"), ("Some of each", "style_sometimes"),
                            ("Staying in flow", "style_no")],
                           "__style__", emoji="\U0001F44B", timeout_ms=60000)

    BREAK_TAGS = ["Meal", "Call", "Rest", "Walk"]

    def tag_choices(self, kind="focus"):
        """Up to 4 quick answers for "what's this round for?": the calendar event on now or soon, recent tags,
        then open important work."""
        if kind == "break":
            return list(self.BREAK_TAGS)
        out = []
        if self.calendar:
            now = datetime.now().astimezone()
            out += [e["title"].strip() for e in self.calendar.events
                    if e["start"] - timedelta(minutes=30) <= now < e["end"]][:1]
        out += self._st("recent_tags", [])
        out += [i.get("title", "").strip() for i in self.store.important_work if not i.get("done_at")]
        seen, picks = set(), []
        for t in out:
            t = " ".join(str(t).split())[:80]
            if t and t.lower() not in seen:
                seen.add(t.lower())
                picks.append(t)
        return picks[:4]

    def ask_tag(self, kind=None, lead=""):
        """Ask what the running round is for. Answering is optional; it times out quietly."""
        kind = kind or self.timer.kind
        self._tag_picks = self.tag_choices(kind)
        q = "Break for?" if kind == "break" else "What's this round for?"
        self._say_followup((lead + " " if lead else "") + q,
                           [(short_text(t, 22), f"tag_{i}") for i, t in enumerate(self._tag_picks)]
                           + [("Other...", "tag_other"), ("Skip", "tag_skip")],
                           "__tag__", emoji="☕" if kind == "break" else "\U0001F3AF", timeout_ms=20000)

    def ask_tag_text(self):
        kind = self.timer.kind
        text = ask(None, "Break for?" if kind == "break" else "What's this round for?",
                   (self.timer.state or {}).get("on", ""), chips=self.tag_choices(kind))
        if text and self.timer.running:
            self.timer.set_on(text)

    def boost(self):
        if not self._st("boost_on", True) or self.quiet_reason():
            return
        self._asked = None
        self.bubble.hop()
        self.speech.say(self.bubble.geometry(), boost_line(self._st("procrastinator", "sometimes")), (),
                        timeout_ms=4500, emoji=random.choice(BOOST_FACES), anim="bounce")

    def _answered(self, key):
        msg, self._asked = self._asked, None
        if key == "checkin_more":
            QTimer.singleShot(0, lambda m=msg: self.more_choices(m))
            return
        if msg is None:
            return
        if msg == "__style__":
            if key.startswith("style_"):
                self.store.settings["procrastinator"] = key[len("style_"):]
                self.store.save()
            return
        if msg == "__tag__":
            if key == "tag_other":
                QTimer.singleShot(0, self.ask_tag_text)
            elif key.startswith("tag_") and key[4:].isdigit():
                picks = getattr(self, "_tag_picks", [])
                if int(key[4:]) < len(picks):
                    self.timer.set_on(picks[int(key[4:])])
            return
        if msg == "__away__":
            if key == "trim" and getattr(self, "_away", None):
                self.timer.trim_away(*self._away)
            self._away = None
            return
        if msg == "__worked__":
            mins = int(key[len("worked_"):]) if key.startswith("worked_") else 0
            if mins:
                self.log_forgotten_focus(mins)
                QTimer.singleShot(0, lambda: self._say_followup(
                    f"Logged {mins} min as focus. Want a timer running from here?",
                    [("Start focus", "focus"), ("No thanks", "fine")], "__backfill__"))
            return
        if msg == "__overrun__":
            if key == "focus":
                self.break_parts = []
                QTimer.singleShot(0, self.ask_focus_minutes)
            elif key == "back":
                self.break_parts = []
                self.timer.clear_overrun()
            elif key == "more":
                QTimer.singleShot(0, self.ask_more_break)
            return
        if msg == "__more__":
            try:
                mins = int(key[len("more_"):]) if key.startswith("more_") else 0
            except ValueError:
                mins = 0
            if mins:
                self.wants_more_break.emit(float(mins))
            return
        if msg == "__backfill__":
            if key == "focus":
                QTimer.singleShot(0, self.ask_focus_minutes)
            return
        if msg == "__focus_length__":
            try:
                minutes = float(key[len("focus_"):]) if key.startswith("focus_") else 0
            except ValueError:
                minutes = 0
            if 1 <= minutes <= 600:
                self.store.settings["focus_min"] = minutes
                self.store.save()
                self.wants_focus.emit(minutes)
            return
        if msg == "__break_length__":
            try:
                minutes = float(key[len("break_"):]) if key.startswith("break_") else 0
            except ValueError:
                minutes = 0
            if 1 <= minutes <= 600:
                self.wants_break.emit(minutes)
            return
        if msg == "__other_task__":
            try:
                delay = int(key[len("other_"):]) if key.startswith("other_") else 0
            except ValueError:
                delay = 0
            if delay:
                interval = float(self._st("nudge_every_min", 45))
                self.active_s = (interval - delay) * 60
                self.store.settings["nudge_active"] = [round(self.active_s), time.time()]
                self.store.save()
            return
        FocusTimer._write({"kind": "checkin", "start": datetime.now().isoformat(timespec="seconds"),
                           "end": datetime.now().isoformat(timespec="seconds"), "message": msg, "response": key})
        event_span, self._focus_event_span = self._focus_event_span, None
        if key == "focus":
            QTimer.singleShot(0, lambda s=event_span: self.ask_focus_minutes(s))
        elif key == "working":
            QTimer.singleShot(0, self.ask_worked_minutes)
        elif key == "break":
            QTimer.singleShot(0, self.ask_break_minutes)
        elif key == "other_task":
            QTimer.singleShot(0, self.ask_other_task)
        elif key == "urgent_detour":
            QTimer.singleShot(0, lambda: self.ask_other_task(urgent=True))
        elif key == "snooze":
            self.active_s = -30 * 60   # ask again 30 min later than usual

    PAUSE_FOREVER = 4102444800            # 2100-01-01: "until I turn them back on"
    PAUSES = [("30 min", 1800), ("1 hour", 3600), ("2 hours", 7200), ("Rest of today", "today"),
              ("Until I turn them back on", "forever")]

    def pause(self, seconds):
        if seconds == "forever":
            until = self.PAUSE_FOREVER
        elif seconds == "today":
            until = datetime.now().replace(hour=6, minute=0, second=0, microsecond=0).timestamp() + 86400
        else:
            until = time.time() + seconds
        self.store.settings["nudge_paused_until"] = until
        self.store.save()

    @staticmethod
    def paused_text(until):
        if until >= NudgeManager.PAUSE_FOREVER:
            return "until you turn them back on"
        d = datetime.fromtimestamp(until)
        return f"until {d:%H:%M}" if d.date() == datetime.now().date() else f"until {d:%a %H:%M}"


# ---------------------------------------------------------------- end-of-session card
def session_stats(store, start, end):
    """Thoughts captured during [start, end] (epoch seconds): (parked, urges, distractions)."""
    ids, urge, dist = set(), set(), set()
    events = read_jsonl(THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl")
    gone = deleted_ids(events)
    for ev in events:
        if ev.get("id") in gone:
            continue
        try:
            ts = datetime.fromisoformat(ev.get("ts", "")).timestamp()
        except Exception:
            continue
        if not (start - 1 <= ts <= end + 1):
            continue
        tid = ev.get("id")
        if ev.get("event") == "captured":
            ids.add(tid)
            if ev.get("urge"):
                urge.add(tid)
            if ev.get("distraction"):
                dist.add(tid)
        elif ev.get("event") == "urge_on":
            urge.add(tid)
        elif ev.get("event") == "distraction_on":
            dist.add(tid)
    for l in store.lists:  # flags set after the fact still count
        for t in l["tasks"]:
            if t["id"] in ids:
                if t.get("urge"):
                    urge.add(t["id"])
                if t.get("distraction"):
                    dist.add(t["id"])
    return len(ids), len(urge & ids), len(dist & ids)


def session_glimmers(store, start, end):
    """Lifts noticed during [start, end]."""
    ids = set()
    events = read_jsonl(THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl")
    gone = deleted_ids(events)
    for ev in events:
        if ev.get("id") in gone:
            continue
        try:
            ts = datetime.fromisoformat(ev.get("ts", "")).timestamp()
        except Exception:
            continue
        if start - 1 <= ts <= end + 1 and ((ev.get("event") == "captured" and ev.get("glimmer"))
                                           or ev.get("event") == "glimmer_on"):
            ids.add(ev.get("id"))
    return len(ids)


def session_quip(minutes, parked, urges, dists, glimmers=0):
    """A cheeky, kind one-liner for the end of a focus session: (emoji, animation, text)."""
    m = fmt_min(minutes)
    E = {"hamster": "\U0001F439", "zen": "\U0001F9D8", "brow": "\U0001F928", "brain": "\U0001F9E0",
         "files": "\U0001F5C2\uFE0F", "cone": "\U0001F6A7", "door": "\U0001F6AA", "huff": "\U0001F624",
         "ext": "\U0001F9EF", "salute": "\U0001FAE1", "ticket": "\U0001F3AB", "park": "\U0001F17F\uFE0F",
         "nophone": "\U0001F4F5", "no": "\U0001F645", "fire": "\U0001F525", "sloth": "\U0001F9A5",
         "trophy": "\U0001F3C6", "melt": "\U0001FAE0", "spark": "\u2728", "rain": "\U0001F326\uFE0F",
         "sweat": "\U0001F605", "cat": "\U0001F63C", "muscle": "\U0001F4AA", "ghost": "\U0001F47B"}
    pools = []
    if parked == 0:
        pools.append([(E["zen"], "float", f"{m} minutes complete. Nothing needed parking this round."),
                      (E["brain"], "bounce", "No notes this round. The lot is ready whenever you need it."),
                      (E["spark"], "bounce", f"{m} minutes finished. A quiet lot today."),
                      (E["cat"], "tilt", "Empty lot this round. Enjoy the clear space.")])
    if dists >= 2:
        pools.append([(E["files"], "bounce", f"You noted {dists} interruptions. They're here when you want to review them."),
                      (E["cone"], "shake", f"{dists} interruptions tried their luck. The lot has them now."),
                      (E["salute"], "bounce", f"{dists} distractions knocked. You took a note and closed the door."),
                      (E["muscle"], "bounce", f"{dists} interruptions noted, and the round is complete."),
                      (E["ghost"], "float", f"{dists} distractions came by. They're parked now, not haunting you.")])
    elif dists == 1:
        pools.append([(E["door"], "wiggle", "One distraction showed up uninvited. You parked it and kept going. Rude, and correct."),
                      (E["cone"], "shake", "One interruption, one note, back to work. Textbook."),
                      (E["salute"], "bounce", "A distraction tried it. It's in the lot now, thinking about what it did."),
                      (E["files"], "bounce", "One distraction, filed and forgotten. Well, filed."),
                      (E["cat"], "tilt", "Something poked you once. You didn't poke back. Nice.")])
    if urges >= 2:
        pools.append([(E["huff"], "shake", f"{urges} itches noted. You can decide what each needs at the break."),
                      (E["ext"], "wiggle", f"{urges} things felt pressing. Now they're somewhere you can see them."),
                      (E["brain"], "bounce", f"You captured {urges} itches during this round."),
                      (E["salute"], "bounce", f"{urges} itches parked for a clearer look later.")])
    elif urges == 1:
        pools.append([(E["salute"], "bounce", "One itch noted. You can decide what to do with it now."),
                      (E["cat"], "tilt", "One thing asked for your attention. It's written down."),
                      (E["ext"], "wiggle", "One urgent-feeling thing is waiting in the lot."),
                      (E["muscle"], "bounce", "An itch showed up. You made a note of it.")])
    if glimmers:
        ls = "s" if glimmers != 1 else ""
        pools.append([(E["spark"], "float", f"{glimmers} lift{ls} spotted mid-focus. Keep collecting those."),
                      (E["spark"], "bounce", f"You noticed {glimmers} good moment{ls} while working. That's a skill."),
                      (E["cat"], "tilt", f"{glimmers} lift{ls} logged. Your brain is learning to look for them."),
                      (E["zen"], "float", "Focused and still caught a good moment. Best of both.")])
    if parked >= 5:
        pools.append([(E["ticket"], "bounce", f"Your brain opened {parked} tickets. Support team (you) will get to them at the break."),
                      (E["park"], "float", f"{parked} thoughts parked. The lot is busier than your head now. Good trade."),
                      (E["files"], "bounce", f"{parked} thoughts out of your head and into the lot. Lighter already."),
                      (E["brain"], "bounce", f"Busy brain today: {parked} parked. And you still finished."),
                      (E["rain"], "float", f"{parked} thoughts rained down. You caught every one.")])
    pools.append([(E["hamster"], "shake", f"Focus round complete: {m} minutes."),
                  (E["brain"], "bounce", f"{m} minutes set aside for one thing. Nicely done."),
                  (E["sloth"], "float", f"Slow and steady counts. {m} minutes complete."),
                  (E["trophy"], "bounce", "The round is finished. Take a moment before the next one."),
                  (E["melt"], "float", "One round done. Let your shoulders drop."),
                  (E["cat"], "tilt", f"{m} minutes complete. Stretch if you need one."),
                  (E["muscle"], "bounce", "A finished round is something you can build on."),
                  (E["spark"], "float", f"{m} minutes complete. A break is a good next step."),
                  (E["salute"], "bounce", f"Round done. {m} minutes on the clock."),
                  (E["zen"], "float", "Done for now. Look away from the screen for a moment."),
                  (E["fire"], "shake", "Round complete. The next move is yours."),
                  (E["ghost"], "float", "That session is in the books. What would help next?"),
                  (E["sloth"], "float", "Finished. No rush to decide the next round.")])
    specific = [x for pool in pools[:-1] for x in pool]
    general = pools[-1]
    use = specific if specific and random.random() < 0.65 else general    # the general lines stay in the mix
    return pick_fresh(use, "quip_specific" if use is specific else "quip_general")


def fmt_hm(minutes):
    minutes = int(round(minutes))
    return f"{minutes} min" if minutes < 60 else f"{minutes // 60} h {minutes % 60:02d} min"


def today_summary(store):
    """One line for the session card: today's sessions, focus time, and what happened to thoughts."""
    n, mins = FocusTimer.today_stats()
    today = datetime.now().date().isoformat()
    parked = let_go = done = 0
    glim = set()
    events = read_jsonl(THOUGHT_LOG, RESCUE_DIR / "thought_log.rescue.jsonl")
    gone = deleted_ids(events)
    for ev in events:
        if not str(ev.get("ts", "")).startswith(today) or ev.get("id") in gone:
            continue
        k = ev.get("event")
        parked += k == "captured"
        let_go += k == "let_go"
        done += k == "done"
        if (k == "captured" and ev.get("glimmer")) or k == "glimmer_on":
            glim.add(ev.get("id"))
    bits = [f"{n} session{'s' if n != 1 else ''}", f"{fmt_hm(mins)} focused", f"{parked} parked"]
    if done:
        bits.append(f"{done} done")
    if let_go:
        bits.append(f"{let_go} let go")
    if glim:
        bits.append(f"{len(glim)} lift{'s' if len(glim) != 1 else ''}")
    line = "Today: " + " \u00B7 ".join(bits)
    tags = FocusTimer.today_by_tag()
    if tags:
        line += "\nOn: " + ", ".join(f"{t} {fmt_hm(m)}" for t, m in tags[:4])
    return line


class SessionCard(QWidget):
    """Grows out of the circle when a focus session completes: the numbers, a cheeky line, and next steps."""

    def __init__(self):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setObjectName("sessionCard")
        self.setStyleSheet(STYLE + f"""
            QLabel#quip {{ color: {C['text']}; font-size: 14px; font-weight: 600; }}
            QLabel#statNum {{ color: {C['text']}; font-size: 22px; font-weight: 700; }}
            QLabel#statLbl {{ color: {C['dim']}; font-size: 11px; }}
            QLabel#todayLine {{ color: {C['dim']}; font-size: 11px; padding: 6px 0 0 0;
                border-top: 1px solid {C['border']}; }}
            QLabel#head {{ color: {C['accent_text']}; font-size: 12px; font-weight: 700; }}
            QPushButton#primary {{ background: {C['accent']}; border: 1px solid {C['accent']}; color: white;
                padding: 6px 12px; border-radius: 8px; font-weight: 600; }}
            QPushButton#primary:hover {{ background: #b54552; }}
            QPushButton#ghost {{ background: transparent; padding: 6px 12px; border-radius: 8px; }}
            QPushButton#appChip {{ background: transparent; padding: 5px 8px; border-radius: 8px; }}
            QPushButton#appChip:checked {{ background: {C['dist_bg']}; color: {C['dist']}; border-color: {C['dist']}; }}
            QLineEdit#nextFocusMinutes {{ background: {C['surface_hi']}; color: {C['text']};
                border: 1px solid {C['border']}; border-radius: 7px; padding: 6px 8px; }}""")
        self.W = 330
        lay = QVBoxLayout(self)
        lay.setContentsMargins(20, 16, 20, 16)
        lay.setSpacing(10)
        top = QHBoxLayout()
        self.head = QLabel("Focus complete")
        self.head.setObjectName("head")
        x = QToolButton()
        x.setText("\u2715")
        x.clicked.connect(self.close_card)
        top.addWidget(self.head, 1)
        top.addWidget(x)
        lay.addLayout(top)
        self.quip = QLabel()
        self.quip.setObjectName("quip")
        self.quip.setWordWrap(True)
        self.face = EmojiFace(34)
        qrow = QHBoxLayout()
        qrow.setSpacing(8)
        qrow.addWidget(self.face, 0, Qt.AlignTop)
        qrow.addWidget(self.quip, 1)
        lay.addLayout(qrow)
        grid = QGridLayout()
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(0)
        self.nums, self.lbls = [], []
        for i in range(4):
            n = QLabel()
            n.setObjectName("statNum")
            n.setAlignment(Qt.AlignCenter)
            lbl = QLabel()
            lbl.setObjectName("statLbl")
            lbl.setAlignment(Qt.AlignCenter)
            lbl.setWordWrap(True)
            grid.addWidget(n, 0, i)
            grid.addWidget(lbl, 1, i)
            self.nums.append(n)
            self.lbls.append(lbl)
        lay.addLayout(grid)
        self.today = QLabel()
        self.today.setObjectName("todayLine")
        self.today.setWordWrap(True)
        self.today.setAlignment(Qt.AlignCenter)
        lay.addWidget(self.today)
        self.apps_line = QLabel(self)            # opt-in app tracking: where this round's time went
        self.apps_line.setObjectName("todayLine")
        self.apps_line.setWordWrap(True)
        lay.addWidget(self.apps_line)
        self.mark_row = QWidget(self)            # press the apps that distracted you this round
        mark_lay = QVBoxLayout(self.mark_row)
        mark_lay.setContentsMargins(0, 0, 0, 0)
        mark_lay.setSpacing(6)
        self.mark_q = QLabel("Choose the distracting apps from this session:", self.mark_row)
        self.mark_q.setWordWrap(True)
        mark_lay.addWidget(self.mark_q)
        self.app_grid = QGridLayout()
        self.app_grid.setSpacing(5)
        mark_lay.addLayout(self.app_grid)
        self.app_buttons = {}
        lay.addWidget(self.mark_row)
        self.actions = QWidget(self)
        btns = QHBoxLayout(self.actions)
        btns.setContentsMargins(0, 0, 0, 0)
        self.b_break = QPushButton()
        self.b_break.setObjectName("primary")
        self.b_again = QPushButton()
        self.b_again.setObjectName("ghost")
        self.b_take = QPushButton()
        self.b_take.setObjectName("ghost")
        self.b_take.setToolTip("Take the minutes in distracting apps out of this round's focus time")
        self.b_take.clicked.connect(self._take_out)
        mark_lay.addWidget(self.b_take, 0, Qt.AlignLeft)   # under the chips: three buttons don't fit one row
        btns.addWidget(self.b_break)
        btns.addWidget(self.b_again)
        btns.addStretch(1)
        lay.addWidget(self.actions)
        self.choices = QWidget(self)
        choice_lay = QVBoxLayout(self.choices)
        choice_lay.setContentsMargins(0, 0, 0, 0)
        choice_lay.setSpacing(7)
        self.choice_prompt = QLabel(self.choices)
        self.choice_prompt.setWordWrap(True)
        choice_lay.addWidget(self.choice_prompt)
        presets = QHBoxLayout()
        presets.setSpacing(5)
        self.length_buttons = {}
        for length in (5, 10, 25, 50):
            button = QPushButton(f"{length} min", self.choices)
            button.setObjectName("ghost")
            button.clicked.connect(lambda _=False, b=button: self._choose_length(b.property("minutes")))
            button.setProperty("minutes", length)
            presets.addWidget(button)
            self.length_buttons[length] = button
        choice_lay.addLayout(presets)
        custom = QHBoxLayout()
        custom.setSpacing(6)
        self.custom_minutes = QLineEdit(self.choices)
        self.custom_minutes.setObjectName("nextFocusMinutes")
        self.custom_minutes.setPlaceholderText("Minutes")
        self.custom_minutes.setAccessibleName("Custom focus minutes")
        self.custom_minutes.setValidator(QIntValidator(1, 600, self.custom_minutes))
        self.custom_minutes.returnPressed.connect(self._start_custom)
        custom.addWidget(self.custom_minutes, 1)
        self.custom_start = QPushButton("Start", self.choices)
        self.custom_start.setObjectName("primary")
        self.custom_start.setAccessibleName("Start custom focus round")
        self.custom_start.setEnabled(False)
        self.custom_start.clicked.connect(self._start_custom)
        self.custom_minutes.textChanged.connect(
            lambda text: self.custom_start.setEnabled(bool(text and self.custom_minutes.hasAcceptableInput())))
        custom.addWidget(self.custom_start)
        back = QPushButton("Back", self.choices)
        back.setObjectName("ghost")
        back.clicked.connect(self._back_from_choices)
        custom.addWidget(back)
        choice_lay.addLayout(custom)
        lay.addWidget(self.choices)
        self.choices.hide()
        self.anim = QVariantAnimation(self)
        self.anim.valueChanged.connect(self._step)
        self.auto = QTimer(self)
        self.auto.setSingleShot(True)
        self.auto.timeout.connect(lambda: None if self.underMouse() else self.close_card())
        self.on_break = self.on_again = self.on_mark = self.on_take_out = None
        self.app_rows, self.marks, self._taken, self.focus_min = [], {}, False, 0
        self.choice_kind = "focus"
        self.auto_break = False
        self.b_break.clicked.connect(self._ask_break)
        self.b_again.clicked.connect(self._ask_again)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(1, 1, -1, -1)
        p.setBrush(QColor(C["surface_hi"]))
        p.setPen(QPen(QColor(C["border"]), 1))
        p.drawRoundedRect(r, 12, 12)

    def show_for(self, circle_rect, minutes, parked, urges, dists, break_min, focus_min, auto_break=False,
                 glimmers=0, today="", on="", apps=None, marks=None):
        face, anim, line = session_quip(minutes, parked, urges, dists, glimmers)
        self.quip.setText(line)
        self.face.set(face, anim)
        self.today.setText(today)
        self.today.setVisible(bool(today))
        head = "Focus complete \u00B7 break started" if auto_break else "Focus complete"
        self.head.setText(head + (f" \u00B7 {short_text(on, 28)}" if on else ""))
        self.app_rows, self.marks, self.focus_min = list(apps or []), dict(marks or {}), minutes
        self._taken = False
        self._build_app_buttons()
        self._show_apps()
        data = [(fmt_min(minutes), "min focused"), (str(parked), "thoughts parked"),
                (str(urges), "itches noted" if urges != 1 else "itch noted"),
                (str(dists), "interruptions noted" if dists != 1 else "interruption noted")]
        for (n, l), wn, wl in zip(data, self.nums, self.lbls):
            wn.setText(n)
            wl.setText(l)
        self.auto_break = auto_break
        self.b_break.setText("Start break")
        self.b_again.setText("Focus again")
        self._set_choices("focus")
        self.actions.show()
        self.choices.hide()
        self.custom_minutes.clear()
        self._circle_rect = QRect(circle_rect)
        screen_for(self, circle_rect.center())
        self.setFixedWidth(self.W)
        self.layout().activate()
        h = max(self.sizeHint().height(), self.heightForWidth(self.W), self.layout().minimumHeightForWidth(self.W)
                if self.layout().hasHeightForWidth() else 0)
        self.setFixedHeight(h + 4)
        screen = QGuiApplication.screenAt(circle_rect.center()) or QGuiApplication.primaryScreen()
        area = screen.availableGeometry()
        right_side = circle_rect.center().x() > area.center().x()
        x = circle_rect.left() - self.W - 10 if right_side else circle_rect.right() + 10
        y = circle_rect.center().y() - self.height() // 2
        x = max(area.left(), min(x, area.right() - self.W))
        y = max(area.top(), min(y, area.bottom() - self.height()))
        self._final = QRect(x, y, self.W, h + 4)
        self._origin = QRect(circle_rect.center().x() - 12, circle_rect.center().y() - 12, 24, 24)
        self.setMinimumSize(0, 0)
        self.setMaximumSize(16777215, 16777215)
        self.setGeometry(self._origin)
        self.setWindowOpacity(0.0)
        self.show()
        apply_share_privacy(self)
        self.anim.stop()
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.setDuration(420)
        self.anim.setEasingCurve(QEasingCurve.OutBack)
        self.anim.start()
        self.auto.start(30000)

    def _fit_open_card(self):
        self.anim.stop()
        self.setFixedWidth(self.W)
        self.layout().activate()
        height = max(self.sizeHint().height(), self.layout().minimumSize().height()) + 4
        area = screen_for(self, self._circle_rect.center()).availableGeometry()
        height = min(height, area.height() - 12)
        x = self._final.x()
        y = max(area.top(), min(self._circle_rect.center().y() - height // 2, area.bottom() - height))
        self._final = QRect(x, y, self.W, height)
        self.setGeometry(self._final)
        self.setWindowOpacity(1.0)

    def app_totals(self):
        """[(app, minutes)] for this round, summed over window titles, biggest first."""
        by = {}
        for r in self.app_rows:
            by[r["app"]] = by.get(r["app"], 0) + r["min"]
        return sorted(by.items(), key=lambda kv: -kv[1])

    def distracting_min(self):
        return int(sum(m for a, m in self.app_totals() if self.marks.get(a) == "distracting"))

    def _show_apps(self):
        totals = self.app_totals()
        bits = [f"{a} {fmt_min(round(m))} min" + (" (distracting)" if self.marks.get(a) == "distracting" else "")
                for a, m in totals[:4] if m >= 0.5]
        self.apps_line.setText("Apps: " + " · ".join(bits) if bits else "")
        self.apps_line.setVisible(bool(bits))
        self.mark_row.setVisible(bool(self.app_buttons))
        n = self.distracting_min()
        self.b_take.setText(f"Take out {n} min")
        self.b_take.setVisible(n >= 1 and not self._taken)

    def _build_app_buttons(self):
        """One toggle per app used a minute or more this round; pressed = distracting."""
        for b in self.app_buttons.values():
            self.app_grid.removeWidget(b)
            b.deleteLater()
        self.app_buttons = {}
        apps = [a for a, m in self.app_totals() if m >= 1][:8]   # ponytail: 8 biggest, the rest are noise
        for i, a in enumerate(apps):
            b = QPushButton(short_text(a.removesuffix(".exe"), 18), self.mark_row)
            b.setObjectName("appChip")
            b.setToolTip(a)
            b.setCheckable(True)
            b.setChecked(self.marks.get(a) == "distracting")
            b.toggled.connect(lambda on, app=a: self._mark(app, on))
            self.app_grid.addWidget(b, i // 2, i % 2)
            self.app_buttons[a] = b

    def _mark(self, app, distracting):
        verdict = "distracting" if distracting else ""
        if verdict:
            self.marks[app] = verdict
        else:
            self.marks.pop(app, None)
        if self.on_mark:
            self.on_mark(app, verdict)
        self._show_apps()
        self._fit_open_card()

    def _take_out(self):
        n = self.distracting_min()
        taken = self.on_take_out(n) if (self.on_take_out and n) else 0
        if taken:
            self.focus_min = max(0, self.focus_min - taken)
            self.nums[0].setText(fmt_min(self.focus_min))
            self._taken = True                   # don't offer it twice
            self.b_take.hide()
            self._fit_open_card()

    def _ask_again(self):
        self._set_choices("focus")
        self.auto.stop()
        self.actions.hide()
        self.choices.show()
        self._fit_open_card()
        self.length_buttons[25].setFocus()

    def _ask_break(self):
        self._set_choices("break")
        self.auto.stop()
        self.actions.hide()
        self.choices.show()
        self._fit_open_card()
        self.length_buttons[10].setFocus()

    def _set_choices(self, kind):
        self.choice_kind = kind
        lengths = (5, 10, 15, 25) if kind == "break" else (5, 10, 25, 50)
        buttons = list(self.length_buttons.values())
        for button, minutes in zip(buttons, lengths):
            button.setText(f"{minutes} min")
            button.setProperty("minutes", minutes)
        self.length_buttons = dict(zip(lengths, buttons))
        if kind == "break":
            self.choice_prompt.setText("How long for a break?" +
                                       (" The current break will restart." if self.auto_break else ""))
        else:
            self.choice_prompt.setText("How long for another focus round?" +
                                       (" The break will end." if self.auto_break else ""))
        self.custom_minutes.clear()
        self.custom_minutes.setAccessibleName(f"Custom {kind} minutes")
        self.custom_start.setAccessibleName(f"Start custom {kind}")

    def _back_from_choices(self):
        self.choices.hide()
        self.actions.show()
        self._fit_open_card()
        (self.b_break if self.choice_kind == "break" else self.b_again).setFocus()
        self.auto.start(30000)

    def _start_custom(self):
        if self.custom_minutes.hasAcceptableInput():
            self._choose_length(int(self.custom_minutes.text()))

    def _choose_length(self, minutes):
        if self.choice_kind == "break":
            if self.on_break and self.on_break(minutes):
                self.close_card()
        else:
            self._start_again(minutes)

    def _start_again(self, minutes):
        if self.on_again and self.on_again(minutes):
            self.close_card()

    def _step(self, v):
        v = float(v)
        a, b = self._origin, self._final
        lerp = lambda p, q: int(p + (q - p) * v)
        self.setGeometry(QRect(lerp(a.x(), b.x()), lerp(a.y(), b.y()),
                               max(24, lerp(a.width(), b.width())), max(24, lerp(a.height(), b.height()))))
        self.setWindowOpacity(max(0.0, min(1.0, v * 1.4)))

    def close_card(self):
        self.anim.stop()
        self.auto.stop()
        self.hide()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Escape:
            self.close_card()
        else:
            super().keyPressEvent(e)

    def take_keys(self):
        self.auto.stop()
        force_foreground(self)
        (self.b_again if self.actions.isVisible() else self.custom_minutes).setFocus()


def confirm_focus_started(bubble, speech, timer, minutes):
    """Acknowledge a chosen next round only after the focus timer is running."""
    if not timer.running or timer.kind != "focus":
        return False
    bubble.hop()
    speech.say(bubble.geometry(), f"Focus started for {fmt_min(minutes)} min.", (),
               timeout_ms=4200, emoji="\u23f1\ufe0f", anim="bounce")
    return True


# ---------------------------------------------------------------- floating bubble
RING_STYLES = [("ember", "Ember", "Burning fuse with sparks"),
               ("comet", "Comet", "A glowing head with a soft tail"),
               ("neon", "Neon breath", "Clean glowing line that slowly breathes"),
               ("ticks", "Watch ticks", "60 ticks like a watch bezel, one blinks"),
               ("minimal", "Minimal", "Thin, still line. No animation")]
RING_STYLE_KEYS = {k for k, _, _ in RING_STYLES}
# circle colours: (name, highlight, middle, shadow, hover highlight)
CIRCLE_COLORS = {"white": ("White", "#ffffff", "#eef3f9", "#aebfd2", "#ffffff"),
                 "maroon": ("Maroon", "#cf5a68", "#a13a47", "#5e1c28", "#dc6a77"),
                 "forest": ("Forest", "#63b584", "#2f6b47", "#143624", "#72c493"),
                 "teal": ("Deep teal", "#52b8b6", "#1f6f73", "#0c3638", "#60c6c4"),
                 "rust": ("Rust", "#e3905b", "#a4502a", "#552510", "#ee9f6b"),
                 "midnight": ("Midnight", "#7489dc", "#34438f", "#151c45", "#8397e6"),
                 "mustard": ("Mustard", "#e6c46a", "#a8822a", "#56420f", "#eecf7a"),
                 "graphite": ("Graphite", "#8e939c", "#4a4e56", "#202328", "#9ea3ab")}
CIRCLE_SHAPES = {"cloud": "Thought cloud", "circle": "Circle", "squircle": "Squircle (soft square)",
                 "pebble": "Pebble (hand-made look)", "capsule": "Capsule (wide and calm)",
                 "diamond": "Soft diamond", "oval": "Oval (tall and simple)",
                 "hexagon": "Soft hexagon", "speech": "Speech bubble"}
CIRCLE_SIZES = {"small": ("Small", 0.82), "medium": ("Medium", 1.0), "large": ("Large", 1.22), "xl": ("Extra large", 1.45)}


class Bubble(QWidget):
    """The floating circle. The middle always shows the open-task count (or a dot). Every timer lives on
    the outline: it burns down clockwise from 12 o'clock with a glowing ember and sparks at its tip
    (gold to orange for focus, teal to green for a break). An overrun break breathes amber."""
    clicked = Signal()
    moved = Signal(QPoint)
    SIZE = 56          # widget size; leaves room for the glow and sparks around the ring
    BODY_R = 16        # radius of the circle
    RING_R = 21        # radius of the timer outline
    PALETTE = {"focus": ("#fff3c4", "#ffb347", "#e8590c", "#8a2d0a"),   # tip, hot, warm, base
               "break": ("#e6fff6", "#7ee0c0", "#2fb58a", "#135e4a")}

    def __init__(self, menu_builder):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setFixedSize(self.SIZE, self.SIZE)
        self.setAcceptDrops(True)
        self.count = 0
        self.show_count = True
        self.save_ok = True
        self.timer = None            # FocusTimer, set by main()
        self.timer_display = "ring"  # ring | time | hidden
        self.ring_style = "ember"    # see RING_STYLES
        self.color_key = "auto"      # see CIRCLE_COLORS; "auto" = white on dark, midnight on light
        self.shape = "cloud"         # see CIRCLE_SHAPES
        self.scale = 1.0
        self.drop_handler = None     # callable(QMimeData) -> bool, set by main()
        self._drag_hover = False
        self._hover = False
        self._press = None
        self._dragging = False
        self.menu_builder = menu_builder
        self._sparks = []            # [x, y, vx, vy, age, life, color]
        self._t0 = time.monotonic()
        self._last = self._t0
        self._hop_y = 0.0
        self.hop_anim = QVariantAnimation(self)
        self.hop_anim.setStartValue(0.0)
        self.hop_anim.setEndValue(1.0)
        self.hop_anim.setDuration(700)
        self.hop_anim.valueChanged.connect(self._hop_step)
        self.anim = QTimer(self)
        self.anim.setInterval(33)    # ~30 fps, only while something is animating
        self.anim.timeout.connect(self._animate)
        self._update_tooltip()

    # ---- state
    def _update_tooltip(self):
        tip = APP_NAME                      # how-to lives behind the ? button; the circle just says who it is
        if self.timer and not self.timer.running and self.timer.overrun_since:
            tip += f"\n{self.timer.overrun_label()}"
        if self.timer and self.timer.running:
            tip += (("\nBreak" if self.timer.kind == "break" else "\nFocus") + f": {fmt_mmss(self.timer.remaining())} left"
                    + (" (paused)" if self.timer.paused else ""))
        if not self.save_ok:
            tip += "\nSaving is retrying (OneDrive busy?). A rescue copy is kept locally."
        self.setToolTip(tip)

    def set_count(self, n):
        self.count = n
        self.update()

    def set_save_ok(self, ok):
        self.save_ok = ok
        self._update_tooltip()
        self.update()

    def body_key(self):
        if self.color_key == "auto":
            return "white" if theme_dark() else "midnight"
        return self.color_key

    def set_look(self, color=None, shape=None, size=None):
        """Colour, shape and size of the circle. Size keeps the circle's centre where it was."""
        if color in CIRCLE_COLORS or color == "auto":
            self.color_key = color
        if shape in CIRCLE_SHAPES:
            self.shape = shape
        if size in CIRCLE_SIZES:
            scale = CIRCLE_SIZES[size][1]
            if abs(scale - self.scale) > 1e-6:
                centre = self.geometry().center()
                self.scale = scale
                self.SIZE = int(round(56 * scale))
                self.BODY_R = 16 * scale
                self.RING_R = 21 * scale
                self.setFixedSize(self.SIZE, self.SIZE)
                self.move(centre.x() - self.SIZE // 2, centre.y() - self.SIZE // 2)
                self.moved.emit(self.pos())
        self.update()

    def _body_path(self, c, B):
        path = QPainterPath()
        if self.shape == "cloud":     # a thought cloud: puffs around the middle, two small bubbles trailing off
            return cloud_path(c, B)
        elif self.shape == "squircle":
            path.addRoundedRect(QRectF(c - B, c - B, 2 * B, 2 * B), B * 0.62, B * 0.62)
        elif self.shape == "capsule":
            path.addRoundedRect(QRectF(c - B, c - B * 0.68, 2 * B, 1.36 * B), B * 0.68, B * 0.68)
        elif self.shape == "oval":
            path.addEllipse(QRectF(c - B * 0.78, c - B, B * 1.56, B * 2))
        elif self.shape == "hexagon":
            points = [(c - B * .86, c - B * .48), (c, c - B), (c + B * .86, c - B * .48),
                      (c + B * .86, c + B * .48), (c, c + B), (c - B * .86, c + B * .48)]
            path.moveTo(*points[0])
            for x, y in points[1:]:
                path.lineTo(x, y)
            path.closeSubpath()
        elif self.shape == "speech":
            path.addRoundedRect(QRectF(c - B, c - B * .87, 2 * B, B * 1.55), B * .42, B * .42)
            path.moveTo(c - B * .42, c + B * .57)
            path.lineTo(c - B * .62, c + B)
            path.lineTo(c + B * .08, c + B * .57)
            path.closeSubpath()
        elif self.shape == "diamond":
            path.moveTo(c, c - B)
            path.cubicTo(c + B * 0.22, c - B * 0.78, c + B * 0.78, c - B * 0.22, c + B, c)
            path.cubicTo(c + B * 0.78, c + B * 0.22, c + B * 0.22, c + B * 0.78, c, c + B)
            path.cubicTo(c - B * 0.22, c + B * 0.78, c - B * 0.78, c + B * 0.22, c - B, c)
            path.cubicTo(c - B * 0.78, c - B * 0.22, c - B * 0.22, c - B * 0.78, c, c - B)
            path.closeSubpath()
        elif self.shape == "pebble":   # a slightly uneven, hand-made outline
            n = 72
            for i in range(n + 1):
                a = 2 * math.pi * i / n
                r = B * (1 + 0.055 * math.sin(3 * a + 0.9) + 0.035 * math.sin(5 * a + 2.1))
                pt = QPointF(c + r * math.cos(a), c + r * math.sin(a) * 0.96)
                path.moveTo(pt) if i == 0 else path.lineTo(pt)
            path.closeSubpath()
        else:
            path.addEllipse(QRectF(c - B, c - B, 2 * B, 2 * B))
        return path

    def _burning(self):
        t = self.timer
        return bool(t and t.running and not t.paused and self.timer_display != "hidden")

    def _animated(self):
        """The 30 fps loop only runs for styles that move; Minimal just repaints once a second."""
        return self._burning() and self.ring_style != "minimal"

    def _overrun(self):
        t = self.timer
        return bool(t and not t.running and t.overrun_since)

    def refresh_shape(self):
        """Called every second by the timer: refresh tooltip, start/stop the animation."""
        self._update_tooltip()
        want = self._animated() or self._overrun() or bool(self._sparks)
        if want and not self.anim.isActive():
            self._last = time.monotonic()
            self.anim.start()
        elif not want and self.anim.isActive():
            self.anim.stop()
        self.update()

    def _tip_point(self, frac):
        """Point on the ring at 'frac' of a full turn, clockwise from 12 o'clock."""
        c = self.SIZE / 2
        a = 2 * math.pi * frac
        return c + self.RING_R * math.sin(a), c - self.RING_R * math.cos(a)

    def _animate(self):
        now = time.monotonic()
        dt = min(0.1, now - self._last)
        self._last = now
        if self._burning() and self.ring_style == "ember":
            frac = self.timer.progress()
            if frac > 0.002 and random.random() < 0.55:       # sparks fly off the ember
                x, y = self._tip_point(frac)
                c = self.SIZE / 2
                ox, oy = (x - c) / self.RING_R, (y - c) / self.RING_R  # outward
                tx, ty = oy, -ox                                     # trailing direction (counter-clockwise)
                sp = random.uniform(8, 20)
                vx = ox * sp + tx * random.uniform(-6, 10) + random.uniform(-3, 3)
                vy = oy * sp + ty * random.uniform(-6, 10) + random.uniform(-3, 3)
                col = random.choice(self.PALETTE[self.timer.kind][:3])
                self._sparks.append([x, y, vx, vy, 0.0, random.uniform(0.35, 0.7), col])
        alive = []
        for sp in self._sparks:
            sp[4] += dt
            if sp[4] < sp[5]:
                sp[0] += sp[2] * dt
                sp[1] += sp[3] * dt
                sp[3] += 18 * dt   # a little gravity
                alive.append(sp)
        self._sparks = alive[-40:]
        if not (self._animated() or self._overrun() or self._sparks):
            self.anim.stop()
        self.update()

    def hop(self):
        """A little 'hey!' bounce before the circle says something."""
        self.hop_anim.stop()
        self.hop_anim.start()

    def _hop_step(self, v):
        v = float(v)
        self._hop_y = -5.0 * abs(math.sin(v * math.pi * 2)) * (1.0 - v)
        self.update()

    def pop_word(self, text, ms=1300):
        """A tiny word bubble just above the circle ("Saved!"): fades in, stays a moment, fades out.
        Mouse clicks pass through it, and it never takes focus."""
        pop = getattr(self, "_pop", None)
        if pop is None:
            pop = self._pop = HintBubble()
            pop.anim = QVariantAnimation(pop)
            pop.anim.setStartValue(0.0)
            pop.anim.setEndValue(1.0)
            pop.anim.valueChanged.connect(self._pop_step)
            pop.anim.finished.connect(pop.hide)
        pop.setText(text)
        g = self.geometry()
        pop._base = QPoint(g.center().x() - pop.width() // 2, g.top() - pop.height() - 2)
        area = screen_for(pop, g.center()).availableGeometry()
        pop._base.setX(max(area.left(), min(pop._base.x(), area.right() - pop.width())))
        pop._base.setY(max(area.top(), pop._base.y()))
        pop.anim.stop()
        pop.anim.setDuration(ms)
        self._pop_step(0.0)
        pop.show()
        apply_share_privacy(pop)
        pop.anim.start()

    def _pop_step(self, v):
        """Fade only: moving a see-through window every frame is what looked jumpy on Windows."""
        pop, v = self._pop, float(v)
        a = min(1.0, v / 0.18) if v < 0.18 else (1.0 if v < 0.72 else max(0.0, (1.0 - v) / 0.28))
        a = a * a * (3 - 2 * a)                 # smoothstep: soft start and end
        pop.setWindowOpacity(round(a, 2))
        if pop.pos() != pop._base:
            pop.move(pop._base)


    # ---- countdown outline styles (all share geometry: the arc runs clockwise from 12 o'clock to the tip)
    def _draw_ember(self, p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c):
        # gradient along the arc: hottest at the burning tip, cooling toward 12 o'clock
        g = QConicalGradient(c, c, 90)
        head = 1.0 - frac
        g.setColorAt(0.0, QColor(base_c))
        g.setColorAt(max(0.0, head - 0.001), QColor(base_c))
        g.setColorAt(head, QColor(tip_c))
        g.setColorAt(min(1.0, head + 0.06), QColor(hot_c))
        g.setColorAt(min(1.0, head + 0.35), QColor(warm_c))
        g.setColorAt(1.0, QColor(base_c))
        flicker = 0.85 + 0.15 * math.sin(now * 11) * math.sin(now * 3.7)
        for width, alpha in ((9, 34), (6, 60)):   # glow layers
            glow = QPen(QColor(hot_c), width)
            glow.setCapStyle(Qt.RoundCap)
            col = QColor(hot_c)
            col.setAlpha(int(alpha * flicker))
            glow.setColor(col)
            p.setPen(glow)
            p.drawArc(ring_rect, 90 * 16, span)
        pen = QPen(g, 2.8)
        pen.setBrush(g)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        p.drawArc(ring_rect, 90 * 16, span)
        # the ember at the tip
        x, y = self._tip_point(frac)
        er = 4.2 + 1.3 * math.sin(now * 13) * math.sin(now * 5.3) + random.uniform(-0.3, 0.3)
        eg = QRadialGradient(x, y, er * 2.2)
        eg.setColorAt(0.0, QColor(255, 255, 255, 250))
        eg.setColorAt(0.25, QColor(tip_c))
        hc = QColor(hot_c)
        hc.setAlpha(150)
        eg.setColorAt(0.55, hc)
        eg.setColorAt(1.0, QColor(0, 0, 0, 0))
        p.setPen(Qt.NoPen)
        p.setBrush(eg)
        p.drawEllipse(QRectF(x - er * 2.2, y - er * 2.2, er * 4.4, er * 4.4))

    def _glow_dot(self, p, x, y, r, core, halo, alpha=150):
        g = QRadialGradient(x, y, r)
        g.setColorAt(0.0, QColor(255, 255, 255, 245))
        g.setColorAt(0.3, QColor(core))
        h = QColor(halo)
        h.setAlpha(alpha)
        g.setColorAt(0.6, h)
        g.setColorAt(1.0, QColor(0, 0, 0, 0))
        p.setPen(Qt.NoPen)
        p.setBrush(g)
        p.drawEllipse(QRectF(x - r, y - r, 2 * r, 2 * r))

    def _draw_comet(self, p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c):
        # tail fades toward 12 o'clock but never vanishes, so the remaining time stays readable
        head = 1.0 - frac
        g = QConicalGradient(c, c, 90)
        dim = QColor(warm_c)
        dim.setAlpha(80)
        g.setColorAt(0.0, dim)
        g.setColorAt(max(0.0, head - 0.001), dim)
        g.setColorAt(head, QColor(tip_c))
        g.setColorAt(min(1.0, head + 0.12), QColor(hot_c))
        g.setColorAt(1.0, dim)
        glow = QColor(hot_c)
        glow.setAlpha(45)
        gp = QPen(glow, 7)
        gp.setCapStyle(Qt.RoundCap)
        p.setPen(gp)
        p.drawArc(ring_rect, int((90 - 360 * frac) * 16), int(min(frac, 0.14) * 360 * 16))   # glow near the head only
        pen = QPen(g, 2.6)
        pen.setBrush(g)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        p.drawArc(ring_rect, 90 * 16, span)
        x, y = self._tip_point(frac)
        pulse = 1.0 + 0.12 * math.sin(now * 4)
        self._glow_dot(p, x, y, 6.5 * pulse, tip_c, hot_c)

    def _draw_neon(self, p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c):
        breath = 0.5 + 0.5 * math.sin(now * 2 * math.pi / 4.0)   # one slow breath every 4 s
        for width, alpha in ((10, 18 + 30 * breath), (6, 40 + 50 * breath)):
            col = QColor(hot_c)
            col.setAlpha(int(alpha))
            gp = QPen(col, width)
            gp.setCapStyle(Qt.RoundCap)
            p.setPen(gp)
            p.drawArc(ring_rect, 90 * 16, span)
        pen = QPen(QColor(tip_c), 2.2)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        p.drawArc(ring_rect, 90 * 16, span)

    def _draw_ticks(self, p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c):
        n = 60
        lit = frac * n
        R = self.RING_R
        for i in range(n):
            a = 2 * math.pi * (i + 0.5) / n
            sx, sy = math.sin(a), -math.cos(a)
            long_ = i % 5 == 0
            r0, r1 = R - (2.6 if long_ else 1.6), R + (2.6 if long_ else 1.6)
            if i + 1 <= lit:
                col = QColor(hot_c if long_ else warm_c)
            elif i < lit:   # the tick being used up right now blinks gently
                col = QColor(tip_c)
                col.setAlpha(int(110 + 145 * (0.5 + 0.5 * math.sin(now * 5))))
            else:
                col = QColor(255, 255, 255, 30)
            pen = QPen(col, 1.6 if long_ else 1.2)
            pen.setCapStyle(Qt.RoundCap)
            p.setPen(pen)
            p.drawLine(QPointF(c + r0 * sx, c + r0 * sy), QPointF(c + r1 * sx, c + r1 * sy))

    def _draw_minimal(self, p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c):
        pen = QPen(QColor(hot_c), 2.2)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        p.drawArc(ring_rect, 90 * 16, span)

    # ---- painting
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.translate(0, self._hop_y)
        S, c, R, B = self.SIZE, self.SIZE / 2, self.RING_R, self.BODY_R
        now = time.monotonic() - self._t0

        # soft drop shadow
        sh = QRadialGradient(c, c + 2, B + 5)
        sh.setColorAt(0.0, QColor(0, 0, 0, 110))
        sh.setColorAt(0.7, QColor(0, 0, 0, 40))
        sh.setColorAt(1.0, QColor(0, 0, 0, 0))
        p.setPen(Qt.NoPen)
        p.setBrush(sh)
        p.drawEllipse(QRectF(c - B - 5, c - B - 3, 2 * (B + 5), 2 * (B + 5)))

        # faint track for the outline, so the circle looks complete when idle
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 34), 2))
        p.drawEllipse(QRectF(c - R, c - R, 2 * R, 2 * R))

        t = self.timer
        ring_rect = QRectF(c - R, c - R, 2 * R, 2 * R)
        if t and t.running and self.timer_display != "hidden":
            frac = max(0.0, min(1.0, t.progress()))
            tip_c, hot_c, warm_c, base_c = self.PALETTE[t.kind]
            span = int(-360 * 16 * frac)
            if t.paused:
                col = QColor(warm_c)
                col.setAlpha(120)
                pen = QPen(col, 2.6)
                pen.setCapStyle(Qt.RoundCap)
                p.setPen(pen)
                p.drawArc(ring_rect, 90 * 16, span)
            elif frac > 0:
                draw = getattr(self, "_draw_" + self.ring_style, self._draw_ember)
                draw(p, c, ring_rect, frac, span, now, tip_c, hot_c, warm_c, base_c)
        elif self._overrun():
            breath = 0.5 + 0.5 * math.sin(now * 3.2)
            for width, alpha in ((9, 30 + 40 * breath), (5, 60 + 60 * breath)):
                col = QColor(C["idea"])
                col.setAlpha(int(alpha))
                p.setPen(QPen(col, width))
                p.drawEllipse(ring_rect)
            p.setPen(QPen(QColor("#ffc15e"), 2.4))
            p.drawEllipse(ring_rect)

        for x, y, _, _, age, life, col in self._sparks:   # sparks
            k = 1.0 - age / life
            cc = QColor(col)
            cc.setAlphaF(max(0.0, k))
            p.setPen(Qt.NoPen)
            p.setBrush(cc)
            r = 0.6 + 1.1 * k
            p.drawEllipse(QRectF(x - r, y - r, 2 * r, 2 * r))

        # body: soft 3D gradient
        _, hi, mid, lo, hov = CIRCLE_COLORS.get(self.body_key(), CIRCLE_COLORS["white"])
        shape = self._body_path(c, B)
        if self.shape == "cloud":   # emoji look: bright top fading to a cool shaded underside, soft drop shadow
            body = QLinearGradient(0, c - 13 * self.scale, 0, c + 11 * self.scale)
            body.setColorAt(0.0, QColor(hov if self._hover else hi))
            body.setColorAt(0.5, QColor(hi))
            body.setColorAt(0.78, QColor(mid))
            body.setColorAt(1.0, QColor(lo))
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(0, 0, 0, 40))
            p.drawPath(shape.translated(0, 1.4 * self.scale))
        else:
            body = QRadialGradient(c - 5 * self.scale, c - 7 * self.scale, B * 1.6)
            body.setColorAt(0.0, QColor(hov if self._hover else hi))
            body.setColorAt(0.55, QColor(mid))
            body.setColorAt(1.0, QColor(lo))
        p.setPen(Qt.NoPen)
        p.setBrush(body)
        p.drawPath(shape)
        p.setBrush(Qt.NoBrush)
        light = self.body_key() == "white"
        # thin rim: a soft grey edge keeps a white body visible on white pages, a light rim on the dark colours
        p.setPen(QPen(QColor(120, 140, 165, 110) if light else QColor(255, 255, 255, 45), 1))
        p.drawPath(self._body_path(c, B - 0.5))

        # status rings outside the timer outline
        if not self.save_ok:
            p.setPen(QPen(QColor(C["idea"]), 1.6, Qt.DashLine))
            p.drawEllipse(QRectF(c - R - 4, c - R - 4, 2 * (R + 4), 2 * (R + 4)))
        if self._drag_hover:
            p.setPen(QPen(QColor("#f3e3c3"), 2, Qt.DashLine))
            p.drawEllipse(ring_rect)

        # The optional digital countdown replaces the note count while a timer is running.
        if t and t.running and self.timer_display == "time":
            left = t.remaining()
            txt = fmt_mmss(left) if left < 100 * 60 else f"{math.ceil(left / 60)}m"
            f = QFont()
            f.setBold(True)
            px = max(7, int(10 * self.scale))
            f.setPixelSize(px)
            while px > max(6, int(7 * self.scale)) and QFontMetrics(f).horizontalAdvance(txt) > B * 1.85:
                px -= 1
                f.setPixelSize(px)
            p.setFont(f)
            p.setPen(QColor("#34465c") if self.body_key() == "white" else QColor("white"))
            p.drawText(QRectF(c - B, c - B, 2 * B, 2 * B), Qt.AlignCenter, txt)
        elif self.show_count and self.count:
            f = QFont()
            f.setBold(True)
            f.setPointSizeF((10.5 if self.count < 100 else 8.5) * self.scale)
            p.setFont(f)
            txt = str(self.count)
            if self.body_key() == "white":   # dark number on the white body, no shadow needed
                p.setPen(QColor("#34465c"))
            else:
                p.setPen(QColor(0, 0, 0, 90))
                p.drawText(QRectF(0, 1, S, S), Qt.AlignCenter, txt)
                p.setPen(QColor("white"))
            p.drawText(QRectF(0, 0, S, S), Qt.AlignCenter, txt)
        elif self.shape != "cloud":   # the cloud reads as a thought bubble on its own; other shapes get a dot
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255, 200))
            p.drawEllipse(QRectF(c - 2.8, c - 2.8, 5.6, 5.6))

    def enterEvent(self, e):
        self._hover = True
        self.fg_at_hover = (foreign_foreground(), time.monotonic())
        self.update()

    def leaveEvent(self, e):
        self._hover = False
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press = e.globalPosition().toPoint()
            self._origin = self.pos()
            self._dragging = False

    def mouseMoveEvent(self, e):
        if self._press is None:
            return
        delta = e.globalPosition().toPoint() - self._press
        if delta.manhattanLength() > 4:
            self._dragging = True
        if self._dragging:
            self.move(self._origin + delta)

    def mouseReleaseEvent(self, e):
        if e.button() != Qt.LeftButton or self._press is None:
            return
        if self._dragging:
            self.moved.emit(self.pos())
        else:
            self.clicked.emit()
        self._press = None

    def contextMenuEvent(self, e):
        menu = self.menu_builder()
        menu.exec(menu_pos_beside(menu, self.geometry()))

    def showEvent(self, e):
        apply_share_privacy(self)
        super().showEvent(e)

    # drops: anything dropped on the circle becomes a task in the current list
    def dragEnterEvent(self, e):
        md = e.mimeData()
        if isinstance(e.source(), AttachmentTile):
            e.ignore()                     # a file on its way out of the shelf, not a new drop
            return
        if md.hasUrls() or md.hasImage() or md.hasText():
            e.acceptProposedAction()
            self._drag_hover = True
            self.update()

    def dragLeaveEvent(self, e):
        self._drag_hover = False
        self.update()

    def dropEvent(self, e):
        self._drag_hover = False
        self.update()
        if self.drop_handler and self.drop_handler(e.mimeData()):
            e.acceptProposedAction()


# ---------------------------------------------------------------- the cloud (circle and app icon)
def cloud_path(c, B):
    """The thought-cloud outline centred on (c, c) with body radius B."""
    path = QPainterPath()
    k = B / 16.0
    path.setFillRule(Qt.WindingFill)
    # emoji-style cloud: a soft flat base, one big puff just right of centre, smaller puffs either side
    path.addRoundedRect(QRectF(c - 15.5 * k, c + 0.5 * k, 31 * k, 10 * k), 5 * k, 5 * k)
    for dx, dy, r in ((-9.5, 2.5, 5.6), (-4.5, -2.5, 6.4), (2.5, -4.5, 8.6), (10, 1.5, 6.0)):
        path.addEllipse(QPointF(c + dx * k, c + dy * k), r * k, r * k)
    path = path.simplified()
    for dx, dy, r in ((-12, 14.5, 3.0), (-16.5, 18.5, 1.9)):   # the thought bubbles trailing off
        path.addEllipse(QPointF(c + dx * k, c + dy * k), r * k, r * k)
    return path


def app_icon():
    """Taskbar / Alt+Tab icon: a white thought cloud on a maroon rounded square (readable on light and dark)."""
    from PySide6.QtGui import QIcon
    icon = QIcon()
    for size in (16, 24, 32, 48, 64, 128, 256):
        pm = QPixmap(size, size)
        pm.fill(Qt.transparent)
        p = QPainter(pm)
        p.setRenderHint(QPainter.Antialiasing)
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(C["accent"]))
        p.drawRoundedRect(QRectF(0, 0, size, size), size * 0.22, size * 0.22)
        p.setBrush(QColor("#ffffff"))
        p.drawPath(cloud_path(size * 0.53, size * 0.36))
        p.end()
        icon.addPixmap(pm)
    return icon


# ---------------------------------------------------------------- attachment tile
class AttachmentTile(QFrame):
    def __init__(self, panel, task, att):
        super().__init__()
        self.panel, self.task, self.att = panel, task, att
        self.path = Store.abs_path(att)
        self.setObjectName("tile")
        self.setFixedSize(62, 62)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(3, 3, 3, 3)
        label = QLabel()
        label.setAlignment(Qt.AlignCenter)
        if att["kind"] == "image" and self.path.exists():
            label.setPixmap(QPixmap(str(self.path)).scaled(54, 54, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        else:
            icon = "\U0001F4C1" if att["kind"] == "folder" else "\U0001F4C4"
            name = att["name"] if len(att["name"]) <= 10 else att["name"][:8] + "…"
            label.setText(f"{icon}\n{name}")
            label.setStyleSheet("font-size: 10px;")
        missing = "" if self.path.exists() else "  (missing)"
        self.setToolTip(f"{att['name']}{missing}\nDrag it out to use it anywhere. Double-click to open. "
                        "Right-click for more.")
        lay.addWidget(label)
        self.copy_btn = QToolButton(self)
        self.copy_btn.setObjectName("copy")
        self.copy_btn.setText("⧉")
        self.copy_btn.setToolTip("Copy to clipboard")
        self.copy_btn.setFixedSize(22, 22)
        self.copy_btn.move(37, 3)
        self.copy_btn.hide()
        self.copy_btn.clicked.connect(self.copy)

    def enterEvent(self, e):
        self.copy_btn.show()
        self.copy_btn.raise_()

    def leaveEvent(self, e):
        self.copy_btn.hide()

    def mouseDoubleClickEvent(self, e):
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.path)))

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press = e.position().toPoint()
            e.accept()
            return
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        """Drag a parked file back out: into a folder, an email, a chat, anywhere that takes files."""
        start = getattr(self, "_press", None)
        if start is None or not (e.buttons() & Qt.LeftButton) or not self.path.exists():
            return
        if (e.position().toPoint() - start).manhattanLength() < QApplication.startDragDistance():
            return
        self._press = None
        from PySide6.QtGui import QDrag
        md = QMimeData()
        md.setUrls([QUrl.fromLocalFile(str(self.path))])
        if self.att["kind"] == "image":
            md.setImageData(QImage(str(self.path)))
        drag = QDrag(self)
        drag.setMimeData(md)
        drag.setPixmap(self.grab().scaled(48, 48, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        drag.exec(Qt.CopyAction)

    def mouseReleaseEvent(self, e):
        self._press = None
        super().mouseReleaseEvent(e)

    def copy(self):
        md = QMimeData()
        if self.att["kind"] == "image":
            md.setImageData(QImage(str(self.path)))
        else:
            md.setUrls([QUrl.fromLocalFile(str(self.path))])
        QGuiApplication.clipboard().setMimeData(md)
        self.copy_btn.setText("✓")
        QTimer.singleShot(900, lambda: self.copy_btn.setText("⧉"))

    def contextMenuEvent(self, e):
        m = QMenu(self)
        m.addAction("Copy", self.copy)
        m.addAction("Open", lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.path))))
        m.addAction("Show in folder", self.reveal)
        m.addSeparator()
        m.addAction("Remove from task", lambda: self.panel.remove_attachment(self.task, self.att))
        m.exec(e.globalPos())

    def reveal(self):
        if sys.platform.startswith("win"):
            subprocess.Popen(["explorer", "/select,", str(self.path)])
        else:
            QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.path.parent)))


# ---------------------------------------------------------------- task card
class RoundCheck(QAbstractButton):
    """Google Tasks style round checkbox."""

    def __init__(self, checked=False):
        super().__init__()
        self.setCheckable(True)
        self.setChecked(checked)
        self.setFixedSize(20, 20)
        self.setCursor(Qt.PointingHandCursor)
        self._hover = False

    def enterEvent(self, e):
        self._hover = True
        self.update()

    def leaveEvent(self, e):
        self._hover = False
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(2, 2, 16, 16)
        if self.isChecked():
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(C["accent"]))
            p.drawEllipse(r)
        else:
            p.setPen(QPen(QColor(C["text"] if self._hover else C["faint"]), 1.6))
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(r)
        if self.isChecked() or self._hover:
            path = QPainterPath(QPointF(6.2, 10.2))
            path.lineTo(8.8, 12.8)
            path.lineTo(13.8, 7.4)
            pen = QPen(QColor("white") if self.isChecked() else QColor(C["faint"]), 1.8)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen)
            p.setBrush(Qt.NoBrush)
            p.drawPath(path)


def edge_jump(ed, e):
    """Up on the first line jumps to the start of the text, Down on the last line to its end.
    Returns True if it moved the cursor (a plain Up/Down with nowhere else to go)."""
    if e.modifiers() not in (Qt.NoModifier, Qt.KeypadModifier) or e.key() not in (Qt.Key_Up, Qt.Key_Down):
        return False
    c = QTextCursor(ed.textCursor())
    up = e.key() == Qt.Key_Up
    if c.movePosition(QTextCursor.Up if up else QTextCursor.Down):
        return False                        # there's another line that way: move normally
    c = ed.textCursor()
    at_edge = c.atStart() if up else c.atEnd()
    if at_edge:
        return False
    ed.moveCursor(QTextCursor.Start if up else QTextCursor.End)
    return True


class AutoText(QTextEdit):
    """Plain-text editor that wraps and grows to fit its content (no inner scrolling).
    single_line: Enter finishes editing instead of adding a line; pasted newlines become spaces."""
    submitted = Signal()

    def __init__(self, text, placeholder="", single_line=False, min_lines=1):
        super().__init__()
        self.single, self.min_lines = single_line, min_lines
        self.setAcceptRichText(False)
        self.setPlainText(text)
        self.setPlaceholderText(placeholder)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setFrameShape(QFrame.NoFrame)
        self.setLineWrapMode(QTextEdit.WidgetWidth)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.setTabChangesFocus(True)
        self.document().setDocumentMargin(2)
        self.document().contentsChanged.connect(self._fit)
        self._fit()

    def _fit(self):
        doc = self.document()
        w = self.viewport().width()
        if w > 20:
            doc.setTextWidth(w)
        min_h = self.fontMetrics().lineSpacing() * self.min_lines + 2 * doc.documentMargin()
        m = self.contentsMargins()
        h = max(min_h, doc.size().height()) + m.top() + m.bottom() + 2
        if self.height() != int(math.ceil(h)):
            self.setFixedHeight(int(math.ceil(h)))

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self._fit()

    def keyPressEvent(self, e):
        if self.single and e.key() in (Qt.Key_Return, Qt.Key_Enter):
            if e.modifiers() & Qt.ShiftModifier:
                self.textCursor().insertText("\n")      # Shift+Enter: a new line in the note
                return
            self.clearFocus()
            self.submitted.emit()
            return
        if edge_jump(self, e):
            return
        super().keyPressEvent(e)

    def insertFromMimeData(self, md):
        if self.single and md.hasText():
            self.insertPlainText(md.text().strip("\n"))
            return
        super().insertFromMimeData(md)

    def wheelEvent(self, e):
        e.ignore()          # the note never scrolls its own text; the wheel goes to the list around it

    def scrollContentsBy(self, dx, dy):
        pass                # it's always as tall as its text, so any inner scroll is a stray jump


class Ghost(QWidget):
    """A picture of a note that moves, scales, turns, tints and fades on its own layer, so each action has its own
    motion while the list underneath closes the gap."""

    def __init__(self, parent, pix, rect, dx, dy, scale, spin, tint, ms):
        super().__init__(parent)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.pix, self.r0 = pix, QRectF(rect)
        self.dx, self.dy, self.scale, self.spin, self.tint, self.ms = dx, dy, scale, spin, QColor(tint), ms
        self.v = 0.0
        self.setGeometry(parent.rect())
        self.anim = QVariantAnimation(self)
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.setDuration(ms)
        self.anim.setEasingCurve(QEasingCurve.OutCubic)
        self.anim.valueChanged.connect(self._step)
        self.anim.finished.connect(self.deleteLater)

    def run(self):
        self.show()
        self.raise_()
        self.anim.start()

    def _step(self, v):
        self.v = float(v)
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        v = self.v
        c = self.r0.center() + QPointF(self.dx * v, self.dy * v)
        sc = 1.0 + (self.scale - 1.0) * v
        p.translate(c)
        p.rotate(self.spin * v)
        p.scale(sc, sc)
        r = QRectF(-self.r0.width() / 2, -self.r0.height() / 2, self.r0.width(), self.r0.height())
        p.setOpacity(max(0.0, 1.0 - v ** 1.4))
        p.drawPixmap(r, self.pix, QRectF(self.pix.rect()))
        t = QColor(self.tint)
        t.setAlpha(int(90 * min(1.0, v * 2.5) * (1.0 - v)))
        p.setPen(Qt.NoPen)
        p.setBrush(t)
        p.drawRoundedRect(r, 10, 10)


class TagPicker(QFrame):
    """The Tags card: every flag as a colored chip in rows of three, lit when on. Click, or Tab and Space.
    Esc or a click outside closes it."""

    def __init__(self, card):
        super().__init__(None, Qt.Popup | Qt.FramelessWindowHint)
        self.card = card
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setObjectName("tagPicker")
        self.setStyleSheet(full_style() + f"""
            QFrame#tagInner {{ background: {C['surface_hi']}; border: 1px solid {C['border']}; border-radius: 12px; }}
            QLabel#tagHead {{ color: {C['dim']}; font-size: 11px; font-weight: 700; }}
            QToolButton#flag {{ padding: 5px 10px; font-size: 12px; }}""")
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        inner = QFrame(self)
        inner.setObjectName("tagInner")
        outer.addWidget(inner)
        v = QVBoxLayout(inner)
        v.setContentsMargins(12, 10, 12, 12)
        v.setSpacing(8)
        head = QLabel("Tags", inner)
        head.setObjectName("tagHead")
        v.addWidget(head)
        grid = QGridLayout()
        grid.setSpacing(6)
        st = card.panel.store.settings
        shown = [(k, i, w, t) for k, i, w, t in FLAG_DEFS if flag_on(st, k)]
        first = None
        for n, (key, icon, word, tip) in enumerate(shown):
            b = QToolButton(inner)
            b.setObjectName("flag")
            b.setProperty("kind", key)
            b.setText(f"{icon}  {word}")
            b.setToolTip(tip)
            b.setCheckable(True)
            b.setChecked(bool(card.task.get(key)))
            b.setCursor(Qt.PointingHandCursor)
            b.setFocusPolicy(Qt.StrongFocus)
            b.toggled.connect(lambda on, k=key: self.card.set_flag(k, on))
            grid.addWidget(b, n // 3, n % 3)
            first = first or b
        v.addLayout(grid)
        self._first = first

    def open_at(self, pos):
        self.adjustSize()
        area = screen_for(self, pos).availableGeometry()
        x = max(area.left(), min(pos.x(), area.right() - self.width()))
        y = pos.y() if pos.y() + self.height() <= area.bottom() else pos.y() - self.height() - 40
        self.move(x, y)
        self.show()
        apply_share_privacy(self)
        if self._first:
            self._first.setFocus()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key_Return, Qt.Key_Enter):
            self.close()
            return
        super().keyPressEvent(e)


def parse_reminder_at(value):
    at = datetime.fromisoformat(value)
    return (at if at.tzinfo else at.astimezone()).astimezone(timezone.utc)


INLINE_REMINDER = re.compile(
    r"(?<!\S)@(?:in[ \t]+)?(?P<amount>[1-9]\d{0,4})[ \t]*"
    r"(?P<unit>minutes?|mins?|m|hours?|hrs?|h|days?|d|weeks?|w)(?=$|[\s,.!?;])", re.I)
BARE_REMINDER = re.compile(
    r"(?<![\w@])(?:in[ \t]+)?(?P<amount>[1-9]\d{0,4})[ \t]*"
    r"(?P<unit>minutes?|mins?|m|hours?|hrs?|h|days?|d|weeks?|w)[ \t]*$", re.I)
CLOCK_REMINDER = re.compile(          # "at 3.05 pm", "at 15:30", "@3pm"; a bare "at 3" is left alone
    r"(?<!\S)(?:at[ \t]+|@)(?P<clock>\d{1,2}(?:[:.]\d{2})?[ \t]*(?:[ap]\.?m\b\.?)?)"
    r"(?=$|[\s,!?;]|\.(?:\s|$))", re.I)


def extract_inline_reminder(text, now=None):
    """Take one time from a note: relative (20m, in 2h) or a clock time (at 3.05 pm: today, else tomorrow).
    Bare relative times only count at the end."""
    now = now or datetime.now(timezone.utc)
    units = {"m": 1, "min": 1, "mins": 1, "minute": 1, "minutes": 1,
             "h": 60, "hr": 60, "hrs": 60, "hour": 60, "hours": 60,
             "d": 1440, "day": 1440, "days": 1440,
             "w": 10080, "week": 10080, "weeks": 10080}

    def found(match, at):
        clean = (text[:match.start()] + text[match.end():]).strip()
        if match.re is not INLINE_REMINDER:
            clean = clean.rstrip(" ,;")
        clean = re.sub(r"[ \t]{2,}", " ", clean)
        clean = re.sub(r"[ \t]+([,.!?;])", r"\1", clean)
        return clean, {"at": at.astimezone(timezone.utc).isoformat(timespec="seconds"), "rings": 3, "interval_min": 1}

    matches = list(INLINE_REMINDER.finditer(text))
    if not matches:
        bare = BARE_REMINDER.search(text)
        matches = [bare] if bare else []
    for match in reversed(matches):
        minutes = int(match.group("amount")) * units[match.group("unit").lower()]
        if 1 <= minutes <= 10080:
            return found(match, now + timedelta(minutes=minutes))
    for match in reversed(list(CLOCK_REMINDER.finditer(text))):
        raw = match.group("clock")
        clock = parse_clock(raw) if re.search(r"[:.ap]", raw, re.I) else None
        if clock:
            local = now.astimezone()
            at = local.replace(hour=clock[0], minute=clock[1], second=0, microsecond=0)
            return found(match, at if at > local else at + timedelta(days=1))
    return text, None


WEEKDAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]


def repeat_text(repeat):
    """'every day', 'weekdays', 'every Mon, Thu', 'every 3 days', 'every month', or '' for none."""
    if not isinstance(repeat, dict):
        return ""
    every = repeat.get("every")
    if every == "day":
        n = max(1, int(repeat.get("n", 1)))
        return "every day" if n == 1 else f"every {n} days"
    if every == "week":
        days = sorted({int(d) for d in repeat.get("days") or [] if 0 <= int(d) <= 6})
        if len(days) == 7:
            return "every day"
        if days == [0, 1, 2, 3, 4]:
            return "weekdays"
        return ("every " + ", ".join(WEEKDAYS[d] for d in days)) if days else ""
    return "every month" if every == "month" else ""


def next_reminder_at(reminder, after=None):
    """The next ring of a repeating reminder after `after` (local, default now), as a UTC iso string, or None.
    Counts from the first scheduled time ("base", kept while snoozed), so snoozes never drift the time of day."""
    repeat = reminder.get("repeat") if isinstance(reminder, dict) else None
    if not repeat_text(repeat):
        return None
    base = parse_reminder_at(reminder.get("base") or reminder["at"]).astimezone().replace(tzinfo=None)
    after = (after or datetime.now()).replace(tzinfo=None)
    at, every = base, repeat["every"]
    if every == "day":
        n = max(1, int(repeat.get("n", 1)))
        if at <= after:
            at += timedelta(days=((after - at).days // n) * n)
        while at <= after:
            at += timedelta(days=n)
    elif every == "week":
        days = {int(d) for d in repeat["days"]}
        if at <= after:
            at += timedelta(days=(after.date() - at.date()).days)
        while at <= after or at.weekday() not in days:
            at += timedelta(days=1)
    else:   # month: same date, or the month's last day when it's shorter (the 31st -> Feb 28)
        dom = int(repeat.get("dom", base.day))
        y, m = (after.year, after.month) if at <= after else (at.year, at.month)
        while True:
            last = ((datetime(y + m // 12, m % 12 + 1, 1)) - timedelta(days=1)).day
            at = datetime(y, m, min(dom, last), base.hour, base.minute)
            if at > after:
                break
            y, m = (y + 1, 1) if m == 12 else (y, m + 1)
    return at.astimezone().astimezone(timezone.utc).isoformat(timespec="seconds")


def reminder_label(reminder):
    if not isinstance(reminder, dict) or not reminder.get("at"):
        return "Remind me"
    try:
        at = parse_reminder_at(reminder["at"]).astimezone()
        rep = repeat_text(reminder.get("repeat"))
        return "Reminder " + ("at " + at.strftime("%I:%M %p").lstrip("0")
                              if at.date() == datetime.now().date()
                              else at.strftime("%b %d, %I:%M %p").replace(" 0", " ")) + (f", {rep}" if rep else "")
    except (ValueError, TypeError):
        return "Remind me"


def reminder_short(reminder):
    """What the reminder chip shows once set: 3:00 PM, Tmrw 9:00 AM, Tue 9:00 AM or Oct 14."""
    try:
        at = parse_reminder_at(reminder["at"]).astimezone()
    except (KeyError, TypeError, ValueError):
        return ""
    days = (at.date() - datetime.now().date()).days
    loop = "↻ " if repeat_text(reminder.get("repeat")) else ""
    if days == 0:
        return loop + clock_text(at)
    if days == 1:
        return loop + "Tmrw " + clock_text(at)
    return loop + ((at.strftime("%a ") + clock_text(at)) if days < 7 else at.strftime("%b %d").replace(" 0", " "))


def reminder_chip(parent, on_click):
    btn = QToolButton(parent)
    btn.setObjectName("remChip")
    btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
    btn.setIconSize(QSize(13, 13))
    btn.setCursor(Qt.PointingHandCursor)
    btn.setFocusPolicy(Qt.StrongFocus)
    btn.setAccessibleName("Remind me")
    btn.clicked.connect(on_click)
    show_reminder_chip(btn, None)
    return btn


def show_reminder_chip(btn, reminder):
    """Bell only while unset; bell and time in the accent color once set."""
    when = reminder_short(reminder) if reminder else ""
    btn.setIcon(line_icon("bell", C["accent_text"] if when else C["dim"]))
    btn.setText(when)
    btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon if when else Qt.ToolButtonIconOnly)
    btn.setProperty("set", bool(when))
    btn.style().unpolish(btn)
    btn.style().polish(btn)
    btn.setToolTip((reminder_label(reminder) + ". Click to change") if when else
                   "Remind me (or type @3pm or 20m in the note)")


def reminder_confirmation(reminder):
    return "\u23f0 Reminder set for " + reminder_label(reminder).removeprefix("Reminder ").removeprefix("at ")


def reminder_tone_wav(kind):
    """A short chime through the normal audio device, independent of Windows theme sounds."""
    notes = {"soft": [(660, 0.16), (880, 0.22)], "peek": [(1047, 0.06), (1397, 0.1)]}.get(
        kind, [(880, 0.15), (1175, 0.15), (988, 0.24)])
    loud = 5000 if kind == "peek" else 11000
    rate = 22050
    samples = bytearray()
    for frequency, duration in notes:
        count = round(duration * rate)
        for i in range(count):
            fade = min(1.0, i / (rate * 0.018), (count - i) / (rate * 0.075))
            value = round(loud * max(0.0, fade) * math.sin(2 * math.pi * frequency * i / rate))
            samples.extend(value.to_bytes(2, "little", signed=True))
        samples.extend(b"\x00\x00" * round(rate * 0.045))
    output = io.BytesIO()
    with wave.open(output, "wb") as wav:
        wav.setnchannels(1)
        wav.setsampwidth(2)
        wav.setframerate(rate)
        wav.writeframes(samples)
    return output.getvalue()


def play_reminder_tone(kind):
    if kind == "mute":
        return True
    try:
        if IS_WIN:
            import winsound
            if kind == "system":
                winsound.MessageBeep(winsound.MB_OK)
            else:
                winsound.PlaySound(reminder_tone_wav(kind), winsound.SND_MEMORY | winsound.SND_NODEFAULT)
        else:
            QApplication.beep()
        return True
    except Exception:
        try:
            if IS_WIN:
                import winsound
                winsound.MessageBeep(winsound.MB_OK)
            else:
                QApplication.beep()
            return True
        except Exception as e:
            log_error(f"note reminder sound failed: {e}")
            return False


def parse_clock(text):
    """'3:30 pm', '3.30 pm', '3pm', '15:30', '930' -> (hour, minute), else None."""
    m = re.fullmatch(r"\s*(\d{1,2})(?:[:.]?(\d{2}))?\s*([ap])?\.?m?\.?\s*", text.lower())
    if not m:
        return None
    hour, minute, half = int(m.group(1)), int(m.group(2) or 0), m.group(3)
    if minute > 59 or hour > 23 or (half and not 1 <= hour <= 12):
        return None
    if half:
        hour = hour % 12 + (12 if half == "p" else 0)
    return hour, minute


def clock_text(at):
    return at.strftime("%I:%M %p").lstrip("0")


class ReminderDialog(QDialog):
    """The reminder card: one click on a quick time sets it; or pick a day and a time (type one too, like
    3:30 pm or 20m). Opens beside the button that asked for it. Enter sets, Esc or a click outside cancels."""

    QUICK = [("15 min", 15), ("30 min", 30), ("1 hour", 60), ("3 hours", 180), ("Tonight", "tonight"),
             ("Tomorrow", "tomorrow")]
    DAYS_AHEAD = 14

    def __init__(self, current=None, parent=None):
        super().__init__(parent, Qt.Popup | Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.removed = False
        self.setStyleSheet(full_style() + f"""
            QFrame#remInner {{ background: {C['surface_hi']}; border: 1px solid {C['border']}; border-radius: 12px; }}
            QLabel#remHead {{ color: {C['text']}; font-size: 13px; font-weight: 700; }}
            QLabel#remSub {{ color: {C['dim']}; font-size: 11px; font-weight: 700; }}
            QLabel#remPreview {{ color: {C['dim']}; font-size: 12px; }}
            QLabel#remPreview[bad="true"] {{ color: {C['anti']}; }}
            QPushButton#quick {{ background: {C['surface']}; border: 1px solid {C['border']}; border-radius: 9px;
                padding: 6px 4px; font-size: 12px; min-width: 72px; }}
            QPushButton#quick:hover, QPushButton#quick:focus {{ background: {C['accent_soft']};
                border-color: {C['accent']}; color: white; }}
            QComboBox {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
                border-radius: 8px; padding: 5px 8px; font-size: 12px; }}
            QComboBox:hover, QComboBox:focus {{ border-color: {C['faint']}; }}
            QComboBox::drop-down {{ border: none; width: 18px; }}
            QComboBox QAbstractItemView {{ background: {C['surface_hi']}; color: {C['text']};
                border: 1px solid {C['border']}; selection-background-color: {C['accent']}; outline: none; }}
            QComboBox QLineEdit {{ background: transparent; border: none; padding: 0; }}
            QPushButton#setRem {{ background: {C['accent']}; border: 1px solid {C['accent']}; color: white;
                border-radius: 8px; padding: 6px 14px; font-weight: 700; }}
            QPushButton#setRem:hover {{ background: #b54552; }}
            QPushButton#setRem:disabled {{ background: {C['surface']}; border-color: {C['border']}; color: {C['faint']}; }}
            QPushButton#removeRem {{ background: transparent; border: none; color: {C['faint']}; padding: 6px 4px; }}
            QPushButton#removeRem:hover {{ color: {C['anti']}; }}""")
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        inner = QFrame(self)
        inner.setObjectName("remInner")
        outer.addWidget(inner)
        v = QVBoxLayout(inner)
        v.setContentsMargins(14, 12, 14, 12)
        v.setSpacing(8)
        hrow = QHBoxLayout()
        hrow.setSpacing(7)
        bell = QLabel(inner)
        bell.setPixmap(line_icon("bell", C["accent_text"]).pixmap(15, 15))
        hrow.addWidget(bell)
        head = QLabel("Change reminder" if current else "Remind me", inner)
        head.setObjectName("remHead")
        hrow.addWidget(head)
        hrow.addStretch(1)
        keys = QLabel("1 to 6 pick", inner)
        keys.setObjectName("remSub")
        hrow.addWidget(keys)
        v.addLayout(hrow)

        grid = QGridLayout()
        grid.setSpacing(6)
        self.chips = []
        now = datetime.now()
        quick = [(label, when) for label, when in self.QUICK if self._quick_at(when, now)]
        for n, (label, when) in enumerate(quick):
            b = QPushButton(inner)
            b.setObjectName("quick")
            at = self._quick_at(when, now)
            b.setText(label if isinstance(when, int) else f"{label} {clock_text(at)}")
            b.setToolTip(at.strftime("%a %b %d, ").replace(" 0", " ") + clock_text(at) + f" (key {n + 1})")
            b.setCursor(Qt.PointingHandCursor)
            b.setAutoDefault(False)
            b.clicked.connect(lambda _=False, w=when: self._pick_quick(w))
            grid.addWidget(b, n // 3, n % 3)
            self.chips.append(b)
        v.addLayout(grid)

        sub = QLabel("Or pick a day and time", inner)
        sub.setObjectName("remSub")
        v.addWidget(sub)
        row = QHBoxLayout()
        row.setSpacing(6)
        self.day = QComboBox(inner)
        today = now.date()
        for i in range(self.DAYS_AHEAD):
            d = today + timedelta(days=i)
            self.day.addItem("Today" if i == 0 else "Tomorrow" if i == 1 else d.strftime("%a, %b %d").replace(" 0", " "),
                             d)
        self.time = QComboBox(inner)
        self.time.setEditable(True)
        self.time.setInsertPolicy(QComboBox.NoInsert)
        self.time.lineEdit().setPlaceholderText("3:30 pm or 20m")
        for minutes in range(0, 24 * 60, 15):
            self.time.addItem(clock_text(datetime(2000, 1, 1, minutes // 60, minutes % 60)))
        self.time.setMaxVisibleItems(10)
        row.addWidget(self.day, 3)
        row.addWidget(self.time, 2)
        v.addLayout(row)
        self.preview = QLabel(inner)
        self.preview.setObjectName("remPreview")
        v.addWidget(self.preview)

        again = QHBoxLayout()
        again.setSpacing(6)
        again_label = QLabel("Repeat", inner)
        again_label.setObjectName("remSub")
        self.repeat = QComboBox(inner)
        self.repeat.setAccessibleName("Repeat")
        for key, label in self.REPEATS:
            self.repeat.addItem(label, key)
        self.every_n = QSpinBox(inner)
        self.every_n.setRange(2, 365)
        self.every_n.setValue(2)
        self.every_n.setPrefix("every ")
        self.every_n.setSuffix(" days")
        self.every_n.setAccessibleName("Repeat every how many days")
        again.addWidget(again_label)
        again.addWidget(self.repeat, 1)
        again.addWidget(self.every_n)
        v.addLayout(again)
        self.day_row = QWidget(inner)
        dr = QHBoxLayout(self.day_row)
        dr.setContentsMargins(0, 0, 0, 0)
        dr.setSpacing(3)
        self.day_btns = []
        for name in WEEKDAYS:
            b = QPushButton(name[:2], self.day_row)
            b.setObjectName("quick")
            b.setCheckable(True)
            b.setAutoDefault(False)
            b.setStyleSheet("min-width: 30px; padding: 4px 2px;")
            b.setAccessibleName(name)
            dr.addWidget(b)
            self.day_btns.append(b)
        v.addWidget(self.day_row)

        rep = QHBoxLayout()
        rep.setSpacing(6)
        ring_label = QLabel("Ring", inner)
        ring_label.setObjectName("remSub")
        self.rings = QComboBox(inner)
        for count in (1, 3, 5):
            self.rings.addItem("once" if count == 1 else f"{count} times", count)
        self.interval = QComboBox(inner)
        for minutes in (1, 5, 10):
            self.interval.addItem(f"every {minutes} min", minutes)
        rep.addWidget(ring_label)
        rep.addWidget(self.rings, 1)
        rep.addWidget(self.interval, 1)
        v.addLayout(rep)

        foot = QHBoxLayout()
        self.remove_btn = QPushButton("Remove", inner)
        self.remove_btn.setObjectName("removeRem")
        self.remove_btn.setCursor(Qt.PointingHandCursor)
        self.remove_btn.setAutoDefault(False)
        self.remove_btn.clicked.connect(self._remove)
        self.remove_btn.setVisible(bool(current))
        foot.addWidget(self.remove_btn)
        foot.addStretch(1)
        self.set_btn = QPushButton("Set reminder", inner)
        self.set_btn.setObjectName("setRem")
        self.set_btn.setCursor(Qt.PointingHandCursor)
        self.set_btn.setDefault(True)
        self.set_btn.clicked.connect(self._accept_valid)
        foot.addWidget(self.set_btn)
        v.addLayout(foot)

        start = now + timedelta(hours=1)
        if current:
            try:
                start = parse_reminder_at(current["at"]).astimezone().replace(tzinfo=None)
            except (KeyError, TypeError, ValueError):
                pass
            self.rings.setCurrentIndex(max(0, self.rings.findData(current.get("rings", 3))))
            self.interval.setCurrentIndex(max(0, self.interval.findData(current.get("interval_min", 1))))
            self._show_repeat(current.get("repeat"))
        else:
            self.rings.setCurrentIndex(1)
            start += timedelta(minutes=-start.minute % 15)       # next quarter hour, an hour from now
            start = start.replace(second=0, microsecond=0)
        self._set_when(start)
        self.day.currentIndexChanged.connect(self._update)
        self.time.currentTextChanged.connect(self._update)
        self.rings.currentIndexChanged.connect(self._update)
        self.repeat.currentIndexChanged.connect(self._update)
        for b in self.day_btns:
            b.toggled.connect(self._update)
        self.every_n.valueChanged.connect(self._update)
        self._update()

    REPEATS = [("", "Does not repeat"), ("day", "Every day"), ("weekdays", "Weekdays, Mon to Fri"),
               ("week", "Every week, same day"), ("days", "On these days"), ("ndays", "Every few days"),
               ("month", "Every month, same date")]

    def _show_repeat(self, repeat):
        """Put a saved repeat back into the Repeat row."""
        text = repeat_text(repeat)
        key = ""
        if text:
            every, days = repeat["every"], sorted(repeat.get("days") or [])
            if every == "day":
                key = "day" if text == "every day" else "ndays"
                self.every_n.setValue(max(2, int(repeat.get("n", 2))))
            elif every == "month":
                key = "month"
            else:
                key = "weekdays" if days == [0, 1, 2, 3, 4] else "day" if len(days) == 7 else "days"
                for d, b in enumerate(self.day_btns):
                    b.setChecked(d in days)
        self.repeat.setCurrentIndex(max(0, self.repeat.findData(key)))

    def repeat_value(self, at):
        """The chosen repeat as stored on the reminder, or None."""
        key = self.repeat.currentData()
        if key == "day":
            return {"every": "day", "n": 1}
        if key == "ndays":
            return {"every": "day", "n": self.every_n.value()}
        if key == "weekdays":
            return {"every": "week", "days": [0, 1, 2, 3, 4]}
        if key == "week":
            return {"every": "week", "days": [at.weekday()]}
        if key == "days":
            return {"every": "week", "days": [d for d, b in enumerate(self.day_btns) if b.isChecked()] or [at.weekday()]}
        if key == "month":
            return {"every": "month", "dom": at.day}
        return None

    @staticmethod
    def _quick_at(when, now):
        if isinstance(when, int):
            return now + timedelta(minutes=when)
        if when == "tonight":                         # gone after about 7:30 PM, so it never means tomorrow
            at = now.replace(hour=20, minute=0, second=0, microsecond=0)
            return at if at > now + timedelta(minutes=30) else None
        return (now + timedelta(days=1)).replace(hour=9, minute=0, second=0, microsecond=0)

    def _set_when(self, at):
        # findData can't match a Python date, which added a second "today" row with the year
        i = next((k for k in range(self.day.count()) if self.day.itemData(k) == at.date()), -1)
        if i < 0:
            self.day.addItem(at.strftime("%a, %b %d %Y").replace(" 0", " "), at.date())
            i = self.day.count() - 1
        self.day.setCurrentIndex(i)
        self.time.setEditText(clock_text(at))

    def chosen_at(self):
        """The local time the day and time fields point at, or None when the time can't be read."""
        text = self.time.currentText().strip()
        now = datetime.now()
        _, relative = extract_inline_reminder(text) if text else (text, None)
        if relative:
            return parse_reminder_at(relative["at"]).astimezone().replace(tzinfo=None)
        clock = parse_clock(text)
        if not clock:
            return None
        day = self.day.currentData()
        at = datetime(day.year, day.month, day.day, *clock)
        if self.day.currentIndex() == 0 and at <= now:
            at += timedelta(days=1)                   # a time already gone today means tomorrow
        return at

    def _update(self):
        at = self.chosen_at()
        now = datetime.now()
        ok = at is not None and at > now
        if at is None:
            text = "Type a time like 3:30 pm, or 20m"
        else:
            days = (at.date() - now.date()).days
            day = "Today" if days == 0 else "Tomorrow" if days == 1 else at.strftime("%a, %b %d").replace(" 0", " ")
            text = f"{day} at {clock_text(at)}, in {short_span((at - now).total_seconds())}"
            rep = repeat_text(self.repeat_value(at))
            if rep:
                text += f". Then {rep}"
        key = self.repeat.currentData()
        if self.every_n.isHidden() != (key != "ndays") or self.day_row.isHidden() != (key != "days"):
            self.every_n.setVisible(key == "ndays")
            self.day_row.setVisible(key == "days")
            if self.isVisible():
                self.adjustSize()
        self.preview.setText(text)
        self.preview.setProperty("bad", not ok)
        self.preview.style().unpolish(self.preview)
        self.preview.style().polish(self.preview)
        self.set_btn.setEnabled(ok)
        self.interval.setEnabled(self.rings.currentData() != 1)

    def _pick_quick(self, when):
        self._set_when(self._quick_at(when, datetime.now()))
        self.accept()

    def _remove(self):
        self.removed = True
        self.accept()

    def _accept_valid(self):
        at = self.chosen_at()
        if at and at > datetime.now():
            self.accept()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key_Return, Qt.Key_Enter):
            self._accept_valid()
            return
        n = e.key() - Qt.Key_1
        if 0 <= n < len(self.chips) and not self.time.hasFocus():
            self.chips[n].click()
            return
        super().keyPressEvent(e)

    def open_at(self, anchor=None):
        self.adjustSize()
        if anchor is not None and anchor.isVisible():
            pos = anchor.mapToGlobal(QPoint(0, anchor.height() + 4))
            above = anchor.height() + 8
        else:
            pos = QCursor.pos() + QPoint(-self.width() // 2, 12)
            above = 24
        area = screen_for(self, pos).availableGeometry()
        x = max(area.left(), min(pos.x(), area.right() - self.width()))
        y = pos.y() if pos.y() + self.height() <= area.bottom() else max(area.top(), pos.y() - self.height() - above)
        self.move(x, y)

    def showEvent(self, e):
        apply_share_privacy(self)
        self.time.setFocus()
        self.time.lineEdit().selectAll()
        super().showEvent(e)

    def value(self):
        at = self.chosen_at() or datetime.now() + timedelta(hours=1)
        value = {"at": at.astimezone().astimezone(timezone.utc).isoformat(timespec="seconds"),
                 "rings": self.rings.currentData(), "interval_min": self.interval.currentData()}
        repeat = self.repeat_value(at)
        if repeat:
            value["repeat"] = repeat
        return value


class AskDialog(QDialog):
    """The app's own small question card, in place of Qt's plain input box: a heading, optional quick
    choices and one field. Enter saves, Esc or a click outside cancels. With `limits` the field takes a
    whole number in that range."""

    def __init__(self, title, value="", parent=None, chips=(), unit="", limits=None):
        super().__init__(parent, Qt.Popup | Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.limits = limits
        self.setStyleSheet(full_style() + f"""
            QFrame#askInner {{ background: {C['surface_hi']}; border: 1px solid {C['border']}; border-radius: 12px; }}
            QLabel#askHead {{ color: {C['text']}; font-size: 13px; font-weight: 700; }}
            QLabel#askUnit {{ color: {C['dim']}; font-size: 12px; }}
            QPushButton#quick {{ background: {C['surface']}; border: 1px solid {C['border']}; border-radius: 9px;
                padding: 6px 8px; font-size: 12px; min-width: 36px; }}
            QPushButton#quick:hover, QPushButton#quick:focus {{ background: {C['accent_soft']};
                border-color: {C['accent']}; color: white; }}
            QPushButton#askOk {{ background: {C['accent']}; border: 1px solid {C['accent']}; color: white;
                border-radius: 8px; padding: 6px 14px; font-weight: 700; }}
            QPushButton#askOk:hover {{ background: #b54552; }}""")
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        inner = QFrame(self)
        inner.setObjectName("askInner")
        outer.addWidget(inner)
        v = QVBoxLayout(inner)
        v.setContentsMargins(14, 12, 14, 12)
        v.setSpacing(8)
        head = QLabel(title, inner)
        head.setObjectName("askHead")
        v.addWidget(head)
        self.chips = []
        if chips:
            row = QHBoxLayout()
            row.setSpacing(5)
            for chip in chips:
                b = QPushButton(str(chip), inner)
                b.setObjectName("quick")
                b.setAutoDefault(False)
                b.setCursor(Qt.PointingHandCursor)
                b.clicked.connect(lambda _=False, c=chip: (self.field.setText(str(c)), self.accept()))
                row.addWidget(b)
                self.chips.append(b)
            row.addStretch(1)
            v.addLayout(row)
        row = QHBoxLayout()
        row.setSpacing(6)
        self.field = QLineEdit(str(value), inner)
        self.field.setMinimumWidth(70 if limits else 220)
        self.field.setAccessibleName(title)
        row.addWidget(self.field, 1)
        if unit:
            u = QLabel(unit, inner)
            u.setObjectName("askUnit")
            row.addWidget(u)
        self.ok_btn = QPushButton("Save", inner)
        self.ok_btn.setObjectName("askOk")
        self.ok_btn.setDefault(True)
        self.ok_btn.clicked.connect(self._save)
        row.addWidget(self.ok_btn)
        v.addLayout(row)

    def value(self):
        text = self.field.text().strip()
        if self.limits is None:
            return text or None
        try:
            n = int(text)
        except ValueError:
            return None
        return n if self.limits[0] <= n <= self.limits[1] else None

    def _save(self):
        if self.value() is None:
            self.field.setFocus()
            self.field.selectAll()
            return
        self.accept()

    def showEvent(self, e):
        apply_share_privacy(self)
        self.field.setFocus()
        self.field.selectAll()
        super().showEvent(e)


DRIFT_TIP = ("Drifted off (phone, a rabbit hole)? Take those minutes out of this round, "
             "so only real focus is logged. The timer keeps going.")


def take_out_drift(timer, parent):
    """Ask how many minutes you drifted and take them out of the running focus round."""
    most = timer.drifted_max()
    if most < 1:
        QToolTip.showText(QCursor.pos(), "Nothing to take out yet. Less than a minute of focus so far.")
        return 0
    minutes = ask(parent, "Minutes you drifted", min(5, most), [c for c in (2, 5, 10, 15) if c <= most],
                  "min", (1, most))
    return timer.take_out(minutes) if minutes else 0


def ask(parent, title, value="", chips=(), unit="", limits=None):
    """Show an AskDialog over `parent` (or by the mouse) and return the answer, or None if cancelled."""
    dlg = AskDialog(title, value, parent, chips, unit, limits)
    dlg.adjustSize()
    win = parent.window() if parent is not None and parent.isVisible() else None
    pos = (win.geometry().center() if win else QCursor.pos()) - QPoint(dlg.width() // 2, dlg.height() // 2)
    area = screen_for(dlg, pos).availableGeometry()
    dlg.move(max(area.left(), min(pos.x(), area.right() - dlg.width())),
             max(area.top(), min(pos.y(), area.bottom() - dlg.height())))
    answer = dlg.value() if dlg.exec() == QDialog.Accepted else None
    dlg.deleteLater()
    return answer


def edit_reminder(parent, current=None, anchor=None):
    dialog = ReminderDialog(current, parent)
    dialog.open_at(anchor)
    if dialog.exec() != QDialog.Accepted:
        return False, current
    return True, None if dialog.removed else dialog.value()


class ReminderAlert(QDialog):
    """A persistent note card grows from the cloud until dismissed or snoozed."""

    def __init__(self, task, settings, answered, bubble=None, note_actions=False):
        super().__init__(None, Qt.FramelessWindowHint | Qt.Tool | Qt.WindowStaysOnTopHint)
        self.task, self.settings, self.answered, self.bubble = task, settings, answered, bubble
        self.setWindowTitle("Note reminder")
        self.setObjectName("reminderAlert")
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.tail_right = True
        self.show_tail = True
        self._tail_y = 40
        self.setStyleSheet(f"""
            QDialog#reminderAlert {{ background: transparent; border: none; }}
            QDialog#reminderAlert QLabel {{ color: {C['text']}; }}
            QDialog#reminderAlert QPushButton {{ background: {C['surface_hi']}; color: {C['text']};
                border: 1px solid {C['border']}; border-radius: 7px; padding: 5px 10px; }}
            QDialog#reminderAlert QPushButton:hover {{ background: {C['accent_soft']}; }}
            QDialog#reminderAlert QPushButton#snoozeDefault {{ background: {C['accent']}; color: white;
                border-color: {C['accent']}; }}
            QDialog#reminderAlert QPushButton:focus {{ border-color: {C['text']}; }}
            QDialog#reminderAlert QPushButton#stopRem {{ background: transparent; border: none; color: {C['dim']}; }}
            QDialog#reminderAlert QPushButton#stopRem:hover {{ color: {C['anti']}; }}
        """)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(22, 17, 28, 18)
        lay.setSpacing(8)
        repeat = repeat_text((task.get("reminder") or {}).get("repeat"))
        heading = QLabel("Note reminder" + (f" · repeats {repeat}" if repeat else ""), self)
        heading.setStyleSheet(f"color: {C['accent_text']}; font-size: 12px; font-weight: 700;")
        lay.addWidget(heading)
        title_row = QHBoxLayout()
        title_row.setSpacing(9)
        self.face = EmojiFace(34)
        self.face.set("\u23f0", "bounce")
        title_row.addWidget(self.face, 0, Qt.AlignTop)
        title = QLabel(task.get("title", "Untitled"), self)
        title.setTextFormat(Qt.PlainText)
        title.setWordWrap(True)
        f = title.font()
        f.setBold(True)
        f.setPointSize(max(11, f.pointSize() + 2))
        title.setFont(f)
        title_row.addWidget(title, 1)
        lay.addLayout(title_row)
        if task.get("desc", "").strip():
            details = QLabel(task["desc"], self)
            details.setTextFormat(Qt.PlainText)
            details.setWordWrap(True)
            details.setTextInteractionFlags(Qt.TextSelectableByMouse)
            scroll = QScrollArea(self)
            scroll.setWidget(details)
            scroll.setWidgetResizable(True)
            scroll.setMaximumHeight(180)
            scroll.setFrameShape(QFrame.NoFrame)
            scroll.setStyleSheet("background: transparent; border: none;")
            lay.addWidget(scroll)
        lay.addWidget(QLabel("Snooze for", self))
        row = QHBoxLayout()
        times = []
        self.snooze_buttons = []
        for key, default in (("reminder_snooze_1", 5), ("reminder_snooze_2", 10), ("reminder_snooze_3", 30)):
            try:
                minutes = max(1, int(settings.get(key, default)))
            except (ValueError, TypeError):
                minutes = default
            if minutes not in times:
                times.append(minutes)
                button = QPushButton(f"{minutes} min", self)
                button.clicked.connect(lambda _=False, m=minutes: self._answer(m))
                row.addWidget(button)
                self.snooze_buttons.append(button)
        lay.addLayout(row)
        primary = self.snooze_buttons[min(1, len(self.snooze_buttons) - 1)]
        primary.setObjectName("snoozeDefault")
        primary.setDefault(True)
        self.default_snooze = times[self.snooze_buttons.index(primary)]
        actions = QHBoxLayout()
        actions.setSpacing(6)
        self.open_button = self.done_button = None
        if note_actions:
            self.open_button = QPushButton("&Open note", self)
            self.open_button.setToolTip("Show it in the list (Alt+O)")
            self.open_button.clicked.connect(lambda: self._answer("open"))
            self.done_button = QPushButton("&Done this time" if repeat else "&Done", self)
            self.done_button.setToolTip("It comes back next time; the note stays open (Alt+D)" if repeat
                                        else "Tick it off (Alt+D)")
            self.done_button.clicked.connect(lambda: self._answer("done"))
            for b in (self.open_button, self.done_button):
                b.setAutoDefault(False)
                actions.addWidget(b)
        actions.addStretch(1)
        dismiss = QPushButton("Skip this one" if repeat else "Stop reminder", self)
        if repeat:
            dismiss.setToolTip("To stop it for good, open the note's reminder and press Remove")
        dismiss.setObjectName("stopRem")
        dismiss.setAutoDefault(False)
        dismiss.clicked.connect(lambda: self._answer(0))
        actions.addWidget(dismiss)
        lay.addLayout(actions)
        self.dismiss_button = dismiss
        self.repeat_timer = QTimer(self)
        self.repeat_timer.timeout.connect(self._ring)
        self.ring_count = 0
        self.max_rings = max(1, min(20, int(task.get("reminder", {}).get("rings", 3))))
        self.repeat_timer.setInterval(max(1, int(task.get("reminder", {}).get("interval_min", 1))) * 60000)
        self._resolved = False
        self.anim = QVariantAnimation(self)
        self.anim.setStartValue(0.0)
        self.anim.setEndValue(1.0)
        self.anim.setDuration(420)
        self.anim.setEasingCurve(QEasingCurve.OutBack)
        self.anim.valueChanged.connect(self._step)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = (QRectF(self.rect()).adjusted(1, 1, -10, -1) if self.tail_right else
             QRectF(self.rect()).adjusted(10, 1, -1, -1))
        path = QPainterPath()
        path.addRoundedRect(r, 15, 15)
        cy = min(r.bottom() - 19, max(r.top() + 19, self._tail_y))
        tail = QPainterPath()
        if self.tail_right:
            tail.moveTo(r.right() - 1, cy - 9)
            tail.lineTo(r.right() + 9, cy)
            tail.lineTo(r.right() - 1, cy + 9)
        else:
            tail.moveTo(r.left() + 1, cy - 9)
            tail.lineTo(r.left() - 9, cy)
            tail.lineTo(r.left() + 1, cy + 9)
        p.setBrush(QColor(C["surface_hi"]))
        p.setPen(QPen(QColor(C["accent"]), 1.6))
        p.drawPath(path.united(tail) if self.show_tail else path)

    def show_from_cloud(self):
        circle = self.bubble.geometry() if self.bubble and self.bubble.isVisible() else None
        self.show_tail = bool(circle)
        area = screen_for(self, circle.center() if circle else QCursor.pos()).availableGeometry()
        width = min(430, max(300, area.width() - 20))
        self.setFixedWidth(width)
        self.layout().activate()
        height = max(self.sizeHint().height(), self.layout().minimumSize().height()) + 4
        self.setFixedHeight(min(height, area.height() - 12))
        if circle:
            self.tail_right = circle.center().x() > area.center().x()
            self.layout().setContentsMargins(22 if self.tail_right else 28, 17,
                                             28 if self.tail_right else 22, 18)
            x = circle.left() - self.width() - 3 if self.tail_right else circle.right() + 3
            y = circle.center().y() - self.height() // 2
            self.bubble.hop()
        else:
            x = area.center().x() - self.width() // 2
            y = area.center().y() - self.height() // 2
        x = max(area.left() + 3, min(x, area.right() - self.width() - 3))
        y = max(area.top() + 3, min(y, area.bottom() - self.height() - 3))
        self._tail_y = circle.center().y() - y if circle else self.height() // 2
        self._final = QRect(x, y, self.width(), self.height())
        self._origin = (QRect(circle.center().x() - 12, circle.center().y() - 12, 24, 24)
                        if circle else self._final)
        self.setMinimumSize(0, 0)
        self.setMaximumSize(16777215, 16777215)
        self.setGeometry(self._origin)
        self.setWindowOpacity(0.0 if circle else 1.0)
        self.show()
        apply_share_privacy(self)
        if circle:
            self.anim.start()

    def _step(self, value):
        v = float(value)
        a, b = self._origin, self._final
        lerp = lambda p, q: int(p + (q - p) * v)
        self.setGeometry(QRect(lerp(a.x(), b.x()), lerp(a.y(), b.y()),
                               max(24, lerp(a.width(), b.width())), max(24, lerp(a.height(), b.height()))))
        self.setWindowOpacity(max(0.0, min(1.0, v * 1.4)))

    def showEvent(self, event):
        super().showEvent(event)
        apply_share_privacy(self)
        if not self.ring_count:
            self._ring()
            if self.ring_count < self.max_rings:
                self.repeat_timer.start()

    def _ring(self):
        self.ring_count += 1
        tone = self.settings.get("reminder_tone", "soft")
        if tone != "mute":
            if IS_WIN:
                threading.Thread(target=play_reminder_tone, args=(tone,), daemon=True).start()
            else:
                play_reminder_tone(tone)
        if self.ring_count >= self.max_rings:
            self.repeat_timer.stop()

    def _answer(self, snooze_minutes):
        self._resolved = True
        self.repeat_timer.stop()
        try:
            self.answered(self.task, snooze_minutes)
        finally:
            self.anim.stop()
            self.hide()

    def reject(self):
        """Esc, or closed without a choice: snooze, never lose it. QDialog.closeEvent calls this and refuses
        the close if the card is still visible, so it must hide here, never call close() again."""
        if self._resolved:
            self.anim.stop()
            self.hide()
        else:
            self._answer(self.default_snooze)


class NoteAlarmManager(QObject):
    def __init__(self, store, parent=None, on_change=None, bubble=None, panel=None):
        super().__init__(parent)
        self.store, self.panel = store, panel
        self.on_change = on_change or (lambda: None)
        self.bubble = bubble
        self.active = {}
        self.timer = QTimer(self)
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self.check_due)
        self.timer.start()

    def check_due(self):
        for task_id, alert in list(self.active.items()):
            if alert.task.get("done") or not alert.task.get("reminder"):
                alert._resolved = True
                alert.close()
                self.active.pop(task_id, None)
        if self.active:
            return  # show one note at a time, so none is hidden behind another
        now = datetime.now(timezone.utc)
        for task in self.store.all_tasks():
            reminder = task.get("reminder")
            if task.get("done") or not isinstance(reminder, dict) or task["id"] in self.active:
                continue
            try:
                due = parse_reminder_at(reminder["at"])
            except (KeyError, ValueError, TypeError):
                continue
            if due <= now:
                alert = ReminderAlert(task, self.store.settings, self._answered, self.bubble, bool(self.panel))
                self.active[task["id"]] = alert
                alert.show_from_cloud()
                QTimer.singleShot(0, lambda a=alert: a._resolved or force_foreground(a))
                break

    def _answered(self, task, snooze_minutes):
        """snooze_minutes: minutes to snooze, 0 to stop, or "open" / "done" (both also stop it). A repeating
        reminder never stops here: it moves on to its next time, and "done" leaves the note open."""
        self.active.pop(task["id"], None)
        reminder = task.get("reminder") or {}
        repeats = bool(repeat_text(reminder.get("repeat")))
        if isinstance(snooze_minutes, int) and snooze_minutes:
            if repeats:
                reminder.setdefault("base", reminder["at"])
            reminder["at"] = (datetime.now(timezone.utc) + timedelta(minutes=snooze_minutes)).isoformat(timespec="seconds")
        elif repeats:
            reminder["at"] = next_reminder_at(reminder)
            reminder.pop("base", None)
        else:
            task.pop("reminder", None)
        self.store.save()
        self.on_change()
        if snooze_minutes == "done" and self.panel and not repeats:
            self.panel.set_done(task, True)
        elif snooze_minutes == "open" and self.panel:
            self.panel.open_task(task)


class TaskCard(QFrame):
    """One task: title (wraps), details (shown when there are any), attachments.
    Clicking the title makes the task active: the flag toggles, an 'Add details' line and a paste/drop hint
    appear on that one task only. Later / Let go float in on hover, so nothing shifts while the mouse moves."""

    def __init__(self, panel, task, idx, total):
        super().__init__()
        self.panel, self.task = panel, task
        self.setObjectName("card")
        self.setAcceptDrops(True)
        self.setFocusPolicy(Qt.ClickFocus)   # "selected" = the card itself has focus (keyboard browsing)
        self.setProperty("done", bool(task["done"]))
        outer = QHBoxLayout(self)
        self.outer = outer
        outer.setContentsMargins(10, 9, 10, 9)
        outer.setSpacing(9)

        chk = RoundCheck(task["done"])
        chk.setToolTip("Mark done" if not task["done"] else "Mark not done")
        chk.toggled.connect(lambda on: panel.set_done(task, on))
        outer.addWidget(chk, 0, Qt.AlignTop)

        body = QVBoxLayout()
        body.setSpacing(3)
        body.setContentsMargins(0, 0, 0, 0)
        outer.addLayout(body, 1)

        self.chip_row = QWidget()
        cr = QHBoxLayout(self.chip_row)
        cr.setContentsMargins(0, 0, 0, 0)
        cr.setSpacing(5)
        self.chips = {}
        for key in FLAG_KEYS:
            text, tip, kind = FLAG_CHIPS[key]
            chip = QLabel(text)
            chip.setObjectName("chip")
            chip.setProperty("kind", kind)
            chip.setToolTip(tip)
            cr.addWidget(chip)
            self.chips[key] = chip
        cr.addStretch(1)
        body.addWidget(self.chip_row)

        self.title = AutoText(task["title"], "Untitled", single_line=True)
        self.title.setObjectName("title")
        self.title.textChanged.connect(self._on_title)
        if task["done"]:
            f = self.title.font()
            f.setStrikeOut(True)
            self.title.setFont(f)
            self.title.setStyleSheet(f"color: {C['faint']};")
        body.addWidget(self.title)

        self.reminder_status = QToolButton(self)
        self.reminder_status.setObjectName("reminderStatus")
        self.reminder_status.setStyleSheet(
            f"QToolButton#reminderStatus {{ color: {C['rem_fg']}; background: {C['rem_bg']}; "
            f"border: 1px solid {C['rem_border']}; border-radius: 8px; padding: 4px 9px; font-size: 12px; "
            f"font-weight: 700; }} QToolButton#reminderStatus:hover {{ background: {C['rem_hover']}; }}")
        self.reminder_status.setCursor(Qt.PointingHandCursor)
        self.reminder_status.setToolTip("Change or remove this reminder")
        self.reminder_status.setFocusPolicy(Qt.StrongFocus)
        self.reminder_status.clicked.connect(self._edit_reminder)
        body.addWidget(self.reminder_status, 0, Qt.AlignLeft)
        self._refresh_reminder()

        self.itch_status = QLabel()
        self.itch_status.setObjectName("itchStatus")
        self.itch_status.setStyleSheet(f"color: {C['dim']}; font-size: 10px;")
        body.addWidget(self.itch_status)

        # while editing: the flag toggles inline (Tab: title > urgent > distraction > itch > details)
        self.flag_row = QWidget()
        fr = QHBoxLayout(self.flag_row)
        fr.setContentsMargins(0, 2, 0, 2)
        fr.setSpacing(6)
        self.fb = {}
        for key, icon, word, tip in FLAG_DEFS:
            b = QToolButton()
            b.setObjectName("flag")
            b.setProperty("kind", key)
            b.setText(f"{icon} {word}")
            b.setProperty("flaghint", tip.split(". ")[0])
            b.setProperty("flagword", word)
            if not flag_on(panel.store.settings, key):
                b.hide()
            b.setCheckable(True)
            b.setChecked(bool(task.get(key)))
            b.setFocusPolicy(Qt.StrongFocus)
            b.toggled.connect(lambda on, k=key: self.set_flag(k, on))
            b.installEventFilter(self)
            fr.addWidget(b)
            self.fb[key] = b
        fr.addStretch(1)
        self.flag_row.hide()
        body.addWidget(self.flag_row)

        self.desc = AutoText(task["desc"], "Add details")
        self.desc.setObjectName("details")
        self.desc.textChanged.connect(self._on_desc)
        body.addWidget(self.desc)
        self.desc.setVisible(bool(task["desc"].strip()))   # after adding: a parentless show pops a window
        self.title.submitted.connect(lambda: QTimer.singleShot(0, self.select))   # Enter: done editing

        self.drop_hint = QLabel("Drop to attach to this task")
        self.drop_hint.setObjectName("dropHint")
        self.drop_hint.setAlignment(Qt.AlignCenter)
        self.drop_hint.hide()
        body.addWidget(self.drop_hint)

        if task["attachments"]:
            grid = QGridLayout()
            grid.setSpacing(5)
            grid.setContentsMargins(0, 3, 0, 0)
            for i, a in enumerate(task["attachments"]):
                grid.addWidget(AttachmentTile(panel, task, a), i // 4, i % 4)
            grid.setColumnStretch(4, 1)
            body.addLayout(grid)

        self.attach_hint = QLabel("Paste or drop a photo or file to attach")
        self.attach_hint.setObjectName("attachHint")
        self.attach_hint.hide()
        body.addWidget(self.attach_hint)

        for w in (self.title, self.desc):
            w.installEventFilter(self)
            w.setAcceptDrops(False)

        # hover actions (floating, so the title keeps its full width)
        self.actions = ActionPill(self)
        self.actions.setObjectName("actionPill")   # painted by ActionPill itself
        ah = QHBoxLayout(self.actions)
        ah.setContentsMargins(3, 2, 3, 2)
        self.destroyed.connect(self.actions.deleteLater)   # it lives in the list, so it goes with the note
        ah.setSpacing(4)
        self.ob = {}
        self.copy_btn = CopyButton()
        self.copy_btn.setToolTip("Copy this note (Ctrl+C while it's selected)")
        self.copy_btn.setFocusPolicy(Qt.NoFocus)   # keyboard: Ctrl+C on a selected note, so Tab still starts at Later
        self.copy_btn.clicked.connect(lambda: self.copy_note())
        ah.addWidget(self.copy_btn)
        self.tags_btn = IconAct("tag", C["dim"], C["text"], "Tags: add or remove flags on this note")
        self.tags_btn.setFocusPolicy(Qt.NoFocus)
        self.tags_btn.clicked.connect(self.tags_menu)
        self.tags_btn.installEventFilter(self)
        self.remind_btn = IconAct("bell", C["dim"], C["idea"], "Remind me: bring this note back at a time you pick")
        self.remind_btn.setFocusPolicy(Qt.NoFocus)
        self.remind_btn.clicked.connect(self._edit_reminder)
        self.remind_btn.installEventFilter(self)
        if not task["done"]:
            ah.addWidget(self.tags_btn)
            ah.addWidget(self.remind_btn)
        acts = [("\u2713 Done" if not task["done"] else "Not done",
                 "Mark it done (the round box, or Ctrl+Enter, does the same)" if not task["done"]
                 else "Back to the open notes", lambda: panel.done_from_keyboard(self))]
        if not task["done"]:   # the other ways out at the break
            if task.get("later"):
                acts.append(("Back to list", "Bring it back into the main list", lambda: panel.set_later(task, False)))
            else:
                acts.append(("Later", "Not today. Tuck it into the Later section", lambda: panel.set_later(task, True)))
            acts.append(("Let go", "No action needed, or just an observation. Logged, not lost",
                         lambda: panel.let_go(task, self)))
        acts.append(("Delete", "Delete a mistake or a test note (Delete key; you can undo)",
                     lambda: panel.delete_task(task, self)))
        self.act_btns = []
        for text, tip, fn in acts:
            if text == "Delete":
                b = IconAct("trash", C["faint"], C["anti"], "Delete (Delete key; you can undo). For mistakes and "
                                                            "test notes")
            else:
                b = QToolButton()
                b.setObjectName("act")
                b.setText(text)
                b.setToolTip(tip)
            b.setFocusPolicy(Qt.NoFocus)          # reached with Tab from a selected card, not by the Tab chain
            if text == "Delete":
                b.setProperty("danger", True)
            if text.startswith("\u2713"):
                b.setProperty("good", True)
            b.clicked.connect(fn)
            b.installEventFilter(self)
            ah.addWidget(b)
            self.act_btns.append(b)
        if not task["done"]:
            self.act_btns += [self.tags_btn, self.remind_btn]   # Tab order: Later, Let go, Delete, Tags, Remind
        self._has_actions = True   # Copy is always there
        self.actions.adjustSize()
        self.actions.hide()
        chain = [self.title] + [self.fb[k] for k in FLAG_KEYS] + [self.desc]   # hidden flags are skipped by Tab
        for a, b in zip(chain, chain[1:]):
            QWidget.setTabOrder(a, b)
        self._apply_flag_look()

    def _refresh_itch_status(self):
        started = self.task.get("itch_started_at")
        actions = self.task.get("itch_actions") or []
        minutes = sum(int(a.get("minutes", 0)) for a in actions if isinstance(a, dict))
        if started:
            try:
                time_label = datetime.fromisoformat(started).strftime("%I:%M %p").lstrip("0")
            except (ValueError, TypeError):
                time_label = "now"
            self.itch_status.setText(f"Started at {time_label}" +
                                     (f" · {minutes} min recorded" if minutes else ""))
        elif actions:
            self.itch_status.setText(f"Acted on · {minutes} min" +
                                     (f" across {len(actions)} times" if len(actions) > 1 else ""))
        else:
            self.itch_status.clear()
        self.itch_status.setVisible(bool(started or actions))

    def _refresh_reminder(self):
        value = self.task.get("reminder")
        label = "\u23f0 " + reminder_label(value)
        self.reminder_status.setText(label)
        self.reminder_status.setAccessibleName(label + ". Click to change or remove it")
        self.reminder_status.setVisible(bool(value))

    def _edit_reminder(self):
        anchor = self.sender() if isinstance(self.sender(), QWidget) else None
        changed, value = edit_reminder(self, self.task.get("reminder"), anchor)
        if changed:
            if value:
                self.task["reminder"] = value
            else:
                self.task.pop("reminder", None)
            self.panel.store.save()
            self._refresh_reminder()
            if value and self.panel.isVisible():
                self.panel._toast(reminder_confirmation(value), ms=4000)

    # ---- flags (updated in place, so focus and Tab order survive)
    def _apply_flag_look(self):
        t = self.task
        live = not t["done"]
        st = self.panel.store.settings
        on = {k: bool(t.get(k)) and live and flag_on(st, k) for k in FLAG_KEYS}
        for k, chip in self.chips.items():
            chip.setVisible(on[k])
        self.chip_row.setVisible(any(on.values()))
        stripe = next((kind for k, kind in (("urgent", "urgent"), ("antiglimmer", "anti"), ("distraction", "dist"),
                                            ("glimmer", "glimmer"), ("urge", "urge"), ("idea", "idea"))
                       + tuple((k, k) for k in FLAG_KEYS if k not in BUILTIN_FLAG_KEYS) if on.get(k)), "")
        self.setProperty("stripe", stripe)
        self.setProperty("tint", next((k for k in ("urgent", "urge", "glimmer") if on.get(k)), ""))
        self.outer.setContentsMargins(7 if stripe else 10, 9, 10, 9)  # coloured left border is 3px
        self.style().unpolish(self)
        self.style().polish(self)
        self._refresh_itch_status()

    def _start_itch_action(self):
        if self.panel.store.start_itch_action(self.task):
            self.panel.refresh_later(self.task["id"], select=True)

    def _cancel_itch_action(self):
        if self.panel.store.cancel_itch_action(self.task):
            self.panel.refresh_later(self.task["id"], select=True)

    def _record_itch_action(self, finish=False):
        default = 10
        if finish:
            try:
                elapsed = datetime.now() - datetime.fromisoformat(self.task["itch_started_at"])
                default = max(1, min(1440, math.ceil(elapsed.total_seconds() / 60)))
            except (KeyError, TypeError, ValueError):
                pass
        minutes = ask(self, "Time spent", default, (5, 10, 15, 30, 60), "min", (1, 1440))
        if minutes and self.panel.store.record_itch_action(self.task, minutes):
            self.panel.refresh_later(self.task["id"], select=True)

    def _undo_itch_action(self):
        if self.panel.store.undo_itch_action(self.task):
            self.panel.refresh_later(self.task["id"], select=True)

    def set_flag(self, key, on):
        if bool(self.task.get(key)) == on:
            return
        self.task[key] = on
        self.panel.store.log_event(f"{key}_{'on' if on else 'off'}", self.task)
        self.panel.store.save()
        for group in (self.fb, self.ob):
            b = group.get(key)
            if b and b.isChecked() != on:
                b.blockSignals(True)
                b.setChecked(on)
                b.blockSignals(False)
        self._apply_flag_look()
        self.panel.update_counts()
        if key == "urgent":   # urgent tasks sit at the top: re-sort, keeping you on this toggle
            self.panel.refresh_later(self.task["id"], focus_key="urgent" if self.fb["urgent"].hasFocus() else None)

    # ---- copy
    def note_text(self):
        """What Copy puts on the clipboard: the title, then the details on the next lines (if any)."""
        title = self.task.get("title", "").strip()
        desc = self.task.get("desc", "").strip()
        return f"{title}\n{desc}" if desc else title

    def _files(self):
        st = self.panel.store
        return [st.abs_path(a) for a in self.task.get("attachments", []) if st.abs_path(a).exists()]

    def copy_note(self, what="both"):
        """what: "text" (title and details), "files" (the attached files), or "both" (pasting into a chat or a
        folder gives the files, into a text box gives the text)."""
        text = self.note_text()
        files = self._files() if what in ("files", "both") else []
        if what == "files" and not files:
            return
        if not text and not files:
            return
        md = QMimeData()
        if what != "files" and text:
            md.setText(text)
        if files:
            md.setUrls([QUrl.fromLocalFile(str(f)) for f in files])
            if len(files) == 1 and files[0].suffix.lower() in IMG_EXT and what == "files":
                md.setImageData(QImage(str(files[0])))
        QGuiApplication.clipboard().setMimeData(md)
        editing = getattr(self, "_active", False)
        if not editing and not self.hasFocus():
            self.select()        # so after pasting elsewhere, Alt+Tab back and Down goes to the next note
        if not editing and (self.underMouse() or self.pill_in_use()):
            self._place_actions()   # copied with the mouse: the tick shows on the button you clicked
            self.actions.show()
            self.actions.raise_()
            self.copy_btn.flash()
        else:
            self.panel._toast("\u2713  Copied", ms=1500)   # Ctrl+C: say it without covering the note

    # ---- behaviour
    def set_active(self, on):
        """Active = you're editing this task: show the details line and the attach hint,
        and keep the hover buttons out of the way of the text (Alt+Up/Down still reorders)."""
        self._active = on
        self.flag_row.setVisible(False)            # tags: the Tags button on the pill (keeps the note narrow)
        self.desc.setVisible(bool(self.desc.toPlainText().strip()))   # older notes' details, if any
        self.attach_hint.setVisible(False)         # paste or drop works anyway; no extra line appearing

    def tags_menu(self):
        """Flags for this note, from the pill: a small card of colored chips, tick as many as you like."""
        TagPicker(self).open_at(self.tags_btn.mapToGlobal(QPoint(0, self.tags_btn.height() + 4)))

    def _check_active(self):
        fw = QApplication.focusWidget()
        self.set_active(fw in (self.title, self.desc, *self.fb.values()))

    def _to_details(self):
        if self.desc.isVisible():
            self.desc.setFocus()

    # ---- keyboard browsing (the card is "selected" when it has focus itself)
    def select(self):
        self.panel.hide_pills()        # browsing with the keys: a pill left under the mouse would look selected
        self.panel._nav_cursor = QCursor.pos()
        self.setFocus(Qt.OtherFocusReason)
        self.panel.ensure_visible(self)
        if self._has_actions:
            QTimer.singleShot(0, self._show_pill_for_keys)   # after the scroll, so it lands under this note

    def _show_pill_for_keys(self):
        """The selected note shows its Later / Let go / Delete pill too (in the gap under it, off the text)."""
        try:
            if self.hasFocus():
                self.panel.hide_pills(keep=self)
                self._place_actions()
                self.actions.show()
                self.actions.raise_()
        except RuntimeError:
            pass

    def pill_in_use(self):
        """Tab moved keyboard focus onto this note's buttons."""
        return any(b.hasFocus() for b in self.act_btns)

    def open_editing(self):
        self.set_active(True)
        self.title.setFocus()
        cur = self.title.textCursor()
        cur.movePosition(cur.MoveOperation.End)
        self.title.setTextCursor(cur)

    def focusInEvent(self, e):
        super().focusInEvent(e)
        # selected: the same lit look as hover, and its Later / Let go / Delete pill in the gap under it
        self.update()
        self.panel.show_nav_hint(True)

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        self.update()
        QTimer.singleShot(0, self.maybe_hide_pill)     # browsed away with the keys: its pill goes too
        QTimer.singleShot(0, self.panel.check_nav_hint)
        if not any(b.hasFocus() for b in self.act_btns):
            QTimer.singleShot(0, self.maybe_hide_pill)

    def is_current(self):
        """The note you're on: the one showing its button pill, or (with no pill up) the one selected with the
        keys or under the mouse. Mouse and keyboard get the same look."""
        owner = getattr(self.panel, "_pill_owner", None)
        if owner is not None and Panel._alive(owner) and owner.isVisible():
            return owner is self
        return self.hasFocus() or any(b.hasFocus() for b in self.act_btns) or self.underMouse()

    def paintEvent(self, e):
        super().paintEvent(e)
        if not self.is_current():
            return
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        stripe = 3 if self.property("stripe") else 0
        r = QRectF(self.rect()).adjusted(0.75 + stripe, 0.75, -0.75, -0.75)   # starts inside the flag's colour edge
        p.setPen(Qt.NoPen)
        p.setBrush(veil(13))                            # a touch lighter (darker on light), on any tint
        p.drawRoundedRect(r, 9, 9)
        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(veil(95), 1.5))                   # soft neutral ring: never fights the flag colours
        p.drawRoundedRect(r, 9, 9)

    def _focus_action(self, i):
        if not self.act_btns:
            return
        self.panel.hide_pills(keep=self)
        self._place_actions()
        self.actions.show()
        self.actions.raise_()
        self.act_btns[i % len(self.act_btns)].setFocus(Qt.TabFocusReason)
        self.update()

    def _nav_key(self, e):
        """Keys while the card is selected. Returns True if handled."""
        k, mods = e.key(), e.modifiers()
        if k in (Qt.Key_Up, Qt.Key_Down):
            d = -1 if k == Qt.Key_Up else 1
            if mods & Qt.AltModifier:
                self.panel.move_task(self.task, d, keep_selected=True)
            else:
                self.panel.select_neighbor(self, d)
            return True
        if k in (Qt.Key_Return, Qt.Key_Enter):
            if mods & Qt.ControlModifier:
                self.panel.done_from_keyboard(self)
            else:
                self.open_editing()
            return True
        if k == Qt.Key_Delete:
            self.panel.delete_task(self.task, self)
            return True
        if e.matches(QKeySequence.Copy):
            self.copy_note()
            return True
        return False

    def contextMenuEvent(self, e):
        m = QMenu(self)
        m.setStyleSheet(STYLE)
        m.addAction("Edit reminder..." if self.task.get("reminder") else "Remind me...", self._edit_reminder)
        m.addSeparator()
        if self.task.get("attachments"):
            cm = m.addMenu("Copy")
            cm.addAction("Text and files", lambda: self.copy_note("both"))
            cm.addAction("Just the text", lambda: self.copy_note("text"))
            cm.addAction("Just the files", lambda: self.copy_note("files"))
        else:
            m.addAction("Copy note", lambda: self.copy_note())
        if self.task.get("urge") or self.task.get("itch_started_at"):
            acted = m.addMenu("Acted on this itch")
            if self.task.get("itch_started_at"):
                acted.addAction("Finish and record time…", lambda: self._record_itch_action(finish=True))
                acted.addAction("Cancel start", self._cancel_itch_action)
            else:
                acted.addAction("Start now", self._start_itch_action)
                acted.addAction("Record time spent…", self._record_itch_action)
            if self.task.get("itch_actions"):
                acted.addAction("Undo last record", self._undo_itch_action)
        others = [l for l in self.panel.store.lists if l is not self.panel.store.list_of(self.task)]
        if others:
            mv = m.addMenu("Move to")
            for l in others:
                mv.addAction(l["name"], lambda l=l: self.panel.move_to_list(self.task, l, self))
        m.addSeparator()
        if not self.task["done"]:
            if self.task.get("later"):
                m.addAction("Back to list", lambda: self.panel.set_later(self.task, False))
            else:
                m.addAction("Later", lambda: self.panel.set_later(self.task, True))
            m.addAction("Let go", lambda: self.panel.let_go(self.task, self))
            m.addSeparator()
        m.addAction("Delete", lambda: self.panel.delete_task(self.task, self))
        m.exec(e.globalPos())

    def event(self, e):
        # Tab on a selected card goes to its Later / Let go buttons (Qt would otherwise move focus away)
        if e.type() == QEvent.KeyPress and self.hasFocus() and e.key() in (Qt.Key_Tab, Qt.Key_Backtab):
            self._focus_action(0 if e.key() == Qt.Key_Tab else -1)
            return True
        return super().event(e)

    def keyPressEvent(self, e):
        if self.hasFocus() and self._nav_key(e):
            return
        super().keyPressEvent(e)

    def mouseReleaseEvent(self, e):  # click on the note (not its text): select it, like the arrow keys do
        if e.button() == Qt.LeftButton:
            self.select()
        super().mouseReleaseEvent(e)

    def enterEvent(self, e):
        self.update()
        if not self._has_actions:
            return
        if any(c.pill_in_use() for c in self.panel.live_cards() if c is not self):
            return                      # you're on another note's buttons with the keyboard: leave that one alone
        if QCursor.pos() == self.panel._nav_cursor:
            return                      # the list scrolled under a mouse that didn't move: not a real hover
        self.panel.hide_pills(keep=self)
        self._place_actions()
        self.actions.show()
        self.actions.raise_()

    def leaveEvent(self, e):
        self.update()
        QTimer.singleShot(60, self.maybe_hide_pill)   # it may be on its way to the pill

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if self.actions.isVisible():
            self._place_actions()

    def _place_actions(self):
        host = self.parentWidget()
        if host is None:
            return
        if self.actions.parentWidget() is not host:
            self.actions.setParent(host)        # hidden by setParent; shown by whoever called us
        self.actions.adjustSize()
        g = self.geometry()
        h = self.actions.height()
        y = g.bottom() + 5 - h // 2              # centred on the gap under the note
        y = max(0, min(y, host.height() - h))
        self.actions.move(g.right() - self.actions.width() - 10, y)
        self.actions.raise_()

    def moveEvent(self, e):
        super().moveEvent(e)
        if self.actions.isVisible():
            self._place_actions()

    def hideEvent(self, e):
        self.actions.hide()
        super().hideEvent(e)

    def maybe_hide_pill(self):
        """Mouse left the note or the pill: hide it, unless it went from one to the other or Tab is on it."""
        try:
            if not (self.underMouse() or self.actions.underMouse() or self.pill_in_use() or self.hasFocus()):
                self.actions.hide()
        except RuntimeError:
            pass

    def _on_title(self):
        self.task["title"] = self.title.toPlainText()
        self.panel.store.save()

    def _on_desc(self):
        self.task["desc"] = self.desc.toPlainText()
        self.panel.store.save()

    def _consume_inline_reminder(self):
        title, title_reminder = extract_inline_reminder(self.title.toPlainText())
        desc, desc_reminder = extract_inline_reminder(self.desc.toPlainText())
        reminder = desc_reminder or title_reminder
        if not reminder or not (title.strip() or desc.strip()):
            return
        if title != self.title.toPlainText():
            self.title.setPlainText(title)
        if desc != self.desc.toPlainText():
            self.desc.setPlainText(desc)
        self.task["reminder"] = reminder
        self.panel.store.save()
        self._refresh_reminder()
        if self.panel.isVisible():
            self.panel._toast(reminder_confirmation(reminder), ms=4000)

    def eventFilter(self, obj, e):
        if obj in (getattr(self, "title", None), getattr(self, "desc", None)) and e.type() == QEvent.FocusOut:
            QTimer.singleShot(0, self._consume_inline_reminder)
        if obj in getattr(self, "act_btns", []):
            if e.type() == QEvent.ShortcutOverride and e.key() == Qt.Key_Escape:
                e.accept()
                return True
            if e.type() == QEvent.KeyPress:
                k = e.key()
                i = self.act_btns.index(obj)
                if k in (Qt.Key_Tab, Qt.Key_Backtab):
                    step = -1 if k == Qt.Key_Backtab or e.modifiers() & Qt.ShiftModifier else 1
                    if 0 <= i + step < len(self.act_btns):
                        self._focus_action(i + step)
                    else:                       # past the last button: back to the card
                        self.actions.hide()
                        self.select()
                    return True
                if k in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Space):
                    obj.click()
                    return True
                if k == Qt.Key_Escape:
                    self.actions.hide()
                    self.select()
                    return True
                if k in (Qt.Key_Up, Qt.Key_Down):
                    self.actions.hide()
                    self.select()
                    return self._nav_key(e)
            if e.type() == QEvent.FocusOut:
                QTimer.singleShot(0, lambda: self.update())
            return False
        if obj in getattr(self, "fb", {}).values():
            flag_focus_hint(obj, e)
            if flag_enter_toggles(obj, e):
                return True
        editing = obj in (getattr(self, "title", None), getattr(self, "desc", None)) or obj in getattr(self, "fb", {}).values()
        if editing and e.type() == QEvent.ShortcutOverride and e.key() == Qt.Key_Escape:
            e.accept()      # Esc while editing goes back to browsing, instead of closing the list
            return True
        if editing and e.type() == QEvent.KeyPress:
            if e.key() == Qt.Key_Escape:
                self.set_active(False)
                self.select()
                return True
            if e.key() in (Qt.Key_Return, Qt.Key_Enter) and e.modifiers() & Qt.ControlModifier:
                self.panel.done_from_keyboard(self)
                return True
        if e.type() == QEvent.FocusIn:
            self.set_active(True)
        elif e.type() == QEvent.FocusOut:
            QTimer.singleShot(0, self._check_active)
        if e.type() == QEvent.KeyPress:
            if e.matches(QKeySequence.Paste) and self.panel.paste_into(self.task):
                return True
            if e.modifiers() & Qt.AltModifier and e.key() in (Qt.Key_Up, Qt.Key_Down):
                self.panel.move_task(self.task, -1 if e.key() == Qt.Key_Up else 1, keep_selected=False)
                return True
        return super().eventFilter(obj, e)

    def _set_drag(self, on):
        self.setProperty("drag", on)
        self.drop_hint.setVisible(on)
        self.style().unpolish(self)
        self.style().polish(self)

    def dragEnterEvent(self, e):
        md = e.mimeData()
        if isinstance(e.source(), AttachmentTile):
            e.ignore()                     # a file on its way out of the shelf, not a new drop
            return
        if md.hasUrls() or md.hasImage() or md.hasText():
            e.acceptProposedAction()
            self._set_drag(True)

    def dragLeaveEvent(self, e):
        self._set_drag(False)

    def dropEvent(self, e):
        self._set_drag(False)
        md = e.mimeData()
        if not self.panel.attach_mime(self.task, md) and md.hasText() and md.text().strip():
            d = self.task["desc"]
            self.task["desc"] = (d + "\n" if d else "") + md.text().strip()
            self.panel.store.save()
            self.panel.refresh_later(self.task["id"])
        e.acceptProposedAction()


HISTORY_OUTCOMES = [("open", "Open"), ("later", "Later"), ("done", "Done"), ("cleared", "Done and cleared"),
                    ("let go", "Let go"), ("abandoned", "Abandoned")]


class HistoryDialog(QDialog):
    """Every thought you've ever parked (from the thought log), with search, type (flags), outcome and a date
    range. Read-only: it's for looking back, the list is for acting."""

    def __init__(self, store, parent=None):
        super().__init__(parent, Qt.Window)
        self.store = store
        self.setWindowTitle(f"{APP_NAME}: history")
        self.setStyleSheet(STYLE + f"""
            QDialog {{ background: {C['bg']}; }}
            QListWidget {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
                border-radius: 6px; font-size: 12px; }}
            QListWidget::item {{ padding: 5px 6px; border-bottom: 1px solid {C['surface']}; }}
            QListWidget::item:selected {{ background: {C['accent_soft']}; color: {C['text']}; }}
            QDateEdit {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
                border-radius: 5px; padding: 2px 4px; }}""")
        self.resize(560, 560)
        self.rows = []
        self.types, self.outcomes = set(), set()
        v = QVBoxLayout(self)
        v.setSpacing(8)
        top = QHBoxLayout()
        self.q = QLineEdit(self)
        self.q.setPlaceholderText("Search all your thoughts")
        self.q.setClearButtonEnabled(True)
        self.q.textChanged.connect(self.apply)
        self.type_btn = QToolButton(self)
        self.type_btn.setObjectName("link")
        self.type_btn.clicked.connect(lambda: self._menu(self.type_btn, self._type_items(), self.types))
        self.out_btn = QToolButton(self)
        self.out_btn.setObjectName("link")
        self.out_btn.clicked.connect(lambda: self._menu(self.out_btn, HISTORY_OUTCOMES, self.outcomes))
        top.addWidget(self.q, 1)
        top.addWidget(self.type_btn)
        top.addWidget(self.out_btn)
        v.addLayout(top)
        dates = QHBoxLayout()
        dates.setSpacing(4)
        self.d_from = QDateEdit(self)
        self.d_to = QDateEdit(self)
        for d in (self.d_from, self.d_to):
            d.setCalendarPopup(True)
            d.setDisplayFormat("MMM d, yyyy")
            d.dateChanged.connect(self.apply)
        lab = QLabel("From", self)
        lab.setObjectName("hint")
        dates.addWidget(lab)
        dates.addWidget(self.d_from)
        lab2 = QLabel("to", self)
        lab2.setObjectName("hint")
        dates.addWidget(lab2)
        dates.addWidget(self.d_to)
        dates.addStretch(1)
        for label, days in (("Today", 0), ("7 days", 7), ("30 days", 30), ("All", None)):
            b = QToolButton(self)
            b.setObjectName("link")
            b.setText(label)
            b.clicked.connect(lambda _=False, n=days: self.set_range(n))
            dates.addWidget(b)
        v.addLayout(dates)
        self.list = QListWidget(self)
        self.list.setWordWrap(True)
        self.list.currentItemChanged.connect(self._show_detail)
        v.addWidget(self.list, 1)
        self.detail = QLabel(self)
        self.detail.setObjectName("emptyText")
        self.detail.setWordWrap(True)
        self.detail.setTextInteractionFlags(Qt.TextSelectableByMouse)
        v.addWidget(self.detail)
        bottom = QHBoxLayout()
        self.count = QLabel(self)
        self.count.setObjectName("hint")
        bottom.addWidget(self.count, 1)
        cp = QPushButton("Copy these", self)
        cp.setToolTip("Copy the thoughts shown, one per line")
        cp.clicked.connect(self.copy_shown)
        bottom.addWidget(cp)
        v.addLayout(bottom)
        QShortcut(QKeySequence("Ctrl+F"), self, lambda: (self.q.setFocus(), self.q.selectAll()))
        self._labels()

    def _type_items(self):
        return [(k, f"{icon}  {w[0].upper() + w[1:]}") for k, icon, w, _ in FLAG_DEFS] + [("none", "No flag")]

    def _menu(self, btn, items, chosen):
        m = QMenu(self)
        m.setStyleSheet(STYLE)
        for key, label in items:
            a = m.addAction(label)
            a.setCheckable(True)
            a.setChecked(key in chosen)
            a.toggled.connect(lambda on, k=key: (chosen.add(k) if on else chosen.discard(k), self._labels(), self.apply()))
        m.addSeparator()
        m.addAction("Any", lambda: (chosen.clear(), self._labels(), self.apply()))
        keep_menu_open(m)
        m.exec(btn.mapToGlobal(btn.rect().bottomLeft()))

    def _labels(self):
        self.type_btn.setText(f"Type ({len(self.types)})" if self.types else "Type: any")
        self.out_btn.setText(f"Outcome ({len(self.outcomes)})" if self.outcomes else "Outcome: any")

    def reload(self):
        self.rows = sorted(thought_rows(self.store), key=lambda r: r.get("captured_at") or "", reverse=True)
        first = next((r["captured_at"] for r in reversed(self.rows) if r.get("captured_at")), None)
        self._first = QDate.fromString(first[:10], "yyyy-MM-dd") if first else QDate.currentDate()
        self.set_range(None)

    def set_range(self, days):
        today = QDate.currentDate()
        for d in (self.d_from, self.d_to):
            d.blockSignals(True)
        self.d_from.setDate(self._first if days is None else today.addDays(-days))
        self.d_to.setDate(today)
        for d in (self.d_from, self.d_to):
            d.blockSignals(False)
        self.apply()

    @staticmethod
    def flags_of(r):
        m = {"urgent": "urgent_ever", "distraction": "dist_ever", "urge": "urge_ever", "glimmer": "glimmer_ever",
             "antiglimmer": "antiglimmer_ever", "idea": "idea_ever"}
        return [k for k, col in m.items() if r.get(col)] + [k for k in FLAG_KEYS if k not in m
                                                           and k in r.get("flags_ever", [])]

    def matches(self, r):
        day = (r.get("captured_at") or "")[:10]
        if not (self.d_from.date().toString("yyyy-MM-dd") <= day <= self.d_to.date().toString("yyyy-MM-dd")):
            return False
        fl = self.flags_of(r)
        if self.types and not (set(fl) & self.types or ("none" in self.types and not fl)):
            return False
        if self.outcomes and r.get("outcome") not in self.outcomes:
            return False
        q = self.q.text().strip().lower()
        return not q or q in (r.get("title", "") + "\n" + r.get("details", "")).lower()

    def apply(self, *_):
        self.list.clear()
        icons = {k: icon for k, icon, *_ in FLAG_DEFS}
        icons.update({k: "" for k in BUILTIN_FLAG_KEYS if k not in icons})
        self.shown = [r for r in self.rows if self.matches(r)]
        for r in self.shown[:2000]:
            try:
                when = datetime.fromisoformat(r["captured_at"]).strftime("%b %d, %H:%M")
            except Exception:
                when = ""
            fl = " ".join(icons[k] for k in self.flags_of(r))
            text = f"{when}   {fl + '  ' if fl else ''}{r.get('title') or 'Untitled'}   \u00B7 {r.get('outcome', '')}"
            it = QListWidgetItem(text)
            it.setData(Qt.UserRole, r)
            self.list.addItem(it)
        n = len(self.shown)
        self.count.setText(f"{n} thought{'s' if n != 1 else ''}" + (" (showing 2000)" if n > 2000 else ""))
        self.detail.setText("")

    def _show_detail(self, cur, _prev=None):
        r = cur.data(Qt.UserRole) if cur else None
        if not r:
            self.detail.setText("")
            return
        bits = [f"List: {r.get('list') or '?'}", f"Outcome: {r.get('outcome')}"]
        if r.get("resolved_at"):
            bits.append(f"on {r['resolved_at'][:16].replace('T', ' ')}")
        det = (r.get("details") or "").strip()
        self.detail.setText("  \u00B7  ".join(bits) + (f"\n{det}" if det else ""))

    def copy_shown(self):
        lines = [f"- {r.get('title') or 'Untitled'}" for r in getattr(self, "shown", [])]
        QGuiApplication.clipboard().setText("\n".join(lines))
        self.count.setText(f"Copied {len(lines)}")


class SendButton(QAbstractButton):
    """Round Park button with a paper plane, beside the text boxes (like sending a chat message). Greyed out until
    something is typed. Click it, or Tab to it and press Enter or Space."""

    def __init__(self, parent, on_click, edits):
        super().__init__(parent)
        self.setFixedSize(40, 40)
        self.setCursor(Qt.PointingHandCursor)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setToolTip("Park it (Enter)")
        self.clicked.connect(on_click)
        self._edits = edits
        for e in edits:
            e.textChanged.connect(self.sync)
        self.sync()

    def sync(self, *_):
        self.setEnabled(any(e.toPlainText().strip() for e in self._edits))
        self.update()

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key_Return, Qt.Key_Enter) and self.isEnabled():
            self.click()
            return
        super().keyPressEvent(e)

    def enterEvent(self, e):
        self.update()

    def leaveEvent(self, e):
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        on = self.isEnabled()
        body = QColor(C["accent"]) if on else QColor(C["surface_hi"])
        if on and (self.underMouse() or self.isDown()):
            body = body.lighter(118)
        r = QRectF(2, 2, 36, 36)
        if self.hasFocus():
            p.setPen(QPen(QColor(C["text"]), 1.5))
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(QRectF(0.75, 0.75, 38.5, 38.5))
        p.setPen(Qt.NoPen)
        p.setBrush(body)
        p.drawEllipse(r)
        # paper plane, pointing right and a little up
        ink = QColor("white") if on else QColor(C["faint"])
        p.translate(20, 20)
        p.rotate(-12)
        plane = QPainterPath()
        plane.moveTo(-9, -8)
        plane.lineTo(10, 0)
        plane.lineTo(-9, 8)
        plane.lineTo(-6, 0)
        plane.closeSubpath()
        p.setBrush(ink)
        p.drawPath(plane)
        p.setPen(QPen(body, 1.6))
        p.drawLine(QPointF(-6, 0), QPointF(3, 0))


def send_button(parent, on_click, edits):
    """The Park button: for anyone who doesn't reach for Enter. Greyed out until something is typed."""
    b = QToolButton(parent)
    b.setObjectName("send")
    b.setText("Park \u2192")
    b.setToolTip("Park it (same as Enter)")
    b.setCursor(Qt.PointingHandCursor)
    b.setFocusPolicy(Qt.NoFocus)          # keyboard users press Enter; Tab stays on the flags
    b.clicked.connect(on_click)

    def sync(*_):
        b.setEnabled(any(e.toPlainText().strip() for e in edits))
    for e in edits:
        e.textChanged.connect(sync)
    sync()
    return b


def line_icon(kind, color, size=26):
    """Flat line icons on a 24-unit grid (rounded joins, 2-unit strokes), drawn at twice the size so they stay crisp
    on high-DPI screens: "trash" and "tag"."""
    from PySide6.QtGui import QIcon
    dpr = 2.0
    pm = QPixmap(int(size * dpr), int(size * dpr))
    pm.setDevicePixelRatio(dpr)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.scale(size / 24, size / 24)
    p.setPen(QPen(QColor(color), 2.0, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(Qt.NoBrush)
    if kind == "trash":
        p.drawLine(QPointF(3.5, 6.5), QPointF(20.5, 6.5))                  # lid
        handle = QPainterPath()
        handle.moveTo(8.5, 6.5)
        handle.lineTo(8.5, 4.8)
        handle.quadTo(8.5, 3, 10.3, 3)
        handle.lineTo(13.7, 3)
        handle.quadTo(15.5, 3, 15.5, 4.8)
        handle.lineTo(15.5, 6.5)
        p.drawPath(handle)
        body = QPainterPath()
        body.moveTo(5.5, 6.5)
        body.lineTo(6.4, 19)
        body.quadTo(6.6, 21, 8.6, 21)
        body.lineTo(15.4, 21)
        body.quadTo(17.4, 21, 17.6, 19)
        body.lineTo(18.5, 6.5)
        p.drawPath(body)
        p.drawLine(QPointF(10, 10.5), QPointF(10, 17))
        p.drawLine(QPointF(14, 10.5), QPointF(14, 17))
    elif kind == "tag":
        tag = QPainterPath()
        tag.moveTo(3.2, 11.6)
        tag.lineTo(3.2, 4.8)
        tag.quadTo(3.2, 3.2, 4.8, 3.2)
        tag.lineTo(11.6, 3.2)
        tag.lineTo(20.3, 11.9)
        tag.quadTo(21.2, 12.8, 20.3, 13.7)
        tag.lineTo(13.7, 20.3)
        tag.quadTo(12.8, 21.2, 11.9, 20.3)
        tag.closeSubpath()
        p.drawPath(tag)
        p.setBrush(QColor(color))
        p.setPen(Qt.NoPen)
        p.drawEllipse(QPointF(7.6, 7.6), 1.6, 1.6)
    elif kind == "bell":
        bell = QPainterPath()
        bell.moveTo(4, 17.5)
        bell.quadTo(6, 15.5, 6, 12.5)
        bell.lineTo(6, 10)
        bell.cubicTo(6, 6.2, 8.7, 3.5, 12, 3.5)
        bell.cubicTo(15.3, 3.5, 18, 6.2, 18, 10)
        bell.lineTo(18, 12.5)
        bell.quadTo(18, 15.5, 20, 17.5)
        bell.closeSubpath()
        p.drawPath(bell)
        clapper = QPainterPath()
        clapper.moveTo(9.8, 20.5)
        clapper.quadTo(12, 22.3, 14.2, 20.5)
        p.drawPath(clapper)
    p.end()
    return QIcon(pm)


class IconAct(QToolButton):
    """A pill button that is just an icon (Tags, Delete), which changes colour on hover like the others."""

    def __init__(self, kind, color, hover_color, tip):
        super().__init__()
        self.setObjectName("act")
        self._icons = (line_icon(kind, color), line_icon(kind, hover_color))
        self.setIcon(self._icons[0])
        self.setIconSize(QSize(13, 13))     # no taller than the text buttons, so the pill keeps its height
        self.setToolTip(tip)
        self.setAccessibleName(tip.split(":")[0].split(" (")[0])

    def enterEvent(self, e):
        self.setIcon(self._icons[1])
        super().enterEvent(e)

    def leaveEvent(self, e):
        self.setIcon(self._icons[0])
        super().leaveEvent(e)

    def focusInEvent(self, e):
        self.setIcon(self._icons[1])
        super().focusInEvent(e)

    def focusOutEvent(self, e):
        self.setIcon(self._icons[0])
        super().focusOutEvent(e)


BREAK_COLOR = "#4fb6a8"
DONE_TOASTS = ["Nice.", "One less thing.", "Off your plate.", "Checked off.", "That's handled.", "Lighter already."]


def play_icon(color):
    """A rounded play triangle for the Focus and Break buttons."""
    from PySide6.QtGui import QIcon
    pm = QPixmap(32, 32)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    path = QPainterPath()
    path.moveTo(10, 7)
    path.lineTo(25, 16)
    path.lineTo(10, 25)
    path.closeSubpath()
    p.setPen(QPen(QColor(color), 3, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(QColor(color))
    p.drawPath(path)
    p.end()
    return QIcon(pm)


def funnel_icon(color):
    """A small painted funnel (the filter button inside the search box)."""
    from PySide6.QtGui import QIcon
    pm = QPixmap(32, 32)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    path = QPainterPath()
    path.moveTo(5, 7)
    path.lineTo(27, 7)
    path.lineTo(18.5, 17)
    path.lineTo(18.5, 25)
    path.lineTo(13.5, 27)
    path.lineTo(13.5, 17)
    path.closeSubpath()
    p.setPen(QPen(QColor(color), 2.2, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(Qt.NoBrush)
    p.drawPath(path)
    p.end()
    return QIcon(pm)


class SentenceLabel(QLabel):
    """One line when it fits; otherwise each sentence on its own line (never a lone word on line two)."""

    def __init__(self, text):
        super().__init__()
        self.full = text
        self.parts = [p.strip() + "." for p in text.split(".") if p.strip()]
        self.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        self.setMinimumWidth(1)
        self.setText(text)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        fm = self.fontMetrics()
        room = self.width() - 6
        if fm.horizontalAdvance(self.full) <= room:
            want = self.full
        else:
            lines = []
            for p in self.parts:           # a sentence wider than the room breaks after its first comma
                if fm.horizontalAdvance(p) > room and ", " in p:
                    a, b = p.split(", ", 1)
                    lines += [a + ",", b]
                else:
                    lines.append(p)
            want = "\n".join(lines)
        if self.text() != want:
            self.setText(want)


class HelpPopup(QFrame):
    """All the how-to in one place, so the main view doesn't need instructions everywhere."""

    def __init__(self, store):
        super().__init__(None, Qt.Popup | Qt.FramelessWindowHint)
        self.setObjectName("helpPop")
        self.setStyleSheet(STYLE)
        self.store = store
        lay = QVBoxLayout(self)
        lay.setContentsMargins(14, 12, 14, 12)
        self.label = QLabel()
        self.label.setTextFormat(Qt.RichText)
        self.label.setWordWrap(True)
        self.label.setFixedWidth(380)
        lay.addWidget(self.label)

    def show_at(self, pos):
        st = self.store.settings
        q = st.get("hotkey_quick", DEFAULT_HOTKEY_QUICK) or "no hotkey"
        l = st.get("hotkey_panel", DEFAULT_HOTKEY_PANEL) or "no hotkey"
        rows = [
            ("Park", "Type above and press Enter. Paste a snip, or drop files or text anywhere here."),
            ("Shelf", "Drop files, screenshots, links or text on the circle to hold them for later. "
                      "Drag a file back out of its note into an email, a chat or a folder."),
            ("Quick note", f"Scribble the mouse up and down, or {q}. Shows nothing else on screen."),
            ("This list", f"Scribble left and right, click the circle, or {l}."),
            ("Important work", "Expand the strip near the top and press +. Give each important piece of work "
                               "a due date and time. It shows time left and the gap to the next deadline. "
                               "Mark work finished or open Finished to bring it back."),
            ("Details", "Click a task's title and press Enter, or click the task, to add details."),
            ("Attach", "Paste (Ctrl+V) or drop a photo or file onto a task."),
            (f"{URGENT_ICON} Urgent", "Really needs doing soon. Urgent thoughts sit at the top, with a red edge."),
            (f"{DIST_ICON} Distraction", "Something from outside broke your focus (a knock, a ping, noise)."),
            (f"{URGE_ICON} Itch", "A pull from inside that feels urgent but can wait. Parked, no guilt."),
            (f"{GLIMMER_ICON} Lift / {ANTI_ICON} drain", "A small good moment / a small moment that put you on edge. "
                                                           "Tracked for your patterns."),
            (f"{IDEA_ICON} Idea", "Something worth keeping, not a to-do. Filter by Idea to see them all."),
            ("Search", "\u2315 or Ctrl+F: search this list, filter by flag, state or date, change the sort, "
                       "or open <b>History</b> to browse every thought you've ever parked."),
            ("Sound", "\u266B opens noise (brown, pink, white, volume) and Music (your songs on repeat)."),
            ("Flags", "Click a task, then Tab from the title through the flags and press Space. "
                      "Switch flags on or off in Settings &gt; Flags."),
            ("At the break", "\u2713 done. Hover for <b>Later</b> (not today) or <b>Let go</b> (no action needed: "
                             "a worry, a passed itch, or just an observation like a lift or a drain). Let go is logged, not lost, with Undo."),
            ("Copy", "Hover a note and click the copy icon, or select it and press Ctrl+C. "
                     "<b>Copy all</b> at the bottom (Ctrl+Shift+C) copies every open note as a list."),
            ("Switch back", "While the list is open it's in Alt+Tab. Coming back puts you on the note you were on. "
                            "Clicking the circle also brings it back."),
            ("Files", "Hover a file to copy it, double-click to open, right-click for more."),
            ("Lists", "+ adds one. Double-click to rename, right-click to delete, drag to reorder. "
                      "The first tab is your inbox: quick notes and drops on the circle land there. "
                      "Right-click a note (or Menu key) &gt; Move to, to sort it into another tab."),
            ("Delete", "Delete on hover, the Delete key, or right-click. For mistakes and test notes: kept in trash, "
                       "left out of your patterns. Undo in the toast."),
            ("Keyboard", "Down from the box selects a note. \u2191\u2193 browse, Enter opens, Esc back, Ctrl+Enter done, "
                         "Tab for Later / Let go, Alt+\u2191\u2193 moves it."),
            ("Resize", "Drag the left, right or bottom edge, or the dotted corner."),
            ("Timer &amp; settings", "Right-click the circle."),
        ]
        html = "<table cellspacing='0' cellpadding='3'>" + "".join(
            f"<tr><td valign='top' style='color:{C['dim']};padding-right:10px;white-space:nowrap'><b>{a}</b></td>"
            f"<td style='color:{C['text']}'>{b}</td></tr>" for a, b in rows) + "</table>"
        self.label.setText(html)
        self.adjustSize()
        screen = QGuiApplication.screenAt(pos) or QGuiApplication.primaryScreen()
        area = screen.availableGeometry()
        x = max(area.left(), min(pos.x() - self.width() + 20, area.right() - self.width()))
        y = max(area.top(), min(pos.y() + 8, area.bottom() - self.height()))
        self.move(x, y)
        self.show()
        apply_share_privacy(self)


# ---------------------------------------------------------------- rounded frameless window
class LinkToggle(QAbstractButton):
    """Two chain links between Focus and Break. Joined = the break starts by itself when focus ends.
    Apart = you choose when focus ends."""
    TIP_ON = "Break starts by itself after focus.\nClick to turn off."
    TIP_OFF = "Break waits for you after focus.\nClick so it starts by itself."

    def __init__(self):
        super().__init__()
        self.setCheckable(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setFixedSize(34, 26)
        self.setFocusPolicy(Qt.TabFocus)
        self.toggled.connect(self._sync_tip)
        self._sync_tip(False)

    def _sync_tip(self, on):
        self.setToolTip(self.TIP_ON if on else self.TIP_OFF)
        self.update()

    def enterEvent(self, e):
        super().enterEvent(e)
        QToolTip.showText(QCursor.pos(), self.toolTip(), self)   # teach right away, no hover delay
        self.update()

    def leaveEvent(self, e):
        super().leaveEvent(e)
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        on, hov = self.isChecked(), self.underMouse()
        r = QRectF(self.rect()).adjusted(1, 2, -1, -2)
        if on or hov:
            bg = QColor(C["accent"]) if on else QColor(C["border"])
            bg.setAlpha(60 if on else 140)
            p.setPen(Qt.NoPen)
            p.setBrush(bg)
            p.drawRoundedRect(r, r.height() / 2, r.height() / 2)
        col = QColor(C["cream"]) if on else QColor(C["dim"] if hov else C["faint"])
        pen = QPen(col, 1.8)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        cy, w, h = self.height() / 2, 11.0, 7.0
        mid = self.width() / 2
        gap = -3.0 if on else 2.0            # overlapping when linked, apart when not
        p.drawRoundedRect(QRectF(mid - gap / 2 - w, cy - h / 2, w, h), h / 2, h / 2)
        p.drawRoundedRect(QRectF(mid + gap / 2, cy - h / 2, w, h), h / 2, h / 2)
        if not on:                           # a small break mark between the links
            p.drawLine(QPointF(mid - 1.5, cy - 6), QPointF(mid - 0.5, cy - 4))
            p.drawLine(QPointF(mid + 0.5, cy + 4), QPointF(mid + 1.5, cy + 6))


class MenuStayOpen(QObject):
    """Clicking an on/off or pick-one item (a checkable action) applies it and keeps the menu open, so you can
    try several settings in one go. Anything else (dialogs, Restart, Quit...) closes the menu as usual.
    Esc or a click outside closes it."""

    def eventFilter(self, menu, e):
        t = e.type()
        if t == QEvent.MouseButtonRelease and e.button() == Qt.LeftButton:
            a = menu.actionAt(e.position().toPoint())
        elif t == QEvent.KeyPress and e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Space):
            a = menu.activeAction()
        else:
            return False
        if a is not None and a.isEnabled() and a.isCheckable() and a.menu() is None:
            a.trigger()
            return True
        return False


MENU_STAY_OPEN = None


def keep_menu_open(menu):
    """Install MenuStayOpen on a menu and all its submenus."""
    global MENU_STAY_OPEN
    if MENU_STAY_OPEN is None:
        MENU_STAY_OPEN = MenuStayOpen()
    menu.installEventFilter(MENU_STAY_OPEN)
    for a in menu.actions():
        if a.menu() is not None:
            keep_menu_open(a.menu())


def menu_pos_beside(menu, rect):
    """Where to open a menu so it sits beside rect (the circle) instead of on top of it."""
    menu.ensurePolished()
    size = menu.sizeHint()
    screen = QGuiApplication.screenAt(rect.center()) or QGuiApplication.primaryScreen()
    area = screen.availableGeometry()
    x = rect.left() - size.width() - 6 if rect.center().x() > area.center().x() else rect.right() + 6
    y = rect.center().y() - 40
    x = max(area.left(), min(x, area.right() - size.width()))
    y = max(area.top(), min(y, area.bottom() - size.height()))
    return QPoint(x, y)


class GrowText(QPlainTextEdit):
    """A details box that starts as one line and grows with what you type or paste (up to max_lines, then it
    scrolls). Enter parks the note; Shift+Enter starts a new line. Offers the few QLineEdit calls the quick
    note uses (text, returnPressed)."""
    returnPressed = Signal()
    grew = Signal()

    def __init__(self, max_lines=6, allow_newline=True):
        super().__init__()
        self.max_lines = max_lines
        self.allow_newline = allow_newline   # False for titles: Enter always parks, pasted line breaks become spaces
        self.setTabChangesFocus(True)
        self.setLineWrapMode(QPlainTextEdit.WidgetWidth)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        self.document().setDocumentMargin(2)
        self.textChanged.connect(self._fit)
        self._fit()

    def text(self):
        return self.toPlainText()

    def setText(self, text):
        self.setPlainText(text)            # also clears this box's own undo history
        self.moveCursor(QTextCursor.End)

    def isUndoAvailable(self):
        return self.document().isUndoAvailable()

    def cursor_on_last_line(self):
        c = QTextCursor(self.textCursor())
        return not c.movePosition(QTextCursor.Down)

    def insertFromMimeData(self, md):
        if not self.allow_newline and md.hasText():
            self.insertPlainText(" ".join(md.text().split()))
            return
        super().insertFromMimeData(md)

    def _fit(self):
        fm = self.fontMetrics()
        lines = 0
        block = self.document().begin()
        while block.isValid():
            lay = block.layout()
            lines += max(1, lay.lineCount() if lay is not None else 1)
            block = block.next()
        lines = max(1, min(self.max_lines, lines))
        m = self.contentsMargins()
        h = lines * fm.lineSpacing() + 2 * int(self.document().documentMargin()) + m.top() + m.bottom() + 10
        if h != self.height():
            self.setFixedHeight(h)
            self.grew.emit()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        QTimer.singleShot(0, self._fit)    # re-wrap at the new width

    def keyPressEvent(self, e):
        if e.key() in (Qt.Key_Return, Qt.Key_Enter) and (not self.allow_newline
                                                          or not (e.modifiers() & Qt.ShiftModifier)):
            self.returnPressed.emit()
            return
        if edge_jump(self, e):
            return
        super().keyPressEvent(e)


class CopyButton(QAbstractButton):
    """The copy icon on a note's hover pill: two overlapping pages. After a copy it turns green and a tick pops in
    for a moment, so you know it worked without a toast. Painted by hand so it looks the same on every Windows setup."""
    W, H = 28, 20

    def __init__(self, parent=None, label=""):
        super().__init__(parent)
        self.label = label
        extra = QFontMetrics(self.font()).horizontalAdvance(max(label, "Copied")) + 10 if label else 0
        self.setFixedSize(self.W + extra, self.H)
        self.setCursor(Qt.PointingHandCursor)
        self._done = 0.0          # 0 = copy icon, >0 = tick (its pop-in scale)
        self._anim = QVariantAnimation(self)
        self._anim.setDuration(260)
        self._anim.setStartValue(0.4)
        self._anim.setEndValue(1.0)
        self._anim.setEasingCurve(QEasingCurve.OutBack)
        self._anim.valueChanged.connect(self._set_done)
        self._reset = QTimer(self)
        self._reset.setSingleShot(True)
        self._reset.timeout.connect(lambda: self._set_done(0.0))

    def set_label(self, label):
        if self.label == label:
            return
        self.label = label
        self._anim.stop()
        self._reset.stop()
        self._done = 0.0
        extra = QFontMetrics(self.font()).horizontalAdvance(max(label, "Copied")) + 10 if label else 0
        self.setFixedSize(self.W + extra, self.H)
        self.update()

    def _set_done(self, v):
        self._done = float(v)
        self.update()

    def flash(self):
        """Show the green tick for a moment."""
        self._anim.stop()
        self._set_done(0.4)       # show it straight away; the animation pops it to full size
        self._anim.start()
        self._reset.start(1200)

    def enterEvent(self, e):
        self.update()

    def leaveEvent(self, e):
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        hover = self.underMouse()
        if self._done:
            bg, edge, ink = QColor(C["glimmer_bg"]), QColor(C["glimmer"]), QColor(C["glimmer"])
        elif self.isDown():
            bg, edge, ink = QColor(C["accent_soft"]), QColor(C["accent"]), QColor(C["text"])
        elif hover:
            bg, edge, ink = QColor(C["surface_hi"]), QColor(C["faint"]), QColor(C["text"])
        else:
            bg, edge, ink = QColor(C["surface"]), QColor(C["border"]), QColor(C["dim"])
        p.setPen(QPen(edge, 1))
        p.setBrush(bg)
        p.drawRoundedRect(r, 8, 8)
        cx, cy = r.left() + self.W / 2 - 0.5, r.center().y()
        if self.label:
            p.setPen(ink)
            p.drawText(QRectF(self.W - 4, 0, self.width() - self.W, self.height()), Qt.AlignVCenter | Qt.AlignLeft,
                       "Copied" if self._done else self.label)
        if self._done:
            k = self._done
            pen = QPen(ink, 1.8)
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen)
            p.setBrush(Qt.NoBrush)
            path = QPainterPath(QPointF(cx - 4.5 * k, cy + 0.2 * k))
            path.lineTo(QPointF(cx - 1.3 * k, cy + 3.4 * k))
            path.lineTo(QPointF(cx + 4.8 * k, cy - 3.4 * k))
            p.drawPath(path)
            return
        pen = QPen(ink, 1.3)
        pen.setJoinStyle(Qt.RoundJoin)
        # back page: only its top and left edges peek out
        back = QRectF(cx - 5.0, cy - 5.5, 7.5, 8.5)
        front = QRectF(cx - 2.0, cy - 2.5, 7.5, 8.5)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        p.save()
        clip = QPainterPath()
        clip.addRect(QRectF(self.rect()))
        hole = QPainterPath()
        hole.addRoundedRect(front.adjusted(-1.6, -1.6, 1.6, 1.6), 2.6, 2.6)
        p.setClipPath(clip.subtracted(hole))
        p.drawRoundedRect(back, 2, 2)
        p.restore()
        p.drawRoundedRect(front, 2, 2)


class ActionPill(QFrame):
    """The Copy / Later / Let go / Delete pill of a note. It floats on the note's bottom edge, in the gap between
    notes (it's a child of the list, not of the note), so it never covers the note's text."""
    FADE = 0

    def __init__(self, card):
        super().__init__(card)
        self.card = card
        self.setAttribute(Qt.WA_TranslucentBackground)

    def leaveEvent(self, e):
        QTimer.singleShot(60, self.card.maybe_hide_pill)

    def enterEvent(self, e):
        self.card.update()                  # the note stays lit while you're on its buttons

    def showEvent(self, e):
        super().showEvent(e)
        self.card.panel.set_pill_owner(self.card)
        QTimer.singleShot(0, self.card.panel._update_more)     # the "more" pill steps aside for it

    def hideEvent(self, e):
        super().hideEvent(e)
        try:
            if getattr(self.card.panel, "_pill_owner", None) is self.card:
                self.card.panel.set_pill_owner(None)
            QTimer.singleShot(0, self.card.panel._update_more)
        except RuntimeError:
            pass

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        p.setBrush(QColor(C["bg"]))
        p.setPen(QPen(QColor(C["border"]), 1))
        p.drawRoundedRect(r, r.height() / 2, r.height() / 2)


class RoundedWindow(QWidget):
    """Frameless, translucent top-level window painted as a rounded card with a soft shadow.
    SHADOW px around the card are transparent; layouts should add it to their margins."""
    SHADOW = 10
    RADIUS = 14

    def __init__(self, flags, accent_border=False):
        super().__init__(None, flags | Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self._accent_border = accent_border

    def card_rect(self):
        m = self.SHADOW
        return QRectF(self.rect()).adjusted(m, m - 2, -m, -m - 2)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = self.card_rect()
        for i in range(self.SHADOW, 0, -1):          # soft shadow, darker near the card
            a = int(46 * (1 - i / (self.SHADOW + 1)) ** 2)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(0, 0, 0, a))
            p.drawRoundedRect(r.adjusted(-i, -i + 3, i, i + 3), self.RADIUS + i, self.RADIUS + i)
        g = QRadialGradient(r.left() + r.width() * 0.2, r.top(), max(r.width(), r.height()) * 1.1)
        g.setColorAt(0.0, QColor(C["glow"]))
        g.setColorAt(1.0, QColor(C["bg"]))
        p.setBrush(g)
        border = QColor(C["accent"]) if self._accent_border else veil(26 if theme_dark() else 40)
        if self._accent_border:
            border.setAlpha(170)
        p.setPen(QPen(border, 1))
        p.drawRoundedRect(r, self.RADIUS, self.RADIUS)
        p.setPen(QPen(QColor(255, 255, 255, 14 if theme_dark() else 200), 1))   # faint highlight along the top
        p.drawLine(QPointF(r.left() + self.RADIUS, r.top() + 1.5), QPointF(r.right() - self.RADIUS, r.top() + 1.5))


class GrabHandle(QWidget):
    """The small pill at the top of the list: drag it to move the window."""

    def __init__(self, win):
        super().__init__()
        self.win = win
        self.setFixedHeight(12)
        self.setCursor(Qt.SizeAllCursor)
        self.setToolTip("Drag to move")
        self._press = None

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        w = 36
        p.setPen(Qt.NoPen)
        p.setBrush(veil(60 if self.underMouse() or self._press else 34))
        p.drawRoundedRect(QRectF((self.width() - w) / 2, 4, w, 4), 2, 2)

    def enterEvent(self, e):
        self.update()

    def leaveEvent(self, e):
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            self._press = e.globalPosition().toPoint() - self.win.frameGeometry().topLeft()

    def mouseMoveEvent(self, e):
        if self._press is not None and not (e.buttons() & Qt.LeftButton):
            self._press = None
        if self._press is not None:
            self.win.move(e.globalPosition().toPoint() - self._press)

    def mouseReleaseEvent(self, e):
        self._press = None
        self.update()


# ---------------------------------------------------------------- important work shelf
def work_due(item):
    try:
        return datetime.fromisoformat(item["due"])
    except (KeyError, TypeError, ValueError):
        return None


def short_span(seconds):
    """A readable duration for deadline countdowns and gaps, rounded up to the next minute."""
    minutes = max(1, math.ceil(abs(seconds) / 60))
    days, rest = divmod(minutes, 1440)
    hours, mins = divmod(rest, 60)
    if days:
        return f"{days}d {hours}h" if hours else f"{days}d"
    if hours:
        return f"{hours}h {mins}m" if mins else f"{hours}h"
    return f"{mins}m"


def work_time_left(due, now=None):
    if due is None:
        return "Set a due date"
    seconds = due.timestamp() - (now or datetime.now()).timestamp()
    if abs(seconds) < 30:
        return "Due now"
    return f"{short_span(seconds)} left" if seconds > 0 else f"Overdue by {short_span(seconds)}"


def work_due_label(due, now=None):
    if due is None:
        return "Date unavailable"
    now = now or datetime.now()
    delta = (due.date() - now.date()).days
    day = "Today" if delta == 0 else "Tomorrow" if delta == 1 else due.strftime("%a %d %b")
    return f"{day}, {due.strftime('%I:%M %p').lstrip('0')}"


class ImportantWorkDialog(QDialog):
    """One short form: name and a local due date/time, with a few easy starting points."""
    def __init__(self, parent, item=None):
        super().__init__(parent)
        self.setWindowTitle("Edit important work" if item else "Add important work")
        self.setModal(True)
        self.setMinimumWidth(340)
        self.setStyleSheet(full_style() + f"QDialog {{ background: {C['bg']}; color: {C['text']}; }}"
                           f"QDateTimeEdit {{ background: {C['field']}; color: {C['text']}; "
                           f"border: 1px solid {C['border']}; border-radius: 6px; padding: 5px; }}")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(18, 16, 18, 16)
        lay.setSpacing(10)
        heading = QLabel("What matters?" if not item else "Update this work")
        heading.setStyleSheet("font-size: 15px; font-weight: 700;")
        lay.addWidget(heading)
        self.title_edit = QLineEdit(self)
        self.title_edit.setPlaceholderText("e.g. Finish the lab report")
        self.title_edit.setMaxLength(180)
        self.title_edit.setText(item.get("title", "") if item else "")
        self.title_edit.setAccessibleName("Important work name")
        lay.addWidget(self.title_edit)
        due_label = QLabel("Due date and time")
        lay.addWidget(due_label)
        self.due_edit = QDateTimeEdit(self)
        self.due_edit.setDisplayFormat("ddd, d MMM yyyy  h:mm AP")
        self.due_edit.setCalendarPopup(True)
        initial = work_due(item) if item else None
        self.due_edit.setDateTime(QDateTime(initial) if initial else QDateTime.currentDateTime().addDays(1))
        self.due_edit.setAccessibleName("Due date and time")
        lay.addWidget(self.due_edit)
        presets = QHBoxLayout()
        for caption, days in (("Today", 0), ("Tomorrow", 1), ("In a week", 7)):
            btn = QPushButton(caption, self)
            btn.clicked.connect(lambda _=False, d=days: self.due_edit.setDateTime(
                QDateTime.currentDateTime().addSecs(3600) if d == 0 else QDateTime.currentDateTime().addDays(d)))
            presets.addWidget(btn)
        lay.addLayout(presets)
        hint = QLabel("Change the time above if the deadline is exact.")
        hint.setObjectName("hint")
        lay.addWidget(hint)
        buttons = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel, parent=self)
        buttons.button(QDialogButtonBox.Save).setText("Save work")
        buttons.button(QDialogButtonBox.Save).setEnabled(bool(self.title_edit.text().strip()))
        self.title_edit.textChanged.connect(lambda s: buttons.button(QDialogButtonBox.Save).setEnabled(bool(s.strip())))
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        lay.addWidget(buttons)
        self.title_edit.setFocus()

    def showEvent(self, e):
        apply_share_privacy(self)
        super().showEvent(e)

    def values(self):
        return self.title_edit.text().strip(), self.due_edit.dateTime().toPython()


class ImportantWorkShelf(QFrame):
    """A collapsible, user-chosen deadline list, independent of captured thoughts."""
    def __init__(self, store, parent):
        super().__init__(parent)
        self.store = store
        self.calendar = None  # wired by main; tests and offline mode need no account
        self.setObjectName("workShelf")
        self._time_labels = []
        self._gap_labels = []
        self.show_finished = False
        outer = QVBoxLayout(self)
        outer.setContentsMargins(8, 4, 8, 4)
        outer.setSpacing(3)
        top = QHBoxLayout()
        top.setSpacing(4)
        self.toggle_btn = QToolButton(self)
        self.toggle_btn.setObjectName("workToggle")
        self.toggle_btn.setCursor(Qt.PointingHandCursor)
        self.toggle_btn.clicked.connect(self.toggle)
        top.addWidget(self.toggle_btn, 1)
        self.next_label = QLabel(self)
        self.next_label.setObjectName("workNext")
        top.addWidget(self.next_label)
        add = QToolButton(self)
        self.add_btn = add
        add.setObjectName("workAdd")
        add.setText("+")
        add.setToolTip("Add important work")
        add.setAccessibleName("Add important work")
        add.clicked.connect(self.add_work)
        top.addWidget(add)
        outer.addLayout(top)
        self.body = QWidget(self)
        body_lay = QVBoxLayout(self.body)
        body_lay.setContentsMargins(0, 2, 0, 0)
        body_lay.setSpacing(3)
        self.scroll = QScrollArea(self.body)
        self.scroll.setObjectName("workScroll")
        self.scroll.setWidgetResizable(True)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.viewport().setStyleSheet("background: transparent;")
        self.rows = QWidget(self.scroll)
        self.rows.setObjectName("workRows")
        self.rows.setStyleSheet("background: transparent;")
        self.rows_lay = QVBoxLayout(self.rows)
        self.rows_lay.setContentsMargins(0, 0, 2, 0)
        self.rows_lay.setSpacing(3)
        self.scroll.setWidget(self.rows)
        body_lay.addWidget(self.scroll)
        self.finished_btn = QToolButton(self.body)
        self.finished_btn.setObjectName("workFinished")
        self.finished_btn.clicked.connect(self.toggle_finished)
        body_lay.addWidget(self.finished_btn)
        outer.addWidget(self.body)
        self.clock = QTimer(self)
        self.clock.setInterval(60000)
        self.clock.timeout.connect(self.update_times)
        self.clock.start()
        self.refresh()

    def active(self):
        return sorted((i for i in self.store.important_work if not i.get("done_at")),
                      key=lambda i: work_due(i) or datetime.max)

    def refresh_later(self):
        QTimer.singleShot(0, self.refresh)

    def toggle(self):
        st = self.store.settings
        st["important_open"] = not st.get("important_open", False)
        self.store.save()
        self.refresh_later()

    def toggle_finished(self):
        self.show_finished = not self.show_finished
        self.refresh_later()

    def _dialog(self, item=None):
        dlg = ImportantWorkDialog(self, item)
        dlg.adjustSize()
        panel = self.window()
        area = (QGuiApplication.screenAt(panel.geometry().center()) or QGuiApplication.primaryScreen()).availableGeometry()
        p = panel.geometry().center() - QPoint(dlg.width() // 2, dlg.height() // 2)
        dlg.move(max(area.left(), min(p.x(), area.right() - dlg.width())),
                 max(area.top(), min(p.y(), area.bottom() - dlg.height())))
        if dlg.exec() != QDialog.Accepted:
            return None
        return dlg.values()

    def add_work(self):
        values = self._dialog()
        if values:
            self.store.add_important_work(*values)
            self.store.settings["important_open"] = True
            self.store.save()
            self.refresh_later()

    def edit_work(self, item):
        values = self._dialog(item)
        if values:
            self.store.edit_important_work(item, *values)
            self.refresh_later()

    def set_done(self, item, done):
        self.store.set_important_done(item, done)
        self.refresh_later()

    def refresh(self):
        while self.rows_lay.count():
            child = self.rows_lay.takeAt(0).widget()
            if child:
                child.hide()
                child.deleteLater()
        self._time_labels, self._gap_labels, self._event_labels, self._event_gaps = [], [], [], []
        calendar_mode = bool(self.calendar and self.calendar.connected)
        if calendar_mode:
            self.next_label.clear()
            self.hide()
            return  # The separate calendar agenda owns event rows while connected.
        self.show()
        if calendar_mode:
            self.show_finished = False
        active = [] if calendar_mode else self.active()
        finished = sorted((i for i in self.store.important_work if i.get("done_at") and not calendar_mode),
                          key=lambda i: i.get("done_at", ""), reverse=True)
        shown = finished if self.show_finished else active
        for index, item in enumerate(shown):
            row = QFrame(self.rows)
            row.setObjectName("workRow")
            line = QHBoxLayout(row)
            line.setContentsMargins(5, 4, 5, 4)
            line.setSpacing(7)
            done = QToolButton(row)
            done.setObjectName("workDone")
            done.setText("✓" if item.get("done_at") else "○")
            done.setToolTip("Move back to important work" if item.get("done_at") else "Mark finished")
            done.setAccessibleName(f"{'Restore' if item.get('done_at') else 'Finish'} {item.get('title', 'work')}")
            done.clicked.connect(lambda _=False, i=item: self.set_done(i, not bool(i.get("done_at"))))
            line.addWidget(done)
            info = QVBoxLayout()
            info.setSpacing(0)
            name = QLabel(item.get("title", "Untitled work"), row)
            name.setObjectName("workTitle")
            name.setWordWrap(True)
            info.addWidget(name)
            when = QLabel(row)
            when.setObjectName("workWhen")
            info.addWidget(when)
            if not item.get("done_at"):
                self._time_labels.append((item, when))
            else:
                when.setText("Finished · due " + work_due_label(work_due(item)))
            line.addLayout(info, 1)
            edit = QToolButton(row)
            edit.setObjectName("workEdit")
            edit.setText("Edit")
            edit.setAccessibleName(f"Edit {item.get('title', 'work')}")
            edit.clicked.connect(lambda _=False, i=item: self.edit_work(i))
            line.addWidget(edit)
            self.rows_lay.addWidget(row)
            if not self.show_finished and index + 1 < len(shown):
                gap = QLabel(self.rows)
                gap.setObjectName("workGap")
                self.rows_lay.addWidget(gap)
                self._gap_labels.append((item, shown[index + 1], gap))
        if not shown and not calendar_mode:
            empty = QLabel("Nothing finished yet." if self.show_finished else
                           "Add your own important work with +.", self.rows)
            empty.setObjectName("workEmpty")
            empty.setWordWrap(True)
            self.rows_lay.addWidget(empty)
        now_events = datetime.now().astimezone()
        upcoming = ([e for e in self.calendar.events if e["end"] > now_events and
                     e["start"] <= now_events + timedelta(days=14)]
                    if self.calendar and not self.show_finished else [])
        if calendar_mode and not upcoming:
            empty = QLabel("No upcoming timed events in the next 14 days.", self.rows)
            empty.setObjectName("workEmpty")
            empty.setWordWrap(True)
            self.rows_lay.addWidget(empty)
        if upcoming:
            label = QLabel("FROM GOOGLE CALENDAR", self.rows)
            label.setObjectName("workGap")
            self.rows_lay.addWidget(label)
            for index, event in enumerate(upcoming):
                row = QFrame(self.rows)
                row.setObjectName("workRow")
                line = QHBoxLayout(row)
                line.setContentsMargins(5, 4, 5, 4)
                source = QFrame(row)
                source.setFixedSize(6, 25)
                source.setStyleSheet(
                    f"background: {calendar_color(event.get('event_color'), calendar_color(event.get('calendar_color')))}; border-radius: 3px;")
                source.setToolTip(event.get("calendar_name") or "Calendar")
                line.addWidget(source)
                info = QVBoxLayout()
                info.setSpacing(0)
                title = QLabel(event["title"], row)
                title.setObjectName("workTitle")
                title.setTextFormat(Qt.PlainText)
                title.setWordWrap(True)
                when = QLabel(row)
                when.setObjectName("workWhen")
                info.addWidget(title)
                info.addWidget(when)
                line.addLayout(info, 1)
                self._event_labels.append((event, when))
                if event["url"]:
                    open_button = QToolButton(row)
                    open_button.setObjectName("workEdit")
                    open_button.setText("Open")
                    open_button.setAccessibleName("Open " + event["title"])
                    open_button.clicked.connect(lambda _=False, url=event["url"]: QDesktopServices.openUrl(QUrl(url)))
                    line.addWidget(open_button)
                if self.calendar and event.get("series_key"):
                    hide_button = QToolButton(row)
                    hide_button.setObjectName("workEdit")
                    hide_button.setText("Hide")
                    hide_button.setToolTip("Hide this event series in PTT. It stays in Google Calendar.")
                    hide_button.setAccessibleName("Hide event series " + event["title"])
                    hide_button.clicked.connect(lambda _=False, e=event: self.calendar.hide_event_series(e))
                    line.addWidget(hide_button)
                self.rows_lay.addWidget(row)
                if index + 1 < len(upcoming):
                    gap = QLabel(self.rows)
                    gap.setObjectName("workGap")
                    self.rows_lay.addWidget(gap)
                    self._event_gaps.append((event, upcoming[index + 1], gap))
        self.rows_lay.addStretch(1)
        rows_height = (len(shown) + len(upcoming)) * 55 + (34 if not shown and not upcoming else 0)
        gaps_height = max(0, len(shown) - 1) * (14 if not self.show_finished else 3) + len(upcoming) * 16
        self.scroll.setFixedHeight(min(210, max(56, rows_height + gaps_height + 8)))
        self.finished_btn.setText("Hide finished" if self.show_finished else f"Finished ({len(finished)})")
        self.finished_btn.setVisible(not calendar_mode and (bool(finished) or self.show_finished))
        self.add_btn.setVisible(not calendar_mode)
        opened = self.store.settings.get("important_open", False)
        self.body.setVisible(opened)
        if calendar_mode:
            self.toggle_btn.setText(("▾" if opened else "▸") + f"  Upcoming events  {len(upcoming)}")
            self.toggle_btn.setToolTip("Collapse upcoming events" if opened else "Expand upcoming events")
        else:
            self.toggle_btn.setText(("▾" if opened else "▸") + f"  Important work  {len(active)}")
            self.toggle_btn.setToolTip("Collapse important work" if opened else "Expand important work")
        self.setVisible(not calendar_mode)  # Calendar events now live in the floating bar's agenda.
        self.update_times()

    def update_times(self):
        now = datetime.now()
        if any(event["end"] <= now.astimezone() for event, _ in self._event_labels):
            self.refresh_later()
            return
        active = [] if self.calendar and self.calendar.connected else self.active()
        nearest = work_due(active[0]) if active else None
        event = self._event_labels[0][0] if self._event_labels else None
        event_start = event["start"].replace(tzinfo=None) if event else None
        if event_start and (nearest is None or event_start < nearest):
            self.next_label.setText("Event now" if event_start <= now else
                                    "Event in " + short_span((event_start - now).total_seconds()))
        else:
            self.next_label.setText(work_time_left(nearest, now) if nearest else "")
        for item, label in self._time_labels:
            due = work_due(item)
            label.setText(f"{work_due_label(due, now)} · {work_time_left(due, now)}")
            color = C["urgent"] if due and due < now else (
                C["warn"] if due and (due - now).total_seconds() < 86400 else C["dim"])
            label.setStyleSheet(f"color: {color};")
        for first, second, label in self._gap_labels:
            a, b = work_due(first), work_due(second)
            label.setText(("same time as the next deadline" if b == a else
                           f"then {short_span(b.timestamp() - a.timestamp())} until the next deadline") if a and b else "")
        for event, label in self._event_labels:
            start = event["start"]
            source = (event.get("calendar_name") + " · ") if event.get("calendar_name") else ""
            if start <= datetime.now().astimezone():
                left = max(0, math.ceil((event["end"] - datetime.now().astimezone()).total_seconds() / 60))
                label.setText(f"{source}Now · {left} min left")
            else:
                label.setText(f"{source}{start:%a %b %d, %I:%M %p} · in {short_span((start - datetime.now().astimezone()).total_seconds())}")
        for first, second, label in self._event_gaps:
            seconds = (second["start"] - first["start"]).total_seconds()
            label.setText(f"then {short_span(seconds)} until the next event")


# ---------------------------------------------------------------- main panel
class Panel(RoundedWindow):
    CARD_BATCH = 40

    def __init__(self, store, bubble):
        # a normal window (not Qt.Tool), so it shows in Alt+Tab and on the taskbar while it's open
        super().__init__(Qt.Window | Qt.WindowStaysOnTopHint)
        self._drag = None
        self.store, self.bubble = store, bubble
        self.focus_return = FocusReturn()
        self.setObjectName("roundwin")
        self.setAttribute(Qt.WA_AlwaysShowToolTips)   # tooltips even when the list isn't the active window
        self.setWindowTitle(APP_NAME)
        self.setStyleSheet(full_style())
        self.setAcceptDrops(True)
        self.resize(*self.store.settings.get("panel_size", [400, 580]))

        self.timer = None       # FocusTimer, set by main()
        self.help = HelpPopup(store)

        v = QVBoxLayout(self)
        m = self.SHADOW
        v.setContentsMargins(12 + m, 2 + m - 2, 12 + m, 8 + m + 2)
        v.addWidget(GrabHandle(self))
        v.setSpacing(8)
        tabs_row = QHBoxLayout()
        tabs_row.setSpacing(2)
        self.tabs = QTabBar()
        self.tabs.setExpanding(False)
        self.tabs.setMovable(True)
        self.tabs.setDrawBase(False)
        self.tabs.setElideMode(Qt.ElideRight)
        self.tabs.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tabs.currentChanged.connect(self._tab_changed)
        self.tabs.tabMoved.connect(self._tab_moved)
        self.tabs.customContextMenuRequested.connect(self._tab_menu)
        self.tabs.tabBarDoubleClicked.connect(lambda i: self._rename_list(i))
        add = QToolButton()
        add.setObjectName("addTab")
        add.setText("+")
        add.setToolTip("New list")
        add.clicked.connect(self._new_list)
        helpb = QToolButton()
        helpb.setObjectName("help")
        helpb.setText("?")
        helpb.setToolTip("How it works")
        helpb.clicked.connect(lambda: self._help_menu(helpb))
        aib = QToolButton()
        aib.setObjectName("help")
        aib.setText("\u2728")
        aib.setToolTip("Your thoughts: browse history, copy for AI, AI analyses")
        aib.clicked.connect(lambda: self._open_ai_menu(aib))
        gear = QToolButton()
        gear.setObjectName("help")
        gear.setText("\u2699")
        gear.setToolTip("Settings")
        gear.clicked.connect(lambda: self._open_settings(gear))
        head = QVBoxLayout()               # app name + what it does
        head.setSpacing(0)
        self.title = QLabel(APP_NAME)
        self.title.setObjectName("appTitle")
        sub = SentenceLabel(APP_TAGLINE)
        sub.setObjectName("appSub")
        head.addWidget(self.title)
        head.addWidget(sub)
        tabs_row.addLayout(head, 1)
        closeb = QToolButton()
        closeb.setObjectName("help")
        closeb.setText("\u2715")
        closeb.setToolTip("Close (Esc)")
        closeb.clicked.connect(self.hide)
        findb = QToolButton()
        findb.setObjectName("help")
        findb.setText("\u2315")
        findb.setToolTip("Search, filter and sort (Ctrl+F)")
        findb.clicked.connect(lambda: self.toggle_search())
        self.findb = findb
        self.noise_btn = QToolButton()
        self.noise_btn.setObjectName("help")
        self.noise_btn.setText("\u266B")
        self.noise_btn.setToolTip("Background noise and music")
        self.noise_btn.setContextMenuPolicy(Qt.CustomContextMenu)
        self.noise_btn.clicked.connect(lambda: getattr(self, "noise_menu", lambda a: None)(self.noise_btn))
        self.noise_btn.customContextMenuRequested.connect(
            lambda _p: getattr(self, "noise_menu", lambda a: None)(self.noise_btn))
        tabs_row.addWidget(add)
        tabs_row.addWidget(findb)
        tabs_row.addWidget(self.noise_btn)
        tabs_row.addWidget(helpb)
        tabs_row.addWidget(aib)
        tabs_row.addWidget(gear)
        tabs_row.addWidget(closeb)
        tabs_row.setAlignment(add, Qt.AlignTop)
        for w in (add, findb, self.noise_btn, helpb, aib, gear, closeb):
            tabs_row.setAlignment(w, Qt.AlignTop)
            w.setFixedSize(26, 28)       # big enough to hit and read; the window minimum width leaves room
        self.title.ensurePolished()
        self.title.setMinimumWidth(self.title.fontMetrics().horizontalAdvance(APP_NAME) + 16)
        v.addLayout(tabs_row)
        v.addWidget(self.tabs)                # only shown with two or more lists

        # search row (Ctrl+F or the search button): one box; the funnel inside it holds filter and sort.
        # Active filters and a non-default sort show as small chips under it (click one to drop it).
        self.find_row = QWidget(self)
        fr = QVBoxLayout(self.find_row)
        fr.setContentsMargins(0, 0, 0, 0)
        fr.setSpacing(4)
        self.find_edit = QLineEdit(self.find_row)
        self.find_edit.setObjectName("find")
        self.find_edit.setPlaceholderText("Search this list")
        self.find_edit.setClearButtonEnabled(True)
        self.find_edit.textChanged.connect(self._find_changed)
        self.find_edit.installEventFilter(self)
        self.funnel = self.find_edit.addAction(funnel_icon(C["dim"]), QLineEdit.TrailingPosition)
        self.funnel.setToolTip("Filter and sort")
        self.funnel.triggered.connect(lambda: self._filter_menu().exec(
            self.find_edit.mapToGlobal(self.find_edit.rect().bottomRight()) - QPoint(180, 0)))
        self.chips_row = QWidget(self.find_row)
        self.chips_lay = QHBoxLayout(self.chips_row)
        self.chips_lay.setContentsMargins(0, 0, 0, 0)
        self.chips_lay.setSpacing(4)
        fr.addWidget(self.find_edit)
        fr.addWidget(self.chips_row)
        self.find_row.setVisible(False)
        v.addWidget(self.find_row)
        self.filters = dict(self.NO_FILTER, flags=[])
        self._update_find_labels()

        self.important = ImportantWorkShelf(store, self)
        v.addWidget(self.important)

        # focus timer strip: start focus / break, pause, resume, stop, "I'm back"
        self.timer_row = QFrame()
        self.timer_row.setObjectName("timerBar")
        tr = QHBoxLayout(self.timer_row)
        tr.setContentsMargins(6, 4, 4, 4)
        tr.setSpacing(2)
        # idle: [25 min][> Focus]   [5 min][> Break]
        self.idle_box = QWidget()
        ib = QHBoxLayout(self.idle_box)
        ib.setContentsMargins(0, 0, 0, 0)
        ib.setSpacing(3)
        self.focus_spin = self._spin("focus_min", DEFAULT_FOCUS_MIN, 600, "Focus length in minutes")
        self.break_spin = self._spin("break_min", DEFAULT_BREAK_MIN, 120, "Break length in minutes")
        go_f = QToolButton()
        go_f.setObjectName("startFocus")
        go_f.setIcon(play_icon("white"))
        go_f.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        go_f.setIconSize(QSize(11, 11))
        go_f.setMinimumWidth(go_f.fontMetrics().horizontalAdvance("Break") + 40)
        go_f.setCursor(Qt.PointingHandCursor)
        go_f.setText("Focus")
        go_f.setToolTip("Start a focus session")
        go_f.clicked.connect(lambda: self._start_from(self.focus_spin, "focus"))
        go_b = QToolButton()
        go_b.setObjectName("startBreak")
        go_b.setIcon(play_icon(BREAK_COLOR))
        go_b.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        go_b.setIconSize(QSize(11, 11))
        go_b.setMinimumWidth(go_b.fontMetrics().horizontalAdvance("Break") + 40)
        go_b.setCursor(Qt.PointingHandCursor)
        go_b.setText("Break")
        go_b.setToolTip("Start a break")
        go_b.clicked.connect(lambda: self._start_from(self.break_spin, "break"))
        def unit(spin):
            label = QLabel("min", self.idle_box)
            label.setObjectName("unit")
            label.setBuddy(spin)
            return label
        self.link = LinkToggle()
        self.link.setChecked(bool(self.store.settings.get("auto_break", False)))
        self.link.toggled.connect(self._set_link)
        ib.setSpacing(3)
        ib.addStretch(1)
        ib.addWidget(self.focus_spin)
        ib.addWidget(unit(self.focus_spin))
        ib.addWidget(go_f)
        ib.addSpacing(2)
        ib.addWidget(self.link)
        ib.addSpacing(2)
        ib.addWidget(self.break_spin)
        ib.addWidget(unit(self.break_spin))
        ib.addWidget(go_b)
        ib.addStretch(1)
        tr.addWidget(self.idle_box, 1)
        # running / overrun: label + up to 3 buttons
        self.timer_label = QLabel()
        self.timer_label.setObjectName("timerChip")
        self.timer_label.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        self.timer_label.setMinimumWidth(40)
        tr.addWidget(self.timer_label, 1)
        self.timer_btns = []
        self.ask_tag = None                  # set by main(): "For..." asks what the running round is for
        for _ in range(4):
            b = QToolButton()
            b.setObjectName("timerBtn")
            b.clicked.connect(lambda _=False, btn=b: (btn.property("action") or (lambda: None))())
            tr.addWidget(b)
            self.timer_btns.append(b)
        v.addWidget(self.timer_row)

        self.quick = GrowText(max_lines=6)   # wraps and grows; Enter parks, Shift+Enter starts a new line
        self.quick.setObjectName("quick")
        self.quick.setPlaceholderText("Park a thought, then tag it below")
        self.quick.returnPressed.connect(self._quick_add)
        self.quick.installEventFilter(self)
        self.qflags = {}
        # the thought gets the whole width; the flags sit on a small row under it
        qbox = QVBoxLayout()
        qbox.setSpacing(5)
        qtop = QHBoxLayout()
        qtop.setSpacing(6)
        qtop.addWidget(self.quick, 1)
        self.quick_reminder = None
        self.reminder_btn = reminder_chip(self, self._edit_quick_reminder)
        self.send_btn = SendButton(self, self._quick_add, [self.quick])
        qtop.addWidget(self.send_btn, 0, Qt.AlignBottom)
        qbox.addLayout(qtop)
        self.qrow = QHBoxLayout()
        self.qrow.setSpacing(4)
        frow = QHBoxLayout()
        frow.addLayout(self.qrow, 1)
        frow.addWidget(self.reminder_btn)
        qbox.addLayout(frow)
        v.addLayout(qbox)
        self.build_quick_flags()
        self.flag_number_guide = AltFlagGuide(self, lambda: self.qflags, lambda: self.store.settings)
        for number in range(1, 10):
            sc = QShortcut(QKeySequence(f"Alt+{number}"), self)
            sc.setContext(Qt.WidgetWithChildrenShortcut)
            sc.activated.connect(lambda n=number: toggle_numbered_flag(self.qflags, self.store.settings, n))

        self.drop_banner = QLabel("Drop to park it as a new task")
        self.drop_banner.setObjectName("dropHint")
        self.drop_banner.setAlignment(Qt.AlignCenter)
        self.drop_banner.hide()
        v.addWidget(self.drop_banner)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.list = QWidget()
        self.list.setObjectName("list")
        self.list_lay = QVBoxLayout(self.list)
        self.list_lay.setContentsMargins(0, 2, 2, 16)   # room for the last note's pill
        self.list_lay.setSpacing(8)
        self.scroll.setWidget(self.list)
        v.addWidget(self.scroll, 1)
        self._main_pending = []
        self._main_total = 0
        self._main_load_queued = False
        self._main_select_after_load = False
        self._section_batches = []
        self._refreshing_cards = False
        self._render_generation = 0
        # "↓ 3 more": thoughts below the fold are never silently hidden behind the sections
        self.more = QToolButton(self.scroll.viewport())
        self.more.setObjectName("morePill")
        self.more.setCursor(Qt.PointingHandCursor)
        self.more.clicked.connect(self._advance_more)
        self.more.hide()
        sb = self.scroll.verticalScrollBar()
        sb.valueChanged.connect(self._main_scrolled)
        sb.rangeChanged.connect(lambda *_: QTimer.singleShot(0, self._update_more))

        # Later and Completed stay pinned at the bottom, visible without scrolling
        self.sections = QFrame()
        self.sections.setObjectName("sections")
        self.sec_lay = QVBoxLayout(self.sections)
        self.sec_lay.setContentsMargins(0, 4, 0, 0)
        self.sec_lay.setSpacing(2)
        v.addWidget(self.sections)

        # "Let go" toast with Undo
        # a small pill that floats centred above the bottom of the list (not part of the layout)
        self.toast = QFrame(self)
        self.toast.setObjectName("toast")
        tl = QHBoxLayout(self.toast)
        tl.setContentsMargins(14, 5, 6, 5)
        tl.setSpacing(10)
        self.toast_text = QLabel()
        self.toast_text.setObjectName("toastText")
        self.toast_undo = QToolButton()
        self.toast_undo.setObjectName("toastUndo")
        self.toast_undo.setCursor(Qt.PointingHandCursor)
        self.toast_undo.setText("Undo")
        tl.addWidget(self.toast_text)
        tl.addWidget(self.toast_undo)
        self.toast.hide()
        self._undo_stack = []    # [(label, fn)], newest last; Ctrl+Z walks back through it
        self.toast_undo.setText("Undo")
        self.toast_undo.setToolTip("Undo (Ctrl+Z)")
        self.toast_undo.clicked.connect(self.undo_last)
        self.toast_timer = QTimer(self)
        self.toast_timer.setSingleShot(True)
        self.toast_timer.timeout.connect(self.toast.hide)
        QShortcut(QKeySequence.Undo, self, self.undo_last)

        self.status = QLabel()
        self.status.setObjectName("hint")
        self.copy_all_btn = CopyButton(label="Copy all")
        self.copy_all_btn.setToolTip("Copy all open notes as a list, details under each (Ctrl+Shift+C)")
        self.copy_all_btn.setFocusPolicy(Qt.NoFocus)
        self.copy_all_btn.clicked.connect(self.copy_all)
        foot = QHBoxLayout()
        foot.setContentsMargins(0, 0, 14, 0)   # room for the painted resize grip
        foot.addWidget(self.status, 1)
        foot.addWidget(self.copy_all_btn)
        v.addLayout(foot)
        self.setMouseTracking(True)            # resize cursors on the edges
        self.setMinimumSize(392 + 2 * self.SHADOW, 320)   # room for the app name and seven header icons
        self._resize = None

        QShortcut(QKeySequence("Escape"), self, self._escape)
        QShortcut(QKeySequence("Ctrl+Shift+C"), self, self.copy_all)
        QShortcut(QKeySequence("Ctrl+F"), self, lambda: self.toggle_search(True))
        QShortcut(QKeySequence("Ctrl+Tab"), self, lambda: self._step_tab(1))
        QShortcut(QKeySequence("Ctrl+Shift+Tab"), self, lambda: self._step_tab(-1))
        self.refresh_tabs()
        self.refresh()

    # ---- tabs
    def refresh_tabs(self):
        signature = (tuple((l["id"], l["name"]) for l in self.store.lists),
                     self.store.settings["current"])
        if getattr(self, "_tabs_signature", None) == signature:
            self.refresh_tab_counts()
            return
        self.tabs.blockSignals(True)
        while self.tabs.count():
            self.tabs.removeTab(0)
        cur = 0
        for i, l in enumerate(self.store.lists):
            self.tabs.addTab(l["name"])
            self.tabs.setTabData(i, l["id"])
            if l["id"] == self.store.settings["current"]:
                cur = i
        self.tabs.setCurrentIndex(cur)
        self.tabs.blockSignals(False)
        multi = len(self.store.lists) > 1        # one list needs no tabs; + adds a second one
        self.tabs.setVisible(multi)
        self.refresh_tab_counts()
        self._tabs_signature = signature

    def refresh_tab_counts(self):
        for i, l in enumerate(self.store.lists):
            if i < self.tabs.count():
                n = sum(1 for t in l["tasks"] if not t["done"])
                self.tabs.setTabText(i, l["name"])
                self.tabs.setTabToolTip(i, "Inbox: quick notes and drops on the circle land in the first tab. "
                                           "Drag another tab here to change it." if i == 0 else "")
                # the count is a separate pill beside the name, so it never reads as part of it
                badge = self.tabs.tabButton(i, QTabBar.RightSide)
                if not n:                            # no pill at all, so the tab doesn't keep its width
                    if badge is not None:
                        self.tabs.setTabButton(i, QTabBar.RightSide, None)
                        badge.deleteLater()
                    continue
                if badge is None:
                    badge = QLabel(self.tabs)        # parented first: no flashing popup on Windows
                    badge.setObjectName("tabCount")
                    badge.setAlignment(Qt.AlignCenter)
                if badge.text() != str(n) or self.tabs.tabButton(i, QTabBar.RightSide) is None:
                    badge.setText(str(n))
                    badge.setToolTip(f"{n} open")
                    badge.ensurePolished()
                    badge.adjustSize()               # the tab takes the pill's size when it's set
                    self.tabs.setTabButton(i, QTabBar.RightSide, badge)

    def _tab_changed(self, i):
        if i >= 0:
            self.store.set_current(self.tabs.tabData(i))
            self.refresh_later()

    def _tab_moved(self, frm, to):
        ls = self.store.lists
        ls.insert(to, ls.pop(frm))
        self.store.save()

    def _step_tab(self, d):
        if self.tabs.count():
            self.tabs.setCurrentIndex((self.tabs.currentIndex() + d) % self.tabs.count())

    def _ask_name(self, title, default):
        return ask(self, title, default)

    def _new_list(self):
        name = self._ask_name("New list", f"{datetime.now():%b %d}")
        if name:
            self.store.add_list(name)
            self.refresh_tabs()
            self.refresh_later()

    def _list_at(self, i):
        lid = self.tabs.tabData(i)
        return next(l for l in self.store.lists if l["id"] == lid)

    def _rename_list(self, i):
        if i < 0:
            return
        l = self._list_at(i)
        name = self._ask_name("Rename list", l["name"])
        if name:
            self.store.rename_list(l, name)
            self.refresh_tabs()

    def _tab_menu(self, pos):
        i = self.tabs.tabAt(pos)
        if i < 0:
            return
        l = self._list_at(i)
        m = QMenu(self)
        m.addAction("Rename", lambda: self._rename_list(i))
        d = m.addAction("Delete list (tasks go to trash)", lambda: self._delete_list(l))
        d.setEnabled(len(self.store.lists) > 1)
        m.exec(self.tabs.mapToGlobal(pos))

    def _delete_list(self, l):
        open_n = sum(1 for t in l["tasks"] if not t["done"])
        if open_n and QMessageBox.question(
                self, "Delete list", f"'{l['name']}' has {open_n} open task(s). Move them to trash?") != QMessageBox.Yes:
            return
        self.store.delete_list(l)
        self.refresh_tabs()
        self.refresh_later()

    # ---- rendering
    def refresh_later(self, focus_id=None, focus_details=False, focus_key=None, select=False):
        QTimer.singleShot(0, lambda: self.refresh(focus_id, focus_details, focus_key, select))

    def refresh(self, focus_id=None, focus_details=False, focus_key=None, select=False):
        self._refreshing_cards = True
        self._render_generation += 1
        pos = self.scroll.verticalScrollBar().value()
        self._nav_cards = []
        self._main_pending = []
        self._main_load_queued = False
        self._main_select_after_load = False
        self._section_batches = []
        for lay in (self.list_lay, self.sec_lay):
            while lay.count():
                item = lay.takeAt(0)
                w = item.widget()
                if w:
                    w.hide()
                    w.deleteLater()
        tasks = self.store.tasks
        open_t = [t for t in tasks if not t["done"]]
        active = self.open_in_order()
        later_t = [t for t in open_t if t.get("later")]
        done_t = [t for t in tasks if t["done"]]
        filtering = self.is_filtering()
        if filtering:                       # one flat list of matches; the Later / Completed sections step aside
            active = self.filtered_tasks()
            later_t, done_t = [], []
        focus_card = None
        self._main_total = len(active)
        count = max(self.CARD_BATCH, next((i + 1 for i, t in enumerate(active)
                                          if t["id"] == focus_id), 0)) if focus_id else self.CARD_BATCH
        for i, t in enumerate(active[:count]):
            card = TaskCard(self, t, i, len(active))
            self.list_lay.addWidget(card)
            self._nav_cards.append(card)
            if t["id"] == focus_id:
                focus_card = card
        self._main_pending = active[count:]
        if not active and filtering:
            nm = QLabel("No notes match. Clear the search or the filter to see everything.")
            nm.setObjectName("emptyText")
            nm.setWordWrap(True)
            nm.setAlignment(Qt.AlignCenter)
            self.list_lay.addWidget(nm)
        elif not active:
            self.list_lay.addWidget(self._empty_state(bool(done_t or later_t)))
        self.list_lay.addStretch(1)

        focus_card = self._build_sections(later_t, done_t, focus_id) or focus_card
        self._sync_nav_cards()

        QTimer.singleShot(0, lambda: self.scroll.verticalScrollBar().setValue(pos))
        QTimer.singleShot(0, self._update_more)
        QTimer.singleShot(0, self._place_toast)
        pending = getattr(self, "_pending_select", None)
        self._pending_select = None
        if focus_card and select:
            QTimer.singleShot(0, focus_card.select)
        elif focus_card:
            target = focus_card.fb.get(focus_key) if focus_key else None
            (target or (focus_card.desc if focus_details else focus_card.title)).setFocus()
        elif pending is not None:
            QTimer.singleShot(0, lambda: self.select_index(pending))
        self.status.setStyleSheet("")
        self.update_counts()
        self.bubble.set_count(self.store.open_count())
        self.refresh_tab_counts()
        self.update_timer_row()
        self._built_fp = self._fingerprint()
        self._refreshing_cards = False

    def _build_sections(self, later_t, done_t, focus_id=None):
        """The pinned Later / Completed sections: one open at a time, the rest are one-line headers.
        Returns the card for focus_id if it's in an open section."""
        focus_card = None
        self._section_batches = []
        while self.sec_lay.count():
            w = self.sec_lay.takeAt(0).widget()
            if w:
                w.hide()
                w.deleteLater()
        opened = self.store.settings.get("open_section")
        for key, title, items in (("later", "Later", later_t), ("done", "Completed", done_t)):
            if not items:
                continue
            show = opened == key
            head = QWidget()
            hl = QHBoxLayout(head)
            hl.setContentsMargins(2, 0, 0, 0)
            sec = QToolButton()
            sec.setObjectName("section")
            sec.setText(("\u25BE " if show else "\u25B8 ") + f"{title} ({len(items)})")
            sec.setToolTip("Show" if not show else "Hide")
            sec.clicked.connect(lambda _=False, k=key: self._toggle_section(k))
            hl.addWidget(sec)
            hl.addStretch(1)
            if key == "done":
                clr = QToolButton()
                clr.setObjectName("link")
                clr.setText("Clear")
                clr.setToolTip("Move completed tasks to trash (recoverable in the data folder)")
                clr.clicked.connect(self.clear_completed)  # logged as 'cleared'
                hl.addWidget(clr)
            self.sec_lay.addWidget(head)
            if show:
                box = QScrollArea()
                box.setWidgetResizable(True)
                box.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
                inner = QWidget()
                inner.setObjectName("list")
                il = QVBoxLayout(inner)
                il.setContentsMargins(0, 0, 2, 16)
                il.setSpacing(8)
                count = max(self.CARD_BATCH, next((i + 1 for i, t in enumerate(items)
                                                  if t["id"] == focus_id), 0)) if focus_id else self.CARD_BATCH
                state = {"box": box, "layout": il, "pending": list(items[count:]), "cards": [],
                         "loaded": 0, "total": len(items), "queued": False, "select": False}
                self._section_batches.append(state)
                for t in items[:count]:
                    card = TaskCard(self, t, 0, 0)
                    il.addWidget(card)
                    state["cards"].append(card)
                    state["loaded"] += 1
                    if t["id"] == focus_id:
                        focus_card = card
                il.addStretch(1)
                box.setWidget(inner)
                box.verticalScrollBar().valueChanged.connect(lambda _, s=state: self._section_scrolled(s))
                box.setMaximumHeight(max(140, int(self.height() * 0.38)))   # the main list keeps most of the room
                box.setMinimumHeight(min(90, max(60, inner.sizeHint().height())))
                self.sec_lay.addWidget(box)
        self.sections.setVisible(bool(later_t or done_t))
        return focus_card

    def _main_cards(self):
        return [self.list_lay.itemAt(i).widget() for i in range(self.list_lay.count())
                if isinstance(self.list_lay.itemAt(i).widget(), TaskCard)]

    def _sync_nav_cards(self):
        self._nav_cards = self._main_cards() + [card for state in self._section_batches for card in state["cards"]]

    def _queue_main_more(self, select=False):
        if not self._main_pending:
            return
        self._main_select_after_load |= select
        if not self._main_load_queued:
            self._main_load_queued = True
            QTimer.singleShot(0, lambda g=self._render_generation: self._load_more_main(g))

    def _load_more_main(self, generation):
        if generation != self._render_generation:
            return
        self._main_load_queued = False
        if not self._main_pending:
            return
        first = len(self._main_cards())
        batch, self._main_pending = self._main_pending[:self.CARD_BATCH], self._main_pending[self.CARD_BATCH:]
        for i, task in enumerate(batch, first):
            card = TaskCard(self, task, i, self._main_total)
            self.list_lay.insertWidget(self.list_lay.count() - 1, card)
            card.show()
        self._sync_nav_cards()
        if self._main_select_after_load:
            self._main_select_after_load = False
            self._nav_cards[first].select()
        QTimer.singleShot(0, self._update_more)

    def _main_scrolled(self, value):
        self._update_more()
        bar = self.scroll.verticalScrollBar()
        if (not self._refreshing_cards and self.isVisible() and value > 0 and
                bar.maximum() - value <= self.scroll.viewport().height()):
            self._queue_main_more()

    def _advance_more(self):
        bar = self.scroll.verticalScrollBar()
        if self._main_pending and bar.value() >= bar.maximum():
            self._queue_main_more()
        else:
            bar.setValue(bar.value() + int(self.scroll.viewport().height() * 0.8))

    def _queue_section_more(self, state, select=False):
        if not state["pending"] or state not in self._section_batches:
            return
        state["select"] |= select
        if not state["queued"]:
            state["queued"] = True
            QTimer.singleShot(0, lambda s=state: self._load_more_section(s))

    def _load_more_section(self, state):
        state["queued"] = False
        if not state["pending"] or state not in self._section_batches:
            return
        first = state["loaded"]
        batch, state["pending"] = state["pending"][:self.CARD_BATCH], state["pending"][self.CARD_BATCH:]
        for task in batch:
            card = TaskCard(self, task, 0, 0)
            state["layout"].insertWidget(state["layout"].count() - 1, card)
            card.show()
            state["cards"].append(card)
            state["loaded"] += 1
        self._sync_nav_cards()
        if state["select"]:
            state["select"] = False
            state["cards"][first].select()

    def _section_scrolled(self, state):
        if self._refreshing_cards or not self.isVisible() or state not in self._section_batches:
            return
        bar = state["box"].verticalScrollBar()
        if bar.value() > 0 and bar.maximum() - bar.value() <= state["box"].viewport().height():
            self._queue_section_more(state)

    def fast_remove(self, task):
        """A note left the main list (deleted, let go, done, Later): take its card out in place instead of
        rebuilding every card, then rebuild only the small Later / Completed sections. Returns False when a full
        refresh is needed instead (searching, or the list would become empty)."""
        if self.is_filtering() or self._main_pending or any(s["pending"] for s in self._section_batches):
            return False
        main = self._main_cards()
        card = next((c for c in main if c.task is task), None)
        if card is None or len(main) == 1:
            return False
        self.list_lay.removeWidget(card)
        card.hide()
        card.deleteLater()
        main.remove(card)
        tasks = self.store.tasks
        later_t = [t for t in tasks if not t["done"] and t.get("later")]
        done_t = [t for t in tasks if t["done"]]
        self._build_sections(later_t, done_t)
        section_cards = [c for c in self.sections.findChildren(TaskCard) if self._alive(c)]
        self._nav_cards = main + section_cards
        pending = getattr(self, "_pending_select", None)
        self._pending_select = None
        if pending is not None:
            QTimer.singleShot(0, lambda: self.select_index(min(pending, len(main) - 1)))
        QTimer.singleShot(0, self._update_more)
        QTimer.singleShot(0, self._place_toast)
        self.update_counts()
        self.bubble.set_count(self.store.open_count())
        self.refresh_tab_counts()
        self._built_fp = self._fingerprint()
        return True

    def fast_add(self, task):
        """A new note in the current list: insert just its card where it belongs (no full rebuild)."""
        if (self.is_filtering() or self._main_pending or any(s["pending"] for s in self._section_batches)
                or task not in self.store.tasks):
            return False
        main = self._main_cards()
        order = self.open_in_order()
        if not main or task not in order or len(order) != len(main) + 1:
            return False
        pos = order.index(task)
        card = TaskCard(self, task, pos, len(order))
        card.setMaximumHeight(0)
        self.list_lay.insertWidget(pos, card)
        QTimer.singleShot(0, lambda: self._animate_card(card, out=False))
        main.insert(pos, card)
        self._nav_cards = main + [c for c in self.sections.findChildren(TaskCard) if self._alive(c)]
        QTimer.singleShot(0, self._update_more)
        self.update_counts()
        self.bubble.set_count(self.store.open_count())
        self.refresh_tab_counts()
        self._built_fp = self._fingerprint()
        return True

    _pill_owner = None

    def set_pill_owner(self, card):
        """The note whose Later / Let go / Delete pill is showing is the one lit up (mouse or keys alike)."""
        old, self._pill_owner = self._pill_owner, card
        for c in (old, card, self.focusWidget()):
            if isinstance(c, TaskCard) and self._alive(c):
                c.update()

    OUT_MS = 180            # a note folding away (Done, Later, Let go, Delete)
    IN_MS = 170             # a new note opening up

    GHOST = {   # (dx, dy, end scale, spin degrees, tint, ms)
        "done": (40, 0, 0.96, 0, "#4cc38a", 300),         # a green nod, slides off to the right
        "later": (0, 70, 0.7, 0, "#6b93f0", 320),         # sinks down toward the Later section, shrinking
        "let_go": (0, -60, 0.9, -6, "#9ecfa0", 380),      # floats up and away like a leaf, a slight turn
        "deleted": (0, 0, 0.55, 0, "#ef5a5f", 220),       # a quick red shrink into nothing
    }

    def _ghost(self, card, kind):
        """Paint a copy of the note on top and send it on its way (the real card is already folding)."""
        spec = self.GHOST.get(kind)
        if spec is None:
            return
        try:
            pix = card.grab()
            top_left = card.mapTo(self, QPoint(0, 0))
        except RuntimeError:
            return
        g = Ghost(self, pix, QRect(top_left, pix.size() / pix.devicePixelRatio()), *spec)
        g.run()

    def remove_later(self, task, pause_ms=0, kind=None):
        """The note leaves the main list: it fades while its space folds shut, so the notes below glide up
        instead of jumping; then fast_remove() takes the card out. pause_ms lets a tick show first (Done).
        Never runs inside the card's own click handler (zero-delay timer at least)."""
        def go():
            card = next((c for c in self._main_cards() if c.task is task), None)
            if card is None or self.is_filtering() or not self.isVisible():
                None if self.fast_remove(task) else self.refresh()
                return
            if kind:
                self._ghost(card, kind)
            self._animate_card(card, out=True, done=lambda: None if self.fast_remove(task) else self.refresh(),
                               hide_now=bool(kind))
        QTimer.singleShot(pause_ms, go)

    def _animate_card(self, card, out, done=None, hide_now=False):
        """Fold a card shut (out) or open it up (in): height and opacity together, eased. hide_now: a ghost
        carries the note away, so the card itself is invisible while its space closes."""
        try:
            card.actions.hide()
        except RuntimeError:
            return
        h = max(1, card.sizeHint().height() if not out else card.height())
        eff = QGraphicsOpacityEffect(card)
        card.setGraphicsEffect(eff)
        anim = QVariantAnimation(card)
        anim.setDuration(self.OUT_MS if out else self.IN_MS)
        anim.setStartValue(0.0)
        anim.setEndValue(1.0)
        anim.setEasingCurve(QEasingCurve.InOutCubic if out else QEasingCurve.OutCubic)

        def step(v):
            v = float(v)
            k = 1.0 - v if out else v
            try:
                eff.setOpacity(0.0 if hide_now else (max(0.0, min(1.0, k * 1.15 - 0.15)) if out else min(1.0, k * 1.3)))
                card.setMaximumHeight(int(h * k))
            except RuntimeError:
                anim.stop()

        def finished():
            try:
                if not out:
                    card.setMaximumHeight(16777215)
                    card.setGraphicsEffect(None)
            except RuntimeError:
                pass
            if done:
                done()
        anim.valueChanged.connect(step)
        anim.finished.connect(finished)
        step(0.0)
        anim.start()

    @staticmethod
    def _alive(w):
        try:
            w.isVisible()
            return True
        except RuntimeError:
            return False

    SORTS = [("manual", "My order (newest on top, Alt+arrows to move)"), ("oldest", "Oldest first"),
             ("newest", "Newest first (by time added)"), ("az", "A to Z"), ("za", "Z to A")]

    def sorted_notes(self, notes):
        """The Sort setting, with urgent notes always on top."""
        how = self.store.settings.get("sort", "manual")
        notes = list(notes)
        if how == "oldest":
            notes.sort(key=lambda t: t.get("created", ""))
        elif how == "newest":
            notes.sort(key=lambda t: t.get("created", ""), reverse=True)
        elif how in ("az", "za"):
            notes.sort(key=lambda t: t.get("title", "").strip().lower(), reverse=how == "za")
        use_urgent = flag_on(self.store.settings, "urgent")
        notes.sort(key=lambda t: not (use_urgent and t.get("urgent") and not t["done"]))
        return notes

    def open_in_order(self):
        """Open notes of the current list as shown: urgent first, then the Sort setting (default: stored order,
        newest on top)."""
        return self.sorted_notes(t for t in self.store.tasks if not t["done"] and not t.get("later"))

    # ---- search, filter, sort
    NO_FILTER = {"flags": [], "show": "active", "days": None}   # search defaults to Open and Later

    def is_filtering(self):
        f = self.filters
        return bool(self.find_edit.text().strip() or f["flags"] or f["show"] != "active" or f["days"])

    def filtered_tasks(self):
        """Notes of the current list that match the search text (title and details) and the filters."""
        f, q = self.filters, self.find_edit.text().strip().lower()
        show = f["show"]
        cutoff = (datetime.now() - timedelta(days=f["days"])).isoformat(timespec="seconds") if f["days"] else ""
        out = []
        for t in self.store.tasks:
            state = "done" if t["done"] else "later" if t.get("later") else "open"
            if show == "active" and state == "done":
                continue
            if show not in ("all", "active") and state != show:
                continue
            if f["flags"] and not any(t.get(k) for k in f["flags"]):
                continue
            if cutoff and t.get("created", "") < cutoff:
                continue
            if q and q not in (t.get("title", "") + "\n" + t.get("desc", "")).lower():
                continue
            out.append(t)
        return self.sorted_notes(out)

    def toggle_search(self, show=None):
        show = not self.find_row.isVisible() if show is None else show
        self.find_row.setVisible(show)
        if show:
            self.find_edit.setFocus()
            self.find_edit.selectAll()
        else:
            self.clear_filters()
            self.quick.setFocus()

    def _maybe_hide_search(self):
        """Clicked somewhere else with nothing typed and no filter on: the search row folds away.
        With a search or filter active it stays, so the list doesn't jump back while you work on the results."""
        if (self.find_row.isVisible() and not self.find_edit.hasFocus() and not self.is_filtering()
                and QApplication.activePopupWidget() is None):
            self.find_row.setVisible(False)

    def clear_filters(self):
        self.find_edit.blockSignals(True)
        self.find_edit.clear()
        self.find_edit.blockSignals(False)
        self.filters = dict(self.NO_FILTER, flags=[])
        self._update_find_labels()
        self.refresh_later()

    def _find_changed(self, _text):
        self._update_find_labels()
        self.refresh_later()

    def _set_filter(self, key, value):
        self.filters[key] = value
        self._update_find_labels()
        self.refresh_later()

    def _toggle_flag_filter(self, k, on):
        fl = [x for x in self.filters["flags"] if x != k] + ([k] if on else [])
        self._set_filter("flags", fl)

    def _update_find_labels(self):
        """Chips under the search box for each active filter and a non-default sort; click one to drop it."""
        f = self.filters
        while self.chips_lay.count():
            w = self.chips_lay.takeAt(0).widget()
            if w:
                w.hide()
                w.deleteLater()
        chips = []
        icons = {k: (icon, word) for k, icon, word, _ in FLAG_DEFS}
        for k in f["flags"]:
            icon, word = icons[k]
            chips.append((f"{icon} {word}", lambda _=False, kk=k: self._toggle_flag_filter(kk, False)))
        if f["show"] != "active":
            chips.append(({"all": "Include Completed", "open": "Open only", "later": "Later only",
                           "done": "Completed only"}[f["show"]],
                          lambda _=False: self._set_filter("show", "active")))
        if f["days"]:
            chips.append(({1: "Last 24 h", 7: "Last 7 days", 30: "Last 30 days"}[f["days"]],
                          lambda _=False: self._set_filter("days", None)))
        how = self.store.settings.get("sort", "manual")
        if how != "manual":
            chips.append(("Sort: " + {"oldest": "oldest first", "newest": "newest first", "az": "A to Z",
                                      "za": "Z to A"}[how], lambda _=False: self.set_sort("manual")))
        for text, fn in chips:
            b = QToolButton(self.chips_row)
            b.setObjectName("filterChip")
            b.setText(text + "  \u2715")
            b.setToolTip("Click to remove")
            b.setCursor(Qt.PointingHandCursor)
            b.clicked.connect(fn)
            self.chips_lay.addWidget(b)
        self.chips_lay.addStretch(1)
        self.chips_row.setVisible(bool(chips))
        n = len(chips) - (how != "manual")
        self.funnel.setIcon(funnel_icon(C["accent"] if n else C["dim"]))
        on = self.is_filtering()
        self.findb.setStyleSheet(f"color: {C['accent_text']};" if on else "")

    def _filter_menu(self):
        m = QMenu(self)
        m.setStyleSheet(STYLE)
        f = self.filters
        m.addSection("Flags (any of)")
        for key, icon, word, tip in FLAG_DEFS:
            if not flag_on(self.store.settings, key):
                continue
            a = m.addAction(f"{icon}  {word[0].upper() + word[1:]}")
            a.setCheckable(True)
            a.setChecked(key in f["flags"])
            a.toggled.connect(lambda on, k=key: self._toggle_flag_filter(k, on))
        m.addSection("Show")
        g = QActionGroup(m)
        for key, label in (("active", "Open + Later (default)"), ("all", "Include Completed"),
                           ("open", "Open only"), ("later", "Later only"), ("done", "Completed only")):
            a = m.addAction(label)
            a.setCheckable(True)
            a.setChecked(f["show"] == key)
            g.addAction(a)
            a.triggered.connect(lambda _=False, k=key: self._set_filter("show", k))
        m.addSection("Added")
        g2 = QActionGroup(m)
        for days, label in ((None, "Any time"), (1, "Last 24 hours"), (7, "Last 7 days"), (30, "Last 30 days")):
            a = m.addAction(label)
            a.setCheckable(True)
            a.setChecked(f["days"] == days)
            g2.addAction(a)
            a.triggered.connect(lambda _=False, d=days: self._set_filter("days", d))
        m.addSection("Sort")
        g3 = QActionGroup(m)
        cur = self.store.settings.get("sort", "manual")
        for key, label in self.SORTS:
            a = m.addAction(label)
            a.setCheckable(True)
            a.setChecked(cur == key)
            g3.addAction(a)
            a.triggered.connect(lambda _=False, k=key: self.set_sort(k))
        m.addSeparator()
        m.addAction("Clear search and filters", self.clear_filters)
        keep_menu_open(m)
        return m

    def _sort_menu(self):
        m = QMenu(self)
        m.setStyleSheet(STYLE)
        g = QActionGroup(m)
        cur = self.store.settings.get("sort", "manual")
        for key, label in self.SORTS:
            a = m.addAction(label)
            a.setCheckable(True)
            a.setChecked(cur == key)
            g.addAction(a)
            a.triggered.connect(lambda _=False, k=key: self.set_sort(k))
        return m

    def set_sort(self, key):
        self.store.settings["sort"] = key
        self.store.save()
        self._update_find_labels()
        self.refresh_later()

    def open_history(self):
        dlg = getattr(self, "_history", None)
        if dlg is None:
            dlg = self._history = HistoryDialog(self.store, self)
        dlg.reload()
        dlg.show()
        dlg.raise_()
        dlg.activateWindow()

    def open_notes_text(self):
        """Copy the notes shown by search/filter, or all open notes when neither is active."""
        lines = []
        notes = self.filtered_tasks() if self.is_filtering() else self.open_in_order()
        for t in notes:
            lines.append(f"- {t['title'].strip() or 'Untitled'}")
            lines += [f"  - {d.strip()}" for d in t.get("desc", "").splitlines() if d.strip()]
        return "\n".join(lines)

    def copy_all(self):
        text = self.open_notes_text()
        if not text:
            return
        QGuiApplication.clipboard().setText(text)
        self.copy_all_btn.flash()

    def _escape(self, from_quick=False):
        """Esc in the top box with something typed or tagged: wipe it for a fresh start. Otherwise close the list."""
        typing = (from_quick or bool(self.quick_reminder) or self.quick.hasFocus() or self.reminder_btn.hasFocus() or
                  any(b.hasFocus() for b in self.qflags.values()))
        if typing and (self.quick.text().strip() or self.quick_reminder or
                       any(b.isChecked() for b in self.qflags.values())):
            self._reset_quick()
            self.quick.setFocus()
        else:
            self.hide()

    def build_quick_flags(self):
        """The flag buttons under the top box, in your flag order (rebuilt when you add or reorder flags)."""
        if hasattr(self, "flag_number_guide"):
            self.flag_number_guide.clear()
        keep = {k for k, b in self.qflags.items() if b.isChecked()}
        while self.qrow.count():
            w = self.qrow.takeAt(0).widget()
            if w:
                w.hide()
                w.deleteLater()
        self.qflags = {}
        visible_keys = [k for k in FLAG_KEYS if flag_on(self.store.settings, k)]
        for key, icon, _word, tip in FLAG_DEFS:
            b = QToolButton(self)
            b.setObjectName("flag")
            b.setProperty("kind", key)
            b.setText(icon)
            number = visible_keys.index(key) + 1 if key in visible_keys else 0
            b.setToolTip(f"{icon} {_word}" + (f" (Alt+{number})" if 1 <= number <= 9 else ""))
            b.setProperty("flaghint", tip.split(". ")[0])
            b.setProperty("flagword", _word)
            b.setCheckable(True)
            b.setChecked(key in keep)
            b.setFocusPolicy(Qt.StrongFocus)
            b.installEventFilter(self)
            self.qrow.addWidget(b)
            b.setVisible(flag_on(self.store.settings, key))
            self.qflags[key] = b
        self.qrow.addStretch(1)
        chain = [self.quick] + [self.qflags[k] for k in FLAG_KEYS] + [self.reminder_btn, self.send_btn]
        for a, b2 in zip(chain, chain[1:]):
            QWidget.setTabOrder(a, b2)

    def flags_changed(self):
        """You added, edited, removed or reordered flags."""
        configure_flags(self.store.settings)
        self.setStyleSheet(full_style())
        self.build_quick_flags()
        self._update_find_labels()
        self.refresh_later()

    def apply_flag_settings(self):
        """Called when flags are switched on/off in Settings."""
        for k, b in self.qflags.items():
            b.setVisible(flag_on(self.store.settings, k))
            if not b.isVisible():
                b.setChecked(False)
        self.refresh_later()

    def clear_completed(self):
        n = sum(1 for t in self.store.tasks if t["done"])
        token = self.store.clear_done()
        self.refresh_later()

        def undo():
            self.store.undo_clear(token)
            self.refresh_later()
        self._push_undo(f"Cleared {n} completed", undo)

    def _toggle_section(self, key):
        st = self.store.settings
        st["open_section"] = None if st.get("open_section") == key else key
        self.store.save()
        self.refresh_later()

    def _pill_over(self, rect):
        """Is a note's Copy / Later / Let go / Delete pill showing inside this rect (viewport coordinates)?"""
        vp = self.scroll.viewport()
        for c in getattr(self, "_nav_cards", []):
            try:
                a = c.actions
                if a.isVisible():
                    tl = a.mapTo(vp, QPoint(0, 0))
                    if QRect(tl, a.size()).adjusted(-4, -4, 4, 4).intersects(rect):
                        return True
            except RuntimeError:
                continue
        return False

    def _update_more(self):
        """Pill at the bottom of the list when some thoughts are below the visible area."""
        vp = self.scroll.viewport()
        bottom = self.scroll.verticalScrollBar().value() + vp.height()
        cards = [self.list_lay.itemAt(i).widget() for i in range(self.list_lay.count())]
        hidden = len(self._main_pending) + sum(1 for c in cards if isinstance(c, TaskCard)
                                               and c.y() + c.height() * 0.5 > bottom)
        if hidden:
            self.more.setText(f"\u2193 {hidden} more")
            self.more.adjustSize()
            self.more.move(8, vp.height() - self.more.height() - 4)   # left corner: note buttons sit on the right
            if self._pill_over(self.more.geometry()):
                self.more.hide()                          # still in the way: the buttons win, it comes back after
            else:
                self.more.show()
                self.more.raise_()
        else:
            self.more.hide()
        self._place_toast()     # the toast sits above the "more" pill, never on it

    # ---- the ways out at the break
    def set_later(self, task, on):
        cards = [c for c in getattr(self, "_nav_cards", []) if c.isVisible()]
        kb = next((c for c in cards if c.task is task and any(b.hasFocus() for b in c.act_btns)), None)
        if kb is not None:
            self._pending_select = cards.index(kb)
        task["later"] = bool(on)
        self.store.log_event("later_on" if on else "later_off", task)
        self.store.save()
        self.remove_later(task, kind="later") if on else self.refresh_later()

        def undo():
            task["later"] = not on
            self.store.log_event("later_off" if on else "later_on", task, undo=True)
            self.store.save()
            self.refresh_later(task["id"], select=True)
        self._push_undo("\U0001F552  Out of sight till later" if on else "Back in the list", undo)

    def move_to_list(self, task, target, card=None):
        if card is not None and card.hasFocus():
            cards = [c for c in self._nav_cards if c.isVisible()]
            self._pending_select = cards.index(card) if card in cards else 0   # stay on the next note
        token = self.store.move_to_list(task, target)
        if token is None:
            return
        self.refresh_tabs()
        self.refresh_later()

        def undo():
            self.store.undo_move_to_list(task, token)
            self.refresh_tabs()
            self.refresh_later(task["id"], select=True)
        self._push_undo(f"→  Moved to {target['name']}", undo)

    _nav_cursor = None

    def live_cards(self):
        out = []
        for c in getattr(self, "_nav_cards", []):
            try:
                c.isVisible()
                out.append(c)
            except RuntimeError:        # already deleted by a refresh
                pass
        return out

    def hide_pills(self, keep=None):
        """Only one Later / Let go pill at a time."""
        for c in self.live_cards():
            if c is not keep and not c.pill_in_use():
                c.actions.hide()

    def delete_task(self, task, card=None):
        """For mistakes and test notes: gone from the list, kept in trash, left out of every analysis."""
        self.let_go(task, card, kind="deleted")

    def let_go(self, task, card=None, kind="let_go"):
        """Fade the card, then release the thought (logged, recoverable), with Undo for a few seconds."""
        if card is not None and (card.hasFocus() or any(b.hasFocus() for b in card.act_btns)):
            cards = [c for c in self._nav_cards if c.isVisible()]
            self._pending_select = cards.index(card) if card in cards else 0

        token = self.store.let_go(task, kind)
        self.remove_later(task, kind=kind)  # its own motion, while the notes below glide up

        def undo():
            self.store.undo_let_go(task, token)
            self.refresh_later(task["id"], select=True)
        self._push_undo("Left out of your patterns" if kind == "deleted" else "\U0001F343  Logged, not lost", undo)

    # ---- undo (the toast button, or Ctrl+Z anywhere in the list)
    def _push_undo(self, label, fn, toast=True):
        self._undo_stack.append((label, fn))
        del self._undo_stack[:-30]
        if toast:
            self._toast(label, can_undo=True)

    def _toast(self, text, can_undo=False, ms=6000):
        self.toast_text.setText(text)
        self.toast_undo.setVisible(can_undo)
        self.toast.show()
        self._place_toast()
        self.toast.raise_()
        self.toast_timer.start(ms)

    def _place_toast(self):
        """Centre the pill horizontally, just above the bottom of the list (and above the "more" pill)."""
        if not self.toast.isVisible():
            return
        self.toast.adjustSize()
        vp = self.scroll.viewport()
        bottom = vp.mapTo(self, QPoint(0, vp.height())).y()
        lift = self.more.height() + 12 if self.more.isVisible() else 10
        r = self.card_rect()
        x = int(r.center().x() - self.toast.width() / 2)
        self.toast.move(x, bottom - self.toast.height() - lift)

    def undo_last(self):
        if not self._undo_stack:
            self._toast("Nothing to undo", ms=1500)
            return
        label, fn = self._undo_stack.pop()
        fn()
        more = f" \u00B7 {len(self._undo_stack)} more with Ctrl+Z" if self._undo_stack else ""
        self._toast("\u21A9  Undone" + more, ms=2500)

    def _do_undo(self):   # kept for older callers
        self.undo_last()

    def _restore_position(self, task, l, idx):
        if task in l["tasks"]:
            l["tasks"].remove(task)
            l["tasks"].insert(min(idx, len(l["tasks"])), task)

    def _empty_state(self, has_done):
        w = QWidget()
        lay = QVBoxLayout(w)
        lay.setContentsMargins(10, 36, 10, 10)
        lay.setSpacing(6)
        face = EmojiFace(34)
        lay.addWidget(face, 0, Qt.AlignHCenter)
        face.set("\U0001F389" if has_done else "\U0001F9D8", "bounce" if has_done else "float")
        t = QLabel("All clear" if has_done else "Nothing parked")
        t.setObjectName("emptyTitle")
        t.setAlignment(Qt.AlignCenter)
        s1 = QLabel("When a thought pulls at you mid-focus, park it here and get back to work. "
                    "Decide what to do with it at your break.")
        s1.setObjectName("emptyText")
        s1.setWordWrap(True)
        s1.setAlignment(Qt.AlignCenter)
        s2 = QLabel("Type above \u00B7 paste a snip \u00B7 drop files here or on the circle\n"
                    "Files wait on the shelf; drag them back out when you need them")
        s2.setObjectName("hint")
        s2.setAlignment(Qt.AlignCenter)
        for x in (t, s1, s2):
            lay.addWidget(x)
        return w

    def _set_link(self, on):
        self.store.settings["auto_break"] = bool(on)
        self.store.save()

    def _start_from(self, spin, kind):
        """Use exactly what's typed, even if the box still has focus (Start buttons don't take focus).
        The adjacent Focus or Break button is the explicit start action."""
        spin.interpretText()
        if self.timer:
            self.timer.start(spin.value(), kind)

    def _spin(self, key, default, hi, tip):
        sp = MinSpin()
        sp.setObjectName("minSpin")
        sp.setDecimals(1)
        sp.setRange(0.1, hi)
        sp.setSingleStep(0.5)
        sp.setValue(float(self.store.settings.get(key, default)))
        sp.setToolTip(tip + ". Type a number (0.5 = 30 seconds), or scroll over it.")
        sp.setKeyboardTracking(False)
        sp.setButtonSymbols(QDoubleSpinBox.NoButtons)
        sp.setAlignment(Qt.AlignLeft | Qt.AlignVCenter)
        sp.setSuffix("")                       # only the number belongs inside the cursor field

        def changed(val):
            self.store.settings[key] = val
            self.store.save()
        sp.valueChanged.connect(changed)
        return sp

    def _help_menu(self, anchor):
        m = QMenu(self)
        m.setStyleSheet(STYLE)
        m.addAction("How it works", lambda: self.help.show_at(anchor.mapToGlobal(anchor.rect().bottomRight())))
        m.addAction("Take the quick tour", lambda: getattr(self, "tour_starter", lambda: None)())
        m.addSeparator()
        m.addAction(f"About {APP_NAME}", self.show_about)
        m.exec(anchor.mapToGlobal(anchor.rect().bottomLeft()))

    def show_about(self):
        def link(url, label):
            return f"<a style='color:{C['urge']}' href='{url}'>{label}</a>" if url else f"{label} (coming soon)"
        box = QMessageBox(self)
        box.setWindowTitle(f"About {APP_NAME}")
        box.setStyleSheet(STYLE + f"QMessageBox {{ background: {C['bg']}; }}")
        box.setTextFormat(Qt.RichText)
        box.setText(f"<b>{APP_NAME}</b> {APP_VERSION}<br>{APP_TAGLINE}<br><br>Made by {APP_AUTHOR}.<br><br>"
                    f"{link(GITHUB_URL, 'GitHub')}<br>{link(COFFEE_URL, 'Buy me a coffee')}<br><br>"
                    f"<span style='color:{C['dim']}'>Thoughts stay local. Calendar and phone alerts are optional. No tracking.</span>")
        box.setTextInteractionFlags(Qt.TextBrowserInteraction)
        for lab in box.findChildren(QLabel):
            lab.setOpenExternalLinks(True)
        box.exec()

    def _open_ai_menu(self, anchor):
        if getattr(self, "ai_menu_builder", None):
            m = self.ai_menu_builder()
            m.exec(anchor.mapToGlobal(anchor.rect().bottomLeft()))

    def _open_settings(self, anchor):
        if getattr(self, "settings_opener", None):
            self.settings_opener()
            return
        if getattr(self, "menu_builder", None):
            m = self.menu_builder()
            m.exec(anchor.mapToGlobal(anchor.rect().bottomLeft()))
            self.update_timer_row()

    def _mins(self, kind):
        st = self.store.settings
        return st.get("break_min", DEFAULT_BREAK_MIN) if kind == "break" else st.get("focus_min", DEFAULT_FOCUS_MIN)

    def take_out_drift(self):
        take_out_drift(self.timer, self)
        self.update_timer_row()

    def update_timer_row(self):
        tm = self.timer
        if not tm:
            self.timer_row.hide()
            return
        fm, bm = self._mins("focus"), self._mins("break")
        if tm.running and tm.kind == "break":
            on = tm.state.get("on")
            text = "Break" + (f" \u00B7 {short_text(on, 14)}" if on else "") + f" \u00B7 {fmt_mmss(tm.remaining())} left"
            color = C["glimmer"]
            btns = [("End break", lambda: (tm.stop(), None))]
            if self.ask_tag:
                btns.append(("For...", self.ask_tag, "What's this break for (meal, call, rest, walk)"))
        elif tm.running:
            on = tm.state.get("on")
            text = (("Paused" if tm.paused else "Focus") + (f" \u00B7 {short_text(on, 14)}" if on else "")
                    + f" \u00B7 {fmt_mmss(tm.remaining())} left")
            color = C["timer"]
            btns = [("Resume" if tm.paused else "Pause", tm.resume if tm.paused else tm.pause),
                    ("Stop", tm.stop), ("Drifted", self.take_out_drift, DRIFT_TIP)]
            if self.ask_tag:
                btns.append(("For...", self.ask_tag, "What's this round for (shows on the session card and in the AI export)"))
        elif tm.overrun_since:
            text, color = tm.overrun_label(), C["idea"]
            btns = [(f"Start focus {fmt_min(fm)} min", lambda: tm.start(fm, "focus")), ("I'm back", tm.clear_overrun)]
        else:
            # idle: editable minutes (keep them in sync if changed from the menu)
            for sp, val in ((self.focus_spin, fm), (self.break_spin, bm)):
                if abs(sp.value() - float(val)) > 1e-6 and not sp.hasFocus():
                    sp.blockSignals(True)
                    sp.setValue(float(val))
                    sp.blockSignals(False)
            want = bool(self.store.settings.get("auto_break", False))
            if self.link.isChecked() != want:
                self.link.blockSignals(True)
                self.link.setChecked(want)
                self.link._sync_tip(want)
                self.link.blockSignals(False)
            self.idle_box.show()
            self.timer_label.hide()
            for b in self.timer_btns:
                b.hide()
            self.timer_row.show()
            return
        self.idle_box.hide()
        self.timer_label.show()
        self.timer_label.setText(text)
        self.timer_label.setStyleSheet(f"color: {color};")
        for b, spec in zip(self.timer_btns, btns + [None] * 4):
            if spec:
                b.setText(spec[0])
                b.setProperty("action", spec[1])
                b.setToolTip(spec[2] if len(spec) > 2 else "")
                b.show()
            else:
                b.hide()
        self.timer_row.show()

    # ---- actions
    def _quick_flags(self):
        return {k: b.isChecked() for k, b in self.qflags.items()}

    def _reset_quick(self):
        self.quick.setText("")     # setText also clears the box's own undo history, so Ctrl+Z goes to the list
        self.quick_reminder = None
        self._refresh_quick_reminder()
        for b in self.qflags.values():
            b.setChecked(False)
        self.quick.setFocus()

    def _quick_add(self):
        text = self.quick.text().strip()
        if text:
            clean, inline_reminder = extract_inline_reminder(text)
            if not clean:
                return
            t = self.store.new_task(clean, source="list", log=False)
            t.update(self._quick_flags())
            if self.quick_reminder or inline_reminder:
                t["reminder"] = (self.quick_reminder or inline_reminder).copy()
            self.store.log_captured(t)
            self.store.save()
            self._reset_quick()
            def show_saved():
                if not self.fast_add(t):
                    self.refresh()
                if t.get("reminder"):
                    self._toast(reminder_confirmation(t["reminder"]), ms=4000)
            QTimer.singleShot(0, show_saved)

    def _edit_quick_reminder(self):
        changed, value = edit_reminder(self, self.quick_reminder, self.reminder_btn)
        if changed:
            self.quick_reminder = value
            self._refresh_quick_reminder()

    def _refresh_quick_reminder(self):
        show_reminder_chip(self.reminder_btn, self.quick_reminder)

    def paste_into(self, task):
        return self.attach_mime(task, QGuiApplication.clipboard().mimeData())

    def attach_mime(self, task, md):
        """Attach copied/dropped files or an image. Returns False for plain text (normal paste)."""
        if md.hasUrls():
            paths = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
            if paths:
                for p in paths:
                    self.store.add_path(task, p)
                self.refresh_later(task["id"])
                return True
        if md.hasImage() and not md.hasText():
            img = QImage(md.imageData())
            if not img.isNull():
                self.store.add_image(task, img)
                self.refresh_later(task["id"])
                return True
        return False

    def eventFilter(self, obj, e):
        if (e.type() == QEvent.KeyPress and obj in [getattr(self, "quick", None),
                *getattr(self, "qflags", {}).values()] and e.modifiers() == Qt.AltModifier
                and Qt.Key_1 <= e.key() <= Qt.Key_9):
            toggle_numbered_flag(self.qflags, self.store.settings, int(e.key()) - int(Qt.Key_0))
            return True
        if obj is getattr(self, "quick", None) and e.type() == QEvent.KeyPress and e.key() == Qt.Key_Escape:
            self._escape(from_quick=True)
            return True
        if (obj is getattr(self, "find_edit", None) and e.type() == QEvent.ShortcutOverride
                and e.key() == Qt.Key_Escape):
            e.accept()                                # keep Esc for the search box (the list's Esc closes it)
            return True
        if obj is getattr(self, "find_edit", None) and e.type() == QEvent.FocusOut:
            QTimer.singleShot(200, self._maybe_hide_search)
        if obj is getattr(self, "find_edit", None) and e.type() == QEvent.KeyPress:
            if e.key() == Qt.Key_Escape:              # Esc: clear and close the search row, not the whole list
                self.toggle_search(False)
                return True
            if e.key() == Qt.Key_Down:                # Down: into the matching notes, like from the top box
                self.select_index(0) if any(c.isVisible() for c in getattr(self, "_nav_cards", [])) else None
                return True
        if obj in getattr(self, "qflags", {}).values():
            flag_focus_hint(obj, e)
            # Space marks flags (as many as you like). Enter marks this one too and parks the note.
            # Ctrl+Enter parks exactly what's marked.
            if e.type() == QEvent.KeyPress and e.key() in (Qt.Key_Return, Qt.Key_Enter):
                if not (e.modifiers() & Qt.ControlModifier):
                    obj.setChecked(True)
                if self.quick.text().strip():
                    self._quick_add()
                return True
        if (obj is getattr(self, "quick", None) and e.type() == QEvent.ShortcutOverride
                and e.matches(QKeySequence.Undo) and not self.quick.isUndoAvailable()):
            e.ignore()          # nothing typed to undo: let Ctrl+Z reach the list's undo
            return True
        if (obj is getattr(self, "quick", None) and e.type() == QEvent.KeyPress and e.key() == Qt.Key_Down
                and (not self.quick.text() or (self.quick.cursor_on_last_line() and self.quick.textCursor().atEnd()))):
            self.select_index(0) if any(c.isVisible() for c in getattr(self, "_nav_cards", [])) else None
            return True
        if obj is getattr(self, "quick", None) and e.type() == QEvent.KeyPress and e.matches(QKeySequence.Paste):
            md = QGuiApplication.clipboard().mimeData()
            if md.hasUrls() or (md.hasImage() and not md.hasText()):
                title = self.quick.text().strip() or f"Snip {datetime.now():%H:%M}"
                t = self.store.new_task(title, source="list_paste", log=False)
                if self.attach_mime(t, md):
                    t.update(self._quick_flags())
                    if self.quick_reminder:
                        t["reminder"] = self.quick_reminder.copy()
                    self.store.log_captured(t)
                    self.store.save()
                    self._reset_quick()
                    return True
                self.store.discard_new(t)
        return super().eventFilter(obj, e)

    def task_from_mime(self, md, title="", source="list_drop", flags=None):
        """New task from dropped/pasted files, image or text. Returns the task, or None if nothing usable."""
        local = [u.toLocalFile() for u in md.urls() if u.isLocalFile()] if md.hasUrls() else []
        if local or (md.hasImage() and not md.hasText()):
            name = title or (Path(local[0]).name if local else f"Snip {datetime.now():%H:%M}")
            t = self.store.new_task(name, source=source, log=False)
            if self.attach_mime(t, md):
                t.update(flags or {})
                self.store.log_captured(t)
                self.refresh_later()
                return t
            self.store.discard_new(t)
            return None
        text = md.text().strip() if md.hasText() else ""
        if md.hasUrls() and not text:
            text = "\n".join(u.toString() for u in md.urls())
        if not text:
            return None
        first = text.splitlines()[0].strip()
        t = self.store.new_task(title or (first[:80] + ("\u2026" if len(first) > 80 else "")),
                                source=source, log=False)
        if title or len(text) > len(first) or len(first) > 80:
            t["desc"] = text
        t.update(flags or {})
        self.store.log_captured(t)
        self.store.save()
        self.refresh_later()
        return t

    def dragEnterEvent(self, e):
        md = e.mimeData()
        if isinstance(e.source(), AttachmentTile):
            e.ignore()                     # a file on its way out of the shelf, not a new drop
            return
        if md.hasUrls() or md.hasImage() or md.hasText():
            e.acceptProposedAction()
            self.drop_banner.show()

    def dragLeaveEvent(self, e):
        self.drop_banner.hide()

    def dropEvent(self, e):  # dropped on empty space: new task
        self.drop_banner.hide()
        if self.task_from_mime(e.mimeData()):
            e.acceptProposedAction()
            if self.store.settings.get("close_on_outside", False):
                force_foreground(self)    # a drop counts as using the list: keep it, until the next outside click

    def move_task(self, task, delta, keep_selected=False):
        """Alt+Up/Down: swap with the neighbour you see above/below it. Urgent tasks stay above the rest."""
        if task["done"]:
            return
        if self.store.settings.get("sort", "manual") != "manual" or self.is_filtering():
            self._toast("Moving works in My order with no search or filter", ms=3000)
            return
        later = bool(task.get("later"))
        use_urgent = flag_on(self.store.settings, "urgent")
        shown = [t for t in self.store.tasks if not t["done"] and bool(t.get("later")) == later]
        if not later:
            shown.sort(key=lambda t: not (use_urgent and t.get("urgent")))
        k = shown.index(task)
        j = k + delta
        if not 0 <= j < len(shown):
            return
        other = shown[j]
        if not later and use_urgent and bool(other.get("urgent")) != bool(task.get("urgent")):
            return   # can't move a normal task above an urgent one (unmark urgent first)
        ts = self.store.tasks
        a, b = ts.index(task), ts.index(other)
        ts[a], ts[b] = ts[b], ts[a]
        self.store.log_event("moved", task, direction="up" if delta < 0 else "down")
        self.store.save()

        def undo():
            if task in ts and other in ts:
                i, j = ts.index(task), ts.index(other)
                ts[i], ts[j] = ts[j], ts[i]
                self.store.log_event("moved", task, direction="down" if delta < 0 else "up", undo=True)
                self.store.save()
            self.refresh_later(task["id"], select=True)
        self._push_undo("Moved", undo, toast=False)
        if keep_selected:
            self.refresh_later(task["id"], select=True)
        else:
            self.refresh_later(task["id"])

    # ---- keyboard browsing
    def ensure_visible(self, card):
        w = card.parentWidget()
        while w is not None and not isinstance(w, QScrollArea):
            w = w.parentWidget()
        if isinstance(w, QScrollArea):
            w.ensureWidgetVisible(card, 0, 24)

    def select_neighbor(self, card, delta):
        cards = [c for c in self._nav_cards if c.isVisible()]
        if card not in cards:
            return
        main = self._main_cards()
        if delta > 0 and main and card is main[-1] and self._main_pending:
            self._queue_main_more(select=True)
            return
        if delta > 0:
            for state in self._section_batches:
                if state["cards"] and card is state["cards"][-1] and state["pending"]:
                    self._queue_section_more(state, select=True)
                    return
        i = cards.index(card) + delta
        if i < 0:
            self.quick.setFocus()          # up from the first note: back to the box
        elif i < len(cards):
            cards[i].select()

    def select_index(self, i):
        cards = [c for c in self._nav_cards if c.isVisible()]
        if i >= len(self._main_cards()) and self._main_pending:
            self._queue_main_more(select=True)
            return
        if cards:
            cards[max(0, min(i, len(cards) - 1))].select()
        else:
            self.quick.setFocus()

    def done_from_keyboard(self, card):
        cards = [c for c in self._nav_cards if c.isVisible()]
        self._pending_select = cards.index(card) if card in cards else 0
        self.set_done(card.task, not card.task["done"])

    def show_nav_hint(self, on):
        if on:
            self.copy_all_btn.hide()        # the key hint needs the room (Ctrl+Shift+C still copies the current set)
            self.status.setStyleSheet(f"color: {C['dim']};")
            self.status.setText("\u2191\u2193 browse \u00B7 Enter open \u00B7 Ctrl+Enter done \u00B7 "
                                "Tab more \u00B7 Alt+\u2191\u2193 move")
            self.status.setToolTip("Tab: Later / Let go / Delete, then Enter. Ctrl+C: copy. Delete key: delete. "
                                   "Esc while editing: back to browsing.")
        else:
            self.status.setStyleSheet("")
            self.update_counts()

    def check_nav_hint(self):
        fw = QApplication.focusWidget()
        card = fw
        while card is not None and not isinstance(card, TaskCard):
            card = card.parentWidget()
        browsing = isinstance(card, TaskCard) and (fw is card or fw in card.act_btns)
        if not browsing:
            self.show_nav_hint(False)

    def open_task(self, task):
        """Show the list on this note's tab with the note selected (the reminder's Open note)."""
        list_id = self.store.list_of(task)["id"]
        if list_id != self.store.settings["current"]:
            self.store.set_current(list_id)
        if self.isVisible():
            self.refresh_tabs()
            force_foreground(self)
        else:
            self.show_near_bubble()
        self.refresh_later(task["id"], select=True)

    def set_done(self, task, on, record=True):
        l = self.store.list_of(task)
        idx = l["tasks"].index(task) if task in l["tasks"] else 0
        before = (bool(task["done"]), task.get("done_at"))
        task["done"] = on
        task["done_at"] = datetime.now().isoformat(timespec="seconds") if on else None
        self.store.log_event("done" if on else "reopened", task)
        if on:  # done sinks to the bottom
            l["tasks"].remove(task)
            l["tasks"].append(task)
        self.store.save()
        self.remove_later(task, pause_ms=140, kind="done") if on else self.refresh_later()   # tick, then away
        if record:
            def undo():
                task["done"], task["done_at"] = before
                self.store.log_event("done" if before[0] else "reopened", task, undo=True)
                self._restore_position(task, l, idx)
                self.store.save()
                self.refresh_later(task["id"], select=True)
            self._push_undo("\u2713  " + pick_fresh(DONE_TOASTS, "done_toast") if on else "Back to open", undo)

    def set_urge(self, task, on):
        task["urge"] = on
        self.store.log_event("urge_on" if on else "urge_off", task)
        self.store.save()
        self.refresh_later()

    def update_counts(self):
        open_t = [t for t in self.store.tasks if not t["done"] and not t.get("later")]
        g = sum(1 for t in open_t if t.get("urgent"))
        u = sum(1 for t in open_t if t.get("urge"))
        d = sum(1 for t in open_t if t.get("distraction"))
        filtering = self.is_filtering()
        self.copy_all_btn.set_label("Copy search results" if filtering else "Copy all")
        self.copy_all_btn.setToolTip(("Copy the matching notes as a list (Ctrl+Shift+C)" if filtering else
                                     "Copy all open notes as a list, details under each (Ctrl+Shift+C)"))
        self.copy_all_btn.setVisible(bool(self.filtered_tasks()) if filtering else bool(open_t))
        self.status.setText(f"{len(open_t)} parked" + (f" \u00B7 {g} urgent" if g else "")
                            + (f" \u00B7 {u} itch{'es' if u != 1 else ''}" if u else "")
                            + (f" \u00B7 {d} distraction{'s' if d != 1 else ''}" if d else ""))

    def remove_attachment(self, task, att):
        self.store.remove_attachment(task, att)
        self.refresh_later(task["id"])

    # ---- show / hide
    def toggle(self):
        """Circle click, hotkey, gesture. Closed: open it. Open and in front: close it.
        Open but behind another app (or minimized by Show desktop): bring it back where you were."""
        if not self.isVisible():
            self.show_near_bubble()
            return
        # clicking the circle activates the circle first, so "in front" includes "was active a moment ago"
        in_front = self.isActiveWindow() or time.monotonic() - self._left_at < 0.6
        if self.isMinimized() or not in_front:
            self.bring_back()
        else:
            self.hide()

    def bring_back(self):
        if self.isMinimized():
            self.showNormal()
        self._remember_app()
        force_foreground(self)
        QTimer.singleShot(0, self.keep_clear_of_bubble)

    _left_at = 0.0
    _left_place = None

    def _place_now(self):
        """Which note you're on: ("select" | "edit", task id), or None (e.g. typing in the top box)."""
        fw = self.focusWidget()
        card = fw
        while card is not None and not isinstance(card, TaskCard):
            card = card.parentWidget()
        if not isinstance(card, TaskCard):
            return None
        return ("select" if fw is card or fw in card.act_btns else "edit", card.task["id"])

    def _restore_place(self):
        place, self._left_place = self._left_place, None
        if not place or not self.isVisible():
            return
        now = self._place_now()
        if now and now[1] == place[1]:
            return                      # Qt already put you back on it
        card = next((c for c in self._nav_cards if c.task["id"] == place[1] and c.isVisible()), None)
        if card:
            card.select()

    def changeEvent(self, e):
        if e.type() == QEvent.ActivationChange:
            if self.isActiveWindow():
                QTimer.singleShot(0, self._restore_place)
            elif self.isVisible():
                self._left_at = time.monotonic()
                self._left_place = self._place_now()
                QTimer.singleShot(120, self.focus_return.remember)   # Alt+Tab away: Esc later returns there
                if self.store.settings.get("close_on_outside", False):
                    QTimer.singleShot(150, self._close_if_outside)
        super().changeEvent(e)

    def _close_if_outside(self):
        """Setting "Close the list when I click elsewhere". Closes only when another app has taken over:
        not for our own dialogs or menus, not for the circle (its click decides), and not while a mouse
        button is held (you may be dragging a file onto the list); then it checks again shortly."""
        if not self.isVisible() or self.isActiveWindow() or not self.store.settings.get("close_on_outside", False):
            return
        if QApplication.activeWindow() is not None or QApplication.activePopupWidget() is not None:
            return                                  # one of our own windows took focus
        if mouse_button_down():
            QTimer.singleShot(200, self._close_if_outside)
            return
        self.hide()

    def show_near_bubble(self):
        screen = screen_for(self, self.bubble.geometry().center())
        area = screen.availableGeometry()
        w = min(self.width(), max(self.minimumWidth(), int(area.width() * 0.45)))
        h = min(self.height(), max(self.minimumHeight(), area.height() - 40))
        if (w, h) != (self.width(), self.height()):
            self.resize(w, h)              # a size saved on a big TV never opens past a small screen
        b = self.bubble.geometry()
        x = b.left() - self.width() - 8 if b.center().x() > area.center().x() else b.right() + 8
        y = b.center().y() - self.height() // 2
        x = max(area.left(), min(x, area.right() - self.width()))
        y = max(area.top() + 30, min(y, area.bottom() - self.height()))
        self.move(x, y)
        self.keep_clear_of_bubble()        # final spot first, so the slide ends exactly there
        self.refresh_tabs()
        if self._fingerprint() != self._built_fp:
            self.refresh()                 # rebuilding every card is the slow part; skip it when nothing changed
        else:
            self.update_counts()
            self.update_timer_row()
        self._start_open_anim()
        self._remember_app()
        force_foreground(self)
        self.quick.setFocus()

    def _remember_app(self):
        """The app to hand the keyboard back to when the list closes (hotkey/gesture: the one in front now;
        circle click: the one you were in when the mouse reached the circle)."""
        h = foreign_foreground()
        if not h:
            hov, at = getattr(self.bubble, "fg_at_hover", (None, 0))
            h = hov if time.monotonic() - at < 60 else None
        self.focus_return.remember(h)

    _built_fp = None
    def _fingerprint(self):
        """Everything the cards are built from. If it's unchanged, the cards on screen are still right."""
        st = self.store.settings
        return json.dumps([self.store.tasks, st.get("current"), st.get("flags_on"), st.get("open_section"),
                           st.get("flag_order"), st.get("custom_flags"),
                           st.get("sort"), self.find_edit.text(), self.filters], sort_keys=True, default=str)

    def _start_open_anim(self):
        """Show the list at full opacity immediately."""
        target = max(0.3, min(1.0, float(self.store.settings.get("opacity_list", 1.0))))
        self.setWindowOpacity(target)
        self.show()

    def showEvent(self, e):
        apply_share_privacy(self)
        self.important.update_times()
        super().showEvent(e)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        QTimer.singleShot(0, self._update_more)
        QTimer.singleShot(0, self._place_toast)
        if self.isVisible() and not self._resize:
            QTimer.singleShot(0, self.keep_clear_of_bubble)

    def _edges_at(self, pos):
        """Which card edges are under the mouse (left, right, bottom; the top is for moving)."""
        r, g = self.card_rect(), 8
        x, y = pos.x(), pos.y()
        left = abs(x - r.left()) <= g
        right = abs(x - r.right()) <= g
        bottom = abs(y - r.bottom()) <= g
        corner = x >= r.right() - 18 and y >= r.bottom() - 18   # the painted grip
        return left, right or corner, bottom or corner

    def _edge_cursor(self, left, right, bottom):
        if bottom and right:
            return Qt.SizeFDiagCursor
        if bottom and left:
            return Qt.SizeBDiagCursor
        if left or right:
            return Qt.SizeHorCursor
        if bottom:
            return Qt.SizeVerCursor
        return None

    def paintEvent(self, e):
        super().paintEvent(e)
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = self.card_rect()
        p.setPen(Qt.NoPen)
        p.setBrush(veil(48))
        for dx, dy in ((0, 0), (-5, 0), (0, -5), (-10, 0), (-5, -5), (0, -10)):   # resize grip dots
            p.drawEllipse(QPointF(r.right() - 7 + dx, r.bottom() - 7 + dy), 1.1, 1.1)

    def mousePressEvent(self, e):
        if e.button() == Qt.LeftButton:
            edges = self._edges_at(e.position().toPoint())
            if any(edges):
                left, right, bottom = edges
                qt_edges = [q for on, q in ((left, Qt.LeftEdge), (right, Qt.RightEdge), (bottom, Qt.BottomEdge)) if on]
                combo = qt_edges[0]
                for q in qt_edges[1:]:
                    combo = combo | q
                handle = self.windowHandle()
                if handle is not None and handle.startSystemResize(combo):   # native resize (Windows)
                    return
                self._resize = (edges, e.globalPosition().toPoint(), self.geometry())   # fallback: do it ourselves
                return
            self._drag = e.globalPosition().toPoint() - self.frameGeometry().topLeft()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if not (e.buttons() & Qt.LeftButton):
            # the button is up: never keep dragging or resizing (a release can land on another window,
            # and mouse tracking would otherwise make the list follow the cursor)
            self._drag = None
            self._resize = None
        if self._resize:
            (left, right, bottom), start, g0 = self._resize
            d = e.globalPosition().toPoint() - start
            g = QRect(g0)
            if right:
                g.setWidth(max(self.minimumWidth(), g0.width() + d.x()))
            if bottom:
                g.setHeight(max(self.minimumHeight(), g0.height() + d.y()))
            if left:
                w = max(self.minimumWidth(), g0.width() - d.x())
                g.setLeft(g0.right() - w + 1)
            self.setGeometry(g)
            return
        if self._drag is not None:
            self.move(e.globalPosition().toPoint() - self._drag)
        else:
            self._sync_edge_cursor(e.position().toPoint())
        super().mouseMoveEvent(e)

    def _sync_edge_cursor(self, pos=None):
        """Resize arrows only while the mouse is on an edge. The window never hears the mouse move onto a note
        (the note gets those events), so a short timer checks and puts the normal cursor back."""
        if pos is None:
            pos = self.mapFromGlobal(QCursor.pos())
        cur = self._edge_cursor(*self._edges_at(pos)) if self.rect().contains(pos) else None
        t = getattr(self, "_edge_timer", None)
        if cur is None:
            self.unsetCursor()
            if t:
                t.stop()
            return
        self.setCursor(cur)
        if t is None:
            t = self._edge_timer = QTimer(self)
            t.setInterval(80)
            t.timeout.connect(lambda: None if self._resize else self._sync_edge_cursor())
        t.start()

    def mouseReleaseEvent(self, e):
        self._drag = None
        self._resize = None
        super().mouseReleaseEvent(e)

    def keep_clear_of_bubble(self):
        """Nothing may cover the circle or run off screen, even when content changes the window size."""
        b = self.bubble.geometry()
        screen = QGuiApplication.screenAt(b.center()) or QGuiApplication.primaryScreen()
        area = screen.availableGeometry()
        fr = self.frameGeometry()
        x, y = fr.x(), fr.y()
        if b.center().x() > area.center().x():   # circle on the right: window stays to its left
            x = min(x, b.left() - 8 - fr.width())
        else:                                     # circle on the left: window stays to its right
            x = max(x, b.right() + 8)
        x = max(area.left(), min(x, area.right() - fr.width()))
        y = max(area.top(), min(y, area.bottom() - fr.height()))
        if (x, y) != (fr.x(), fr.y()):
            self.move(x, y)

    def closeEvent(self, e):
        e.ignore()
        self.hide()

    def hideEvent(self, e):
        self.focus_return.give_back()      # before the window goes, so Windows doesn't pick some other window
        self._drag = None
        self._resize = None
        self.store.settings["panel_size"] = [self.width(), self.height()]
        self.store.save()
        super().hideEvent(e)
        if len(self._main_cards()) > self.CARD_BATCH or any(s["loaded"] > self.CARD_BATCH
                                                            for s in self._section_batches):
            QTimer.singleShot(0, self._trim_hidden_cards)

    def _trim_hidden_cards(self):
        if (self.isVisible() or
                (len(self._main_cards()) <= self.CARD_BATCH and
                 all(s["loaded"] <= self.CARD_BATCH for s in self._section_batches))):
            return
        self.scroll.verticalScrollBar().setValue(0)
        self.refresh()


# ---------------------------------------------------------------- private quick note
class QuickBox(RoundedWindow):
    """One-line capture box. Shows no tasks, so it's safe during a meeting or screen share."""

    def __init__(self, panel):
        super().__init__(Qt.WindowStaysOnTopHint | Qt.Tool, accent_border=True)
        self.panel = panel
        self.focus_return = FocusReturn()
        self._warned = False
        self.setObjectName("roundwin")
        self.setStyleSheet(full_style())
        self.setFixedWidth(430 + 2 * self.SHADOW)
        lay = QVBoxLayout(self)
        m = self.SHADOW
        lay.setContentsMargins(12 + m, 12 + m - 2, 12 + m, 9 + m + 2)
        lay.setSpacing(6)
        self.edit = GrowText(max_lines=6)       # Enter parks, Shift+Enter starts a new line
        self.edit.setObjectName("quick")
        self.edit.grew.connect(lambda: self._regrow())
        self.edit.returnPressed.connect(self._save)
        self.edit.installEventFilter(self)
        self.edit.setAcceptDrops(False)  # drops go to the box: new task
        self.setAcceptDrops(True)
        self.hint = QLabel()
        self.hint.setObjectName("hint")
        self.hint.mousePressEvent = lambda e: self._grab_focus()
        close = QToolButton()
        close.setText("\u2715")
        close.setToolTip("Close (Esc)")
        close.setFocusPolicy(Qt.NoFocus)
        close.clicked.connect(self.hide)
        self.flags = {}
        # row 1: the note (whole width). row 2: flags. row 3: details (whole width, grows)
        body = QHBoxLayout()           # left: note, flags, details. right: close on top, Park at the bottom
        body.setSpacing(8)
        left = QVBoxLayout()
        left.setSpacing(6)
        left.addWidget(self.edit)
        right = QVBoxLayout()
        right.setSpacing(4)
        right.addWidget(close, 0, Qt.AlignRight | Qt.AlignTop)
        right.addStretch(1)
        body.addLayout(left, 1)
        body.addLayout(right)
        lay.addLayout(body)
        self._left, self._right = left, right
        self.details = GrowText(max_lines=6)
        self.details.setObjectName("qdetails")
        self.details.grew.connect(self._regrow)
        self.details.setPlaceholderText("Details (optional). Paste or drop a file to attach")
        self.details.returnPressed.connect(self._save)
        self.details.installEventFilter(self)
        self.details.setAcceptDrops(False)
        self.details.textChanged.connect(lambda: self.idle.start())
        self.row2 = QHBoxLayout()
        self.row2.setSpacing(4)
        frow = QHBoxLayout()
        frow.addLayout(self.row2, 1)
        left.addLayout(frow)
        self._flag_line = frow
        self.pending_reminder = None
        self.reminder_btn = reminder_chip(self, self._edit_reminder)
        self._flag_line.addWidget(self.reminder_btn)
        left.addWidget(self.details)
        self.details.hide()              # one box is enough for a stray thought (Shift+Enter for more lines)
        self.send_btn = SendButton(self, self._save, [self.edit, self.details])
        right.addWidget(self.send_btn, 0, Qt.AlignBottom)
        lay.addWidget(self.hint)
        self.build_flags()
        self.flag_number_guide = AltFlagGuide(self, lambda: self.flags, lambda: self.panel.store.settings)
        for number in range(1, 10):
            sc = QShortcut(QKeySequence(f"Alt+{number}"), self)
            sc.setContext(Qt.WidgetWithChildrenShortcut)
            sc.activated.connect(lambda n=number: toggle_numbered_flag(self.flags, self.panel.store.settings, n))
        QShortcut(QKeySequence("Escape"), self, self._escape)
        # safety: an empty, untouched box closes itself, so it never lingers if focus went elsewhere
        self.idle = QTimer(self)
        self.idle.setSingleShot(True)
        self.idle.setInterval(15000)
        self.idle.timeout.connect(lambda: self.hide() if not self.edit.text().strip() and
                                  not self.pending_reminder else None)
        self.edit.textChanged.connect(lambda *_: self.idle.start())

    def _escape(self):
        """Esc with something typed or tagged: wipe it for a fresh start. Esc on an empty box: close."""
        if (self.edit.text().strip() or self.details.text().strip() or self.pending_reminder
                or any(b.isChecked() for b in self.flags.values())):
            self.edit.clear()
            self.details.clear()
            self.pending_reminder = None
            self._refresh_reminder()
            for b in self.flags.values():
                b.setChecked(False)
            self.edit.setFocus()
            self._say("Cleared. Esc again to close")
            QTimer.singleShot(1800, lambda: self._say("") if self.hint.text().startswith("Cleared") else None)
        else:
            self.hide()

    def build_flags(self):
        """Flag buttons in your flag order (rebuilt when you add or reorder flags)."""
        if hasattr(self, "flag_number_guide"):
            self.flag_number_guide.clear()
        while self.row2.count():
            w = self.row2.takeAt(0).widget()
            if w:
                w.hide()
                w.deleteLater()
        self.flags = {}
        visible_keys = [k for k in FLAG_KEYS if flag_on(self.panel.store.settings, k)]
        for key, icon, _word, tip in FLAG_DEFS:
            b = QToolButton(self)
            b.setObjectName("flag")
            b.setProperty("kind", key)
            b.setText(icon)
            number = visible_keys.index(key) + 1 if key in visible_keys else 0
            b.setToolTip(f"{icon} {_word}" + (f" (Alt+{number})" if 1 <= number <= 9 else ""))
            b.setProperty("flaghint", tip.split(". ")[0])
            b.setProperty("flagword", _word)
            b.setCheckable(True)
            b.setFocusPolicy(Qt.StrongFocus)
            b.installEventFilter(self)
            self.row2.addWidget(b)
            self.flags[key] = b
        self.row2.addStretch(1)
        chain = [self.edit] + [self.flags[k] for k in FLAG_KEYS] + [self.reminder_btn, self.details, self.send_btn]
        for a, b2 in zip(chain, chain[1:]):
            QWidget.setTabOrder(a, b2)
        self.setStyleSheet(full_style())

    def popup(self):
        # never show the list next to the private box; it comes back when the quick note closes
        self._reopen_list = self.panel.isVisible() and not self.panel.isMinimized()
        self._our_window = next((w for w in QApplication.topLevelWidgets() if w.isVisible() and w is not self.panel
                                 and w.windowType() == Qt.Window and w.isActiveWindow()), None)
        self.panel.hide()
        self.focus_return.remember()
        self.edit.clear()
        self.details.clear()
        self.pending_reminder = None
        self._refresh_reminder()
        for k, b in self.flags.items():
            b.setChecked(False)
            b.setVisible(flag_on(self.panel.store.settings, k))
        self.edit.setPlaceholderText("Quick note (Shift+Enter for a new line)")
        self._say("")
        self.adjustSize()
        pos = QCursor.pos()
        area = screen_for(self, pos).availableGeometry()
        x = max(area.left(), min(pos.x() - self.width() // 2, area.right() - self.width()))
        y = max(area.top(), min(pos.y() + 20, area.bottom() - self.height()))
        self.move(x, y)
        self._warned = False
        self.hint.setStyleSheet("")
        self._grab_focus()
        self.idle.start()
        QTimer.singleShot(250, self._check_focus)

    def _grab_focus(self):
        force_foreground(self)
        self.edit.setFocus()

    def _regrow(self):
        """Details grew or shrank: resize the box and keep it on screen."""
        if not self.isVisible():
            return
        self.adjustSize()
        area = (QGuiApplication.screenAt(self.geometry().center()) or QGuiApplication.primaryScreen()).availableGeometry()
        if self.geometry().bottom() > area.bottom():
            self.move(self.x(), max(area.top(), area.bottom() - self.height()))

    def _say(self, text, style=""):
        """The status line is hidden unless there's something to say (parked, drop, focus warning)."""
        self.hint.setStyleSheet(style)
        self.hint.setText(text)
        self.hint.setVisible(bool(text))
        self.adjustSize()

    def _check_focus(self):
        """If Windows refused focus, say so loudly instead of letting keys go to another app."""
        if self.isVisible() and not self.isActiveWindow():
            self._grab_focus()
            QTimer.singleShot(150, self._warn_if_unfocused)

    def _warn_if_unfocused(self):
        if self.isVisible() and not self.isActiveWindow():
            self._warned = True
            self._say("Click here to type (Windows kept focus in the other app)", f"color: {C['idea']}; font-weight: bold;")

    def changeEvent(self, e):
        if e.type() == QEvent.ActivationChange:
            if self.isActiveWindow():
                if self._warned:
                    self._warned = False
                    self._say("")
                self.edit.setFocus()
        super().changeEvent(e)

    def toggle(self):
        self.hide() if self.isVisible() else self.popup()

    def showEvent(self, e):
        apply_share_privacy(self)
        super().showEvent(e)

    def hideEvent(self, e):
        """Parked, Esc or closed: back to where you were. That's the full list if it was open, or one of our own
        windows (Settings, History) if you were in it, otherwise the app you were typing in."""
        reopen, ours = getattr(self, "_reopen_list", False), getattr(self, "_our_window", None)
        self._reopen_list, self._our_window = False, None
        if reopen:
            QTimer.singleShot(0, self.panel.show_near_bubble)
        elif ours is not None and ours.isVisible():
            QTimer.singleShot(0, lambda: (ours.raise_(), force_foreground(ours)))
        else:
            self.focus_return.give_back()
        super().hideEvent(e)

    def _done(self, reminder=None):
        self._say(reminder_confirmation(reminder) if reminder else "Parked \u2713")
        self.panel.refresh_later()
        delay = 1500 if reminder else 500
        QTimer.singleShot(delay, self.hide)
        if reminder:
            message = reminder_confirmation(reminder)
            QTimer.singleShot(delay + 20, lambda: self.panel.bubble.pop_word(message, 3800))
        elif self.panel.store.settings.get("saved_pop", True):
            QTimer.singleShot(520, lambda: self.panel.bubble.pop_word(pick_fresh(SAVED_WORDS, "saved")))

    def dragEnterEvent(self, e):
        md = e.mimeData()
        if isinstance(e.source(), AttachmentTile):
            e.ignore()                     # a file on its way out of the shelf, not a new drop
            return
        if md.hasUrls() or md.hasImage() or md.hasText():
            e.acceptProposedAction()
            self.idle.start()
            self._say("Drop to park it")

    def dropEvent(self, e):
        t = self.panel.task_from_mime(e.mimeData(), self.edit.text().strip(), source="private_note_drop",
                                      flags={k: b.isChecked() for k, b in self.flags.items()})
        if t:
            extra = self.details.text().strip()   # keep what was typed in details too
            if extra:
                t["desc"] = (t["desc"] + "\n" if t.get("desc") else "") + extra
                self.panel.store.save()
            if self.pending_reminder:
                t["reminder"] = self.pending_reminder.copy()
                self.panel.store.save()
            e.acceptProposedAction()
            self.edit.clear()
            self.details.clear()
            self.pending_reminder = None
            self._refresh_reminder()
            self._done(t.get("reminder"))
        else:
            self._say("")

    def dragLeaveEvent(self, e):
        self._say("")
        super().dragLeaveEvent(e)

    def _apply_extras(self, t):
        """Flags and details from the box onto a new task (before it's logged)."""
        for k, b in self.flags.items():
            t[k] = b.isChecked()
        extra = self.details.text().strip()
        if extra:
            t["desc"] = (t["desc"] + "\n" if t["desc"] else "") + extra
        if self.pending_reminder:
            t["reminder"] = self.pending_reminder.copy()

    def _edit_reminder(self):
        changed, value = edit_reminder(self, self.pending_reminder, self.reminder_btn)
        if changed:
            self.pending_reminder = value
            self._refresh_reminder()

    def _refresh_reminder(self):
        show_reminder_chip(self.reminder_btn, self.pending_reminder)

    def _save(self):
        text = self.edit.text().strip()
        extra = self.details.text().strip()
        if text or extra:
            text, inline_reminder = extract_inline_reminder(text)
            extra, extra_reminder = extract_inline_reminder(extra)
            inline_reminder = extra_reminder or inline_reminder
            if not text and not extra:
                return
            t = self.panel.store.new_task(text or extra.splitlines()[0][:80], source="private_note", log=False)
            if text:
                self._apply_extras(t)
                if extra != self.details.text().strip():
                    t["desc"] = extra
            else:
                for k, b in self.flags.items():
                    t[k] = b.isChecked()
            if self.pending_reminder or inline_reminder:
                t["reminder"] = (self.pending_reminder or inline_reminder).copy()
            self.panel.store.log_captured(t)
            self.panel.store.save()
            self.edit.clear()
            self.details.clear()
            self.pending_reminder = None
            self._refresh_reminder()
            self._done(t.get("reminder"))

    def eventFilter(self, obj, e):
        if (e.type() == QEvent.KeyPress and obj in [self.edit, self.details, *self.flags.values()]
                and e.modifiers() == Qt.AltModifier and Qt.Key_1 <= e.key() <= Qt.Key_9):
            toggle_numbered_flag(self.flags, self.panel.store.settings, int(e.key()) - int(Qt.Key_0))
            return True
        if obj in getattr(self, "flags", {}).values():
            flag_focus_hint(obj, e)
        if (e.type() == QEvent.KeyPress and obj in self.flags.values()
                and e.key() in (Qt.Key_Return, Qt.Key_Enter)):
            if not (e.modifiers() & Qt.ControlModifier):
                obj.setChecked(True)      # same rule as the list: Enter on a flag = this one too, then park
            self._save()
            return True
        if e.type() == QEvent.KeyPress and e.matches(QKeySequence.Paste) and obj in (self.edit, self.details):
            md = QGuiApplication.clipboard().mimeData()
            if md.hasUrls() or (md.hasImage() and not md.hasText()):
                title = self.edit.text().strip() or f"Snip {datetime.now():%H:%M}"
                t = self.panel.store.new_task(title, source="private_note_paste", log=False)
                if self.panel.attach_mime(t, md):
                    self._apply_extras(t)
                    self.panel.store.log_captured(t)
                    self.panel.store.save()
                    self.details.clear()
                    self.edit.clear()
                    self.pending_reminder = None
                    self._refresh_reminder()
                    self._done(t.get("reminder"))
                else:
                    self.panel.store.discard_new(t)
                return True
        return super().eventFilter(obj, e)


# ---------------------------------------------------------------- phone alert (ntfy)
# ---------------------------------------------------------------- settings window
class ToggleSwitch(QAbstractButton):
    """A painted on/off switch with a sliding knob."""

    def __init__(self, on=False, parent=None):
        super().__init__(parent)
        self.setCheckable(True)
        self.setChecked(bool(on))
        self.setCursor(Qt.PointingHandCursor)
        self.setFixedSize(40, 22)
        self._k = 1.0 if on else 0.0
        self._anim = QVariantAnimation(self)
        self._anim.setDuration(140)
        self._anim.setEasingCurve(QEasingCurve.OutCubic)
        self._anim.valueChanged.connect(self._set_k)
        self.toggled.connect(self._slide)

    def _set_k(self, v):
        self._k = float(v)
        self.update()

    def _slide(self, on):
        self._anim.stop()
        self._anim.setStartValue(self._k)
        self._anim.setEndValue(1.0 if on else 0.0)
        self._anim.start()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        off, on = QColor(C["border"] if theme_dark() else C["faint"]), QColor(C["accent"])
        k = self._k
        track = QColor(int(off.red() + (on.red() - off.red()) * k), int(off.green() + (on.green() - off.green()) * k),
                       int(off.blue() + (on.blue() - off.blue()) * k))
        if not self.isEnabled():
            track.setAlpha(90)
        p.setPen(Qt.NoPen)
        p.setBrush(track)
        p.drawRoundedRect(QRectF(1, 2, 38, 18), 9, 9)
        p.setBrush(QColor("#f4f4f4") if self.isEnabled() else QColor("#8a8a8a"))
        p.drawEllipse(QRectF(4 + 18 * k, 5, 12, 12))
        if self.hasFocus():
            p.setPen(QPen(QColor(C["text"]), 1))
            p.setBrush(Qt.NoBrush)
            p.drawRoundedRect(QRectF(0.5, 1.5, 39, 19), 9.5, 9.5)


class Segmented(QWidget):
    """A row of joined buttons, one picked (like iOS segmented controls)."""
    changed = Signal(object)

    def __init__(self, options, current, parent=None):
        super().__init__(parent)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self.btns = {}
        for i, (key, label) in enumerate(options):
            b = QPushButton(label, self)
            b.setObjectName("seg")
            b.setCheckable(True)
            b.setCursor(Qt.PointingHandCursor)
            b.setProperty("pos", "first" if i == 0 else "last" if i == len(options) - 1 else "mid")
            b.setChecked(key == current)
            b.clicked.connect(lambda _=False, k=key: self.set_value(k, emit=True))
            lay.addWidget(b)
            self.btns[key] = b
        self.value = current

    def set_value(self, key, emit=False):
        self.value = key
        for k, b in self.btns.items():
            b.setChecked(k == key)
        if emit:
            self.changed.emit(key)


class Swatch(QAbstractButton):
    """A round colour chip; a ring shows the chosen one."""

    def __init__(self, color, tip, parent=None, half=None):
        super().__init__(parent)
        self.color = QColor(color)
        self.half = QColor(half) if half else None
        self.setCheckable(True)
        self.setToolTip(tip)
        self.setCursor(Qt.PointingHandCursor)
        self.setFixedSize(30, 30)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        if self.isChecked():
            p.setPen(QPen(QColor(C["text"]), 2))
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(QRectF(1.5, 1.5, 27, 27))
        p.setPen(QPen(QColor(0, 0, 0, 60), 1))
        p.setBrush(self.color)
        p.drawEllipse(QRectF(5, 5, 20, 20))
        if self.half is not None:      # two-colour chip: right half in the second colour
            p.setBrush(self.half)
            p.drawPie(QRectF(5, 5, 20, 20), -90 * 16, 180 * 16)


class PreviewTile(QAbstractButton):
    """A picture with a caption under it; a border shows the chosen one."""

    def __init__(self, pixmap, caption, parent=None, size=(84, 84)):
        super().__init__(parent)
        self.pix, self.caption = pixmap, caption
        self.setCheckable(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setFixedSize(*size)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)
        r = QRectF(self.rect()).adjusted(1, 1, -1, -1)
        p.setPen(QPen(QColor(C["accent"] if self.isChecked() else C["border"]), 2 if self.isChecked() else 1))
        p.setBrush(QColor(C["surface_hi"] if self.underMouse() else C["field"]))
        p.drawRoundedRect(r, 10, 10)
        if self.pix is not None and not self.pix.isNull():
            s = min(self.width() - 20, self.height() - 34)
            pm = self.pix.scaled(s, s, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            p.drawPixmap(int((self.width() - pm.width()) / 2), 8 + int((s - pm.height()) / 2), pm)
        p.setPen(QColor(C["text"] if self.isChecked() else C["dim"]))
        f = QFont(self.font())
        f.setPixelSize(11)
        p.setFont(f)
        p.drawText(QRectF(2, self.height() - 24, self.width() - 4, 20), Qt.AlignCenter, self.caption)


class ChoiceCard(QAbstractButton):
    """A small card with a title and one line under it (sound kinds, countdown styles)."""

    def __init__(self, title, desc, parent=None):
        super().__init__(parent)
        self.title, self.desc = title, desc
        self.setCheckable(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setToolTip(desc)
        self.setMinimumHeight(52)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

    def sizeHint(self):
        return QSize(150, 52)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = QRectF(self.rect()).adjusted(1, 1, -1, -1)
        p.setPen(QPen(QColor(C["accent"] if self.isChecked() else C["border"]), 2 if self.isChecked() else 1))
        p.setBrush(QColor(C["accent_soft"] if self.isChecked() else (C["surface_hi"] if self.underMouse() else C["field"])))
        p.drawRoundedRect(r, 9, 9)
        f = QFont(self.font())
        f.setPixelSize(12)
        f.setBold(True)
        p.setFont(f)
        p.setPen(QColor(C["text"]))
        p.drawText(QRectF(12, 7, r.width() - 16, 18), Qt.AlignLeft | Qt.AlignVCenter, self.title)
        f.setBold(False)
        f.setPixelSize(10)
        p.setFont(f)
        p.setPen(QColor(C["dim"]))
        fm = QFontMetrics(f)
        p.drawText(QRectF(12, 26, r.width() - 16, 18), Qt.AlignLeft | Qt.AlignVCenter,
                   fm.elidedText(self.desc, Qt.ElideRight, int(r.width() - 18)))


def bubble_preview(bubble, color=None, shape=None):
    """A picture of the circle with another colour or shape (the real circle is repainted right after)."""
    keep = (bubble.color_key, bubble.shape, bubble.show_count)
    try:
        if color:
            bubble.color_key = color
        if shape:
            bubble.shape = shape
        return bubble.grab()
    finally:
        bubble.color_key, bubble.shape, bubble.show_count = keep
        bubble.update()


def make_settings_style():
    return f"""
QWidget#settingsRoot {{ background: {C['bg']}; }}
QListWidget#side {{ background: {C['surface']}; border: none; border-right: 1px solid {C['border']};
    color: {C['dim']}; font-size: 13px; outline: none; padding: 10px 6px; }}
QListWidget#side::item {{ padding: 9px 10px; border-radius: 8px; margin: 1px 0; }}
QListWidget#side::item:selected {{ background: {C['accent_soft']}; color: {C['text']}; }}
QListWidget#side::item:hover:!selected {{ background: {C['surface_hi']}; color: {C['text']}; }}
QScrollArea#page {{ background: {C['bg']}; border: none; }}
QWidget#pageBody {{ background: {C['bg']}; }}
QLabel#pageTitle {{ color: {C['text']}; font-size: 18px; font-weight: 700; }}
QLabel#pageSub {{ color: {C['faint']}; font-size: 11px; }}
QLabel#section {{ color: {C['dim']}; font-size: 11px; font-weight: 700; letter-spacing: 1px; padding-top: 10px; }}
QFrame#group {{ background: {C['surface']}; border: 1px solid {C['border']}; border-radius: 10px; }}
QLabel#rowTitle {{ color: {C['text']}; font-size: 12px; }}
QLabel#rowDesc {{ color: {C['faint']}; font-size: 11px; }}
QToolButton#fold {{ color: {C['dim']}; font-size: 11px; font-weight: 700; text-align: left; border: none;
    background: transparent; padding: 10px 0 2px 0; }}
QToolButton#fold:hover, QToolButton#fold:focus {{ color: {C['text']}; }}
QLabel#value {{ color: {C['dim']}; font-size: 11px; min-width: 38px; }}
QKeySequenceEdit, QLineEdit {{ background: {C['field']}; color: {C['text']}; border: 1px solid {C['border']};
    border-radius: 6px; padding: 3px 6px; }}
QPushButton#seg {{ background: {C['field']}; color: {C['dim']}; border: 1px solid {C['border']}; border-radius: 0;
    padding: 4px 11px; font-size: 11px; }}
QPushButton#seg[pos="first"] {{ border-top-left-radius: 7px; border-bottom-left-radius: 7px; }}
QPushButton#seg[pos="last"] {{ border-top-right-radius: 7px; border-bottom-right-radius: 7px; }}
QPushButton#seg:checked {{ background: {C['accent']}; color: white; border-color: {C['accent']}; }}
QPushButton#seg:hover:!checked {{ background: {C['surface_hi']}; color: {C['text']}; }}
QPushButton#act {{ background: {C['surface_hi']}; color: {C['text']}; border: 1px solid {C['border']}; border-radius: 7px;
    padding: 5px 12px; font-size: 11px; }}
QPushButton#act:hover {{ border-color: {C['accent']}; }}
QPushButton#act:disabled {{ color: {C['border']}; border-color: {C['surface_hi']}; }}
QSlider::groove:horizontal {{ height: 4px; background: {C['border']}; border-radius: 2px; }}
QSlider::sub-page:horizontal {{ background: {C['accent']}; border-radius: 2px; }}
QSlider::handle:horizontal {{ background: #f4f4f4; border: 1px solid {C['border']}; width: 14px; height: 14px; margin: -5px 0; border-radius: 7px; }}
QSlider::handle:horizontal:hover {{ background: white; }}
"""


SETTINGS_STYLE = make_settings_style()


class NoWheelSlider(QSlider):
    """Only a click or a drag moves it: the mouse wheel scrolls the page, so a scroll never changes a setting."""

    def __init__(self, *a):
        super().__init__(*a)
        self.setFocusPolicy(Qt.StrongFocus)

    def wheelEvent(self, e):
        e.ignore()


class GestureOverlay(QWidget):
    """A see-through layer over the circle's screen that shows what a setting means while you drag its slider:
    the "near the circle" zone as a glowing circle, or how big a scribble has to be as a traced zigzag. Clicks
    pass through, and it fades away a moment after you let go."""

    def __init__(self):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool
                         | Qt.WindowTransparentForInput)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.mode, self.value, self.center = "zone", 320, QPoint()
        self.t0 = time.monotonic()
        self.alpha = 0.0
        self.tick = QTimer(self)
        self.tick.setInterval(16)
        self.tick.timeout.connect(self._step)
        self.hide_at = 0.0

    def show_zone(self, bubble, radius):
        self._show(bubble, "zone", radius, bubble.geometry().center())

    def show_scribble(self, bubble, level, near):
        screen = QGuiApplication.screenAt(bubble.geometry().center()) or QGuiApplication.primaryScreen()
        if near:                          # beside the circle, toward the middle of the screen, not on top of it
            bc, sc = bubble.geometry().center(), screen.availableGeometry().center()
            c = bc + QPoint(-110 if bc.x() > sc.x() else 110, 0)
        else:
            c = screen.availableGeometry().center()
        self._show(bubble, "scribble", level, c)

    def _show(self, bubble, mode, value, center):
        screen = screen_for(self, bubble.geometry().center())
        if self.geometry() != screen.geometry():
            self.setGeometry(screen.geometry())
        self.mode, self.value, self.center = mode, value, self.mapFromGlobal(center)
        self.hide_at = time.monotonic() + 1.6
        if not self.isVisible():
            self.t0 = time.monotonic()
            self.show()
            apply_share_privacy(self)
        self.tick.start()
        self.update()

    def _step(self):
        now = time.monotonic()
        target = 1.0 if now < self.hide_at else 0.0
        self.alpha += (target - self.alpha) * 0.18
        if target == 0.0 and self.alpha < 0.02:
            self.alpha = 0.0
            self.tick.stop()
            self.hide()
            return
        self.update()

    def _pill(self, p, text, at):
        f = QFont(self.font())
        f.setPixelSize(13)
        f.setBold(True)
        p.setFont(f)
        fm = QFontMetrics(f)
        w, h = fm.horizontalAdvance(text) + 28, 30
        r = QRectF(at.x() - w / 2, at.y() - h / 2, w, h)
        r.moveLeft(max(8, min(r.left(), self.width() - w - 8)))
        r.moveTop(max(8, min(r.top(), self.height() - h - 8)))
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(20, 21, 24, int(230 * self.alpha)))
        p.drawRoundedRect(r, h / 2, h / 2)
        p.setPen(QColor(255, 255, 255, int(255 * self.alpha)))
        p.drawText(r, Qt.AlignCenter, text)

    def paintEvent(self, e):
        if self.alpha <= 0:
            return
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        a = self.alpha
        t = time.monotonic() - self.t0
        accent = QColor(C["accent"])
        if self.mode == "zone":
            r = float(self.value)
            c = QPointF(self.center)
            veil = QPainterPath()
            veil.addRect(QRectF(self.rect()))
            hole = QPainterPath()
            hole.addEllipse(c, r, r)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(8, 8, 12, int(110 * a)))       # dim everything outside the zone
            p.drawPath(veil.subtracted(hole))
            g = QRadialGradient(c, r)
            g.setColorAt(0.0, QColor(accent.red(), accent.green(), accent.blue(), int(10 * a)))
            g.setColorAt(0.82, QColor(accent.red(), accent.green(), accent.blue(), int(38 * a)))
            g.setColorAt(1.0, QColor(accent.red(), accent.green(), accent.blue(), int(90 * a)))
            p.setBrush(g)
            p.drawEllipse(c, r, r)
            pen = QPen(QColor(255, 255, 255, int(200 * a)), 2, Qt.DashLine)
            pen.setDashOffset(-t * 12)                        # the edge slowly runs around
            p.setPen(pen)
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(c, r, r)
            self._pill(p, f"Scribbles count inside this circle  \u00B7  {int(r)} px", QPointF(c.x(), c.y() - r - 26))
        else:
            revs, seg = SCRIBBLE_LEVELS[int(self.value)]
            seg_draw = max(seg * 2.2, 40)                    # drawn a little bigger than the minimum, to read it
            c = QPointF(self.center)
            path = QPainterPath()
            n = revs + 1
            x0 = c.x() - (n - 1) * 9
            path.moveTo(x0, c.y() + seg_draw / 2)
            for i in range(1, n):
                path.lineTo(x0 + i * 18, c.y() + (seg_draw / 2 if i % 2 == 0 else -seg_draw / 2))
            glow = QPen(QColor(accent.red(), accent.green(), accent.blue(), int(90 * a)), 12, Qt.SolidLine,
                        Qt.RoundCap, Qt.RoundJoin)
            p.setPen(glow)
            p.drawPath(path)
            p.setPen(QPen(QColor(255, 255, 255, int(230 * a)), 3, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
            p.drawPath(path)
            k = (t * 0.9) % 1.0                              # a dot tracing the scribble
            dot = path.pointAtPercent(k)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255, int(255 * a)))
            p.drawEllipse(dot, 6, 6)
            self._pill(p, f"{SCRIBBLE_LEVEL_NAMES[int(self.value)]}: {revs} turns within a second, "
                          f"{seg} px or more each", QPointF(c.x(), c.y() + seg_draw / 2 + 34))


class HotkeyEdit(QKeySequenceEdit):
    """A hotkey box that turns the global hotkeys off while you type in it (so the old combo doesn't fire)."""

    def __init__(self, seq, on_focus, on_blur, parent=None):
        super().__init__(QKeySequence(seq), parent)
        self._on_focus, self._on_blur = on_focus, on_blur
        if hasattr(self, "setMaximumSequenceLength"):
            self.setMaximumSequenceLength(1)

    def focusInEvent(self, e):
        self._on_focus()
        super().focusInEvent(e)

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        self._on_blur()


GOOGLE_CALENDAR_SCOPE = "https://www.googleapis.com/auth/calendar.readonly"


def calendar_token_blob(value, encrypt=True):
    """Protect a refresh token for this Windows user before saving it in the synced settings file."""
    if not IS_WIN:
        raise RuntimeError("Google Calendar connection needs Windows.")
    import ctypes
    from ctypes import wintypes

    class Blob(ctypes.Structure):
        _fields_ = [("size", wintypes.DWORD), ("data", ctypes.POINTER(ctypes.c_byte))]

    raw = value.encode() if encrypt else base64.b64decode(value, validate=True)
    source = ctypes.create_string_buffer(raw)
    input_blob = Blob(len(raw), ctypes.cast(source, ctypes.POINTER(ctypes.c_byte)))
    output_blob = Blob()
    crypt = ctypes.windll.crypt32
    name = "CryptProtectData" if encrypt else "CryptUnprotectData"
    operation = getattr(crypt, name)
    operation.argtypes = [ctypes.POINTER(Blob), ctypes.c_void_p, ctypes.c_void_p,
                          ctypes.c_void_p, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(Blob)]
    operation.restype = wintypes.BOOL
    if not operation(ctypes.byref(input_blob), None, None, None, None, 0, ctypes.byref(output_blob)):
        raise RuntimeError("Windows could not open the calendar connection. Please reconnect.")
    try:
        result = ctypes.string_at(output_blob.data, output_blob.size)
        return base64.b64encode(result).decode() if encrypt else result.decode()
    finally:
        ctypes.windll.kernel32.LocalFree.argtypes = [ctypes.c_void_p]
        ctypes.windll.kernel32.LocalFree(output_blob.data)


def calendar_json(url, token=None, form=None):
    headers = {"Accept": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    if form is not None:
        headers["Content-Type"] = "application/x-www-form-urlencoded"
    request = urllib.request.Request(url, data=urllib.parse.urlencode(form).encode() if form is not None else None,
                                     headers=headers)
    try:
        with urllib.request.urlopen(request, timeout=12) as response:
            return json.load(response)
    except urllib.error.HTTPError as exc:
        if exc.code == 400 and form and form.get("grant_type") == "refresh_token":
            raise RuntimeError("Calendar connection expired. Reconnect in Settings.") from None
        if exc.code == 401:
            raise RuntimeError("Calendar access expired. Reconnect in Settings.") from None
        if exc.code == 403:
            raise RuntimeError("Calendar access was refused. Check that the Calendar API is enabled.") from None
        raise RuntimeError(f"Google Calendar returned error {exc.code}.") from None


def calendar_pages(path, token, params):
    items, page = [], None
    while True:
        query = dict(params)
        if page:
            query["pageToken"] = page
        url = "https://www.googleapis.com/calendar/v3" + path + "?" + urllib.parse.urlencode(query)
        data = calendar_json(url, token=token)
        items.extend(data.get("items", []))
        page = data.get("nextPageToken")
        if not page:
            return items


def event_details_text(text, limit=280):
    """An event's notes as short plain text: Google sends some as HTML."""
    text = html.unescape(re.sub(r"<br\s*/?>|</p>", "\n", str(text or ""), flags=re.I))
    text = re.sub(r"<[^>]+>", "", text)
    text = "\n".join(line.strip() for line in text.splitlines() if line.strip())
    return text if len(text) <= limit else text[:limit].rstrip() + "..."


MEET_NOW_URL = "https://meet.google.com/new"  # Google starts a fresh call in the default browser


def new_event_url(start, minutes=30):
    """Google Calendar's own new-event page, filled with a time. Nothing personal goes in the link."""
    fmt = "%Y%m%dT%H%M%SZ"
    end = start + timedelta(minutes=minutes)
    return ("https://calendar.google.com/calendar/render?action=TEMPLATE&dates="
            f"{start.astimezone(timezone.utc).strftime(fmt)}/{end.astimezone(timezone.utc).strftime(fmt)}")


def ink_for(color):
    """Dark or light text, whichever has more contrast on this fill (WCAG relative luminance)."""
    def lum(c):
        ch = [v / 255 for v in (c.red(), c.green(), c.blue())]
        ch = [v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4 for v in ch]
        return 0.2126 * ch[0] + 0.7152 * ch[1] + 0.0722 * ch[2]
    fill, dark, light = lum(QColor(color)), QColor("#1b1f24"), QColor(DARK["text"])
    return dark if (fill + 0.05) / (lum(dark) + 0.05) >= (lum(light) + 0.05) / (fill + 0.05) else light


def calendar_events(rows, now, past_days=0):
    """Pick timed, busy, non-declined events. Expanded recurring instances arrive from Google."""
    events = []
    for row in rows:
        if row.get("status") == "cancelled" or row.get("transparency") == "transparent":
            continue
        if any(a.get("self") and a.get("responseStatus") == "declined" for a in row.get("attendees", [])):
            continue
        try:
            start = datetime.fromisoformat(row["start"]["dateTime"].replace("Z", "+00:00")).astimezone()
            end = datetime.fromisoformat(row["end"]["dateTime"].replace("Z", "+00:00")).astimezone()
        except (KeyError, TypeError, ValueError):
            continue  # all-day event or invalid date
        if end <= now - timedelta(days=past_days) or end <= start or end - start >= timedelta(hours=24):
            continue
        entry_points = row.get("conferenceData", {}).get("entryPoints", [])
        join = row.get("hangoutLink") or next((p.get("uri") for p in entry_points
                                              if p.get("entryPointType") == "video"), "")
        url = join or row.get("htmlLink") or ""
        uid = row.get("iCalUID")
        event_id = row.get("recurringEventId") or row.get("id")
        identity = str(uid) if uid else (f"{row.get('_calendar_id') or ''}:{event_id}" if event_id else "")
        events.append({"title": str(row.get("summary") or "Busy"), "start": start, "end": end,
                       "url": url if isinstance(url, str) and url.startswith("https://") else "",
                       "join": bool(join), "calendar_id": row.get("_calendar_id", ""),
                       "calendar_name": row.get("_calendar_name", ""),
                       "page": row.get("htmlLink") if str(row.get("htmlLink", "")).startswith("https://") else "",
                       "location": str(row.get("location") or ""),
                       "details": event_details_text(row.get("description")),
                       "calendar_color": calendar_color(row.get("_calendar_color")),
                       "event_color": calendar_color(row.get("_event_color"),
                                                     calendar_color(row.get("_calendar_color"))),
                       "series_key": calendar_series_key(identity) if identity else ""})
    return sorted(events, key=lambda e: (e["start"], e["end"]))


def _ics_lines(content):
    """Unfold RFC 5545 content lines; the feed is never written to disk."""
    lines = []
    for line in content.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        if line.startswith((" ", "\t")) and lines:
            lines[-1] += line[1:]
        else:
            lines.append(line)
    return lines


CALENDAR_COLORS = ("#7b8fe8", "#4eaa90", "#e3a458", "#c17cc8", "#dd7891", "#74a9cf")


def calendar_color(value, fallback=CALENDAR_COLORS[0]):
    """Accept only an opaque hex color before it is used in a stylesheet."""
    return value if isinstance(value, str) and re.fullmatch(r"#[0-9a-fA-F]{6}", value) else fallback


def calendar_ics_color(value):
    """Normalize an iCal CSS color to safe hex when the feed actually contains one."""
    color = QColor(value) if isinstance(value, str) else QColor()
    return color.name() if color.isValid() else ""


def google_event_color(row, palette, labels, fallback):
    """Use the event's Google label or legacy color before its calendar color."""
    label_id = str(row.get("eventLabelId") or "")
    if label_id:
        return calendar_color(labels.get(label_id), fallback)
    color_id = str(row.get("colorId") or "")
    legacy = palette.get(color_id, {}) if isinstance(palette, dict) else {}
    return calendar_color(legacy.get("background") if isinstance(legacy, dict) else None, fallback)


def calendar_series_key(identity):
    """Save only an opaque key when the user hides a Google event series."""
    return hashlib.sha256(str(identity).encode("utf-8", errors="replace")).hexdigest()


def calendar_ics_metadata(content):
    """Calendar-level labels are optional in private iCal feeds."""
    header = []
    for line in _ics_lines(content):
        if line == "BEGIN:VEVENT":
            break
        header.append(line)
    values = {}
    for line in header:
        if ":" in line:
            key, value = line.split(":", 1)
            values[key.upper()] = value
    name = _ics_text(values.get("X-WR-CALNAME", "")).strip()
    color = values.get("X-WR-CALCOLOR") or values.get("COLOR")
    return name[:80], calendar_ics_color(color)


def _ics_properties(lines):
    events, current = [], None
    for line in lines:
        if line == "BEGIN:VEVENT":
            current = {}
        elif line == "END:VEVENT" and current is not None:
            events.append(current)
            current = None
        elif current is not None and ":" in line:
            key, value = line.split(":", 1)
            parts = key.split(";")
            name = parts[0].upper()
            params = dict(p.split("=", 1) for p in parts[1:] if "=" in p)
            current.setdefault(name, []).append((value, params))
    return events


def _ics_value(event, name):
    values = event.get(name, [])
    return values[0] if values else ("", {})


def _ics_datetime(value, params=None):
    """Convert Google iCal UTC, offset and TZID times to a local aware datetime."""
    params = params or {}
    if not value or params.get("VALUE", "").upper() == "DATE" or "T" not in value:
        return None
    try:
        if value.endswith("Z"):
            return datetime.strptime(value, "%Y%m%dT%H%M%SZ").replace(tzinfo=timezone.utc).astimezone()
        if re.search(r"[+-]\d{4}$", value):
            return datetime.strptime(value, "%Y%m%dT%H%M%S%z").astimezone()
        parsed = datetime.strptime(value, "%Y%m%dT%H%M%S")
        zone_name = params.get("TZID", "").strip('"')
        if zone_name:
            zone = QTimeZone(zone_name.encode("utf-8"))
            if not zone.isValid():
                return None  # avoid displaying a wrong time for an unknown zone
            qt = QDateTime(QDate(parsed.year, parsed.month, parsed.day),
                           QTime(parsed.hour, parsed.minute, parsed.second), zone)
            return datetime.fromtimestamp(qt.toSecsSinceEpoch(), timezone.utc).astimezone()
        return parsed.astimezone()
    except (ValueError, OverflowError):
        return None


def _ics_text(value):
    return value.replace("\\n", "\n").replace("\\N", "\n").replace("\\,", ",").replace("\\;", ";").replace("\\\\", "\\")


def _ics_days(rule, base, horizon):
    """Expand common Google RRULEs by calendar day, including weekday ordinals and counts."""
    freq = rule.get("FREQ", "")
    if freq not in ("DAILY", "WEEKLY", "MONTHLY", "YEARLY"):
        return
    try:
        interval = max(1, int(rule.get("INTERVAL", "1")))
        count = int(rule["COUNT"]) if "COUNT" in rule else None
    except ValueError:
        return
    if count is not None and count <= 0:
        return
    weekdays = {"MO": 0, "TU": 1, "WE": 2, "TH": 3, "FR": 4, "SA": 5, "SU": 6}
    byday = [x for x in rule.get("BYDAY", "").split(",") if x]
    bymonthday = [int(x) for x in rule.get("BYMONTHDAY", "").split(",") if re.fullmatch(r"-?\d+", x)]
    bymonth = [int(x) for x in rule.get("BYMONTH", "").split(",") if x.isdigit()]
    bysetpos = [int(x) for x in rule.get("BYSETPOS", "").split(",") if re.fullmatch(r"-?\d+", x)]
    wkst = weekdays.get(rule.get("WKST", "MO"), 0)
    first_week = base - timedelta(days=(base.weekday() - wkst) % 7)
    matched = 0
    day = base
    while day <= horizon:
        days_since = (day - base).days
        months_since = (day.year - base.year) * 12 + day.month - base.month
        period = {"DAILY": days_since, "WEEKLY": (day - first_week).days // 7,
                  "MONTHLY": months_since, "YEARLY": day.year - base.year}[freq]
        valid = period % interval == 0
        if bymonth and day.month not in bymonth:
            valid = False
        elif freq == "YEARLY" and not bymonth and day.month != base.month:
            valid = False
        days_in_month = monthrange(day.year, day.month)[1]
        if bymonthday:
            valid = valid and day.day in [x if x > 0 else days_in_month + x + 1 for x in bymonthday]
        elif freq in ("MONTHLY", "YEARLY") and not byday and day.day != base.day:
            valid = False
        if byday:
            day_ok = False
            for entry in byday:
                match = re.fullmatch(r"(-?\d)?(MO|TU|WE|TH|FR|SA|SU)", entry)
                if not match or weekdays[match.group(2)] != day.weekday():
                    continue
                nth = int(match.group(1)) if match.group(1) else None
                if nth is None or (nth > 0 and (day.day - 1) // 7 + 1 == nth) or (
                        nth < 0 and (days_in_month - day.day) // 7 + 1 == -nth):
                    day_ok = True
            valid = valid and day_ok
        elif freq == "WEEKLY":
            valid = valid and day.weekday() == base.weekday()
        if valid and bysetpos and byday and freq in ("MONTHLY", "YEARLY"):
            # Google's common "second Tuesday" form: BYDAY=TU;BYSETPOS=2.
            matching = [d for d in range(1, days_in_month + 1)
                        if datetime(day.year, day.month, d).weekday() in
                        [weekdays[x[-2:]] for x in byday if x[-2:] in weekdays]]
            valid = day.day in [matching[p - 1] if p > 0 and p <= len(matching) else
                                matching[p] if p < 0 and -p <= len(matching) else -1 for p in bysetpos]
        if valid:
            matched += 1
            if count is not None and matched > count:
                return
            yield day
        day += timedelta(days=1)


def calendar_ics_events(content, now, past_days=0):
    """Read a private Google iCal feed, including recurring instances and changed/cancelled ones."""
    raw_events = _ics_properties(_ics_lines(content))
    changes = {}
    for item in raw_events:
        uid = _ics_value(item, "UID")[0]
        rid, params = _ics_value(item, "RECURRENCE-ID")
        if uid and rid:
            when = _ics_datetime(rid, params)
            if when:
                changes.setdefault(uid, {})[int(when.timestamp())] = item
    horizon = now + timedelta(days=14)
    results = []

    def add(item, start, end):
        if not start or not end or end <= now - timedelta(days=past_days) or start > horizon or end <= start or end - start >= timedelta(hours=24):
            return
        if _ics_value(item, "STATUS")[0] == "CANCELLED" or _ics_value(item, "TRANSP")[0] == "TRANSPARENT":
            return
        title = _ics_text(_ics_value(item, "SUMMARY")[0]) or "Busy"
        url = _ics_value(item, "URL")[0] or _ics_value(item, "X-GOOGLE-CONFERENCE")[0]
        location = _ics_text(_ics_value(item, "LOCATION")[0])
        description = _ics_text(_ics_value(item, "DESCRIPTION")[0])
        join = re.search(r"https://(?:meet\.google\.com|[^/\s]+\.zoom\.us|teams\.microsoft\.com)/[^\s<>]+",
                         location + " " + description)
        if join:
            url = join.group(0).rstrip(".,;)")
        if not isinstance(url, str) or not url.startswith("https://"):
            url = ""
        event_color = _ics_value(item, "COLOR")[0]
        uid = _ics_value(item, "UID")[0]
        results.append({"title": title, "start": start, "end": end, "url": url,
                        "location": location, "details": event_details_text(description), "join": bool(join), "event_color": calendar_ics_color(event_color),
                        "series_key": calendar_series_key(uid) if uid else ""})

    for item in raw_events:
        if _ics_value(item, "RECURRENCE-ID")[0]:
            continue
        start_raw, start_params = _ics_value(item, "DTSTART")
        end_raw, end_params = _ics_value(item, "DTEND")
        start, end = _ics_datetime(start_raw, start_params), _ics_datetime(end_raw, end_params)
        if not start or not end:
            continue
        duration = end - start
        uid = _ics_value(item, "UID")[0]
        exceptions = changes.get(uid, {})
        exdates = set()
        for value, params in item.get("EXDATE", []):
            for part in value.split(","):
                dt = _ics_datetime(part, params)
                if dt:
                    exdates.add(int(dt.timestamp()))
        occurrences = [start]
        rrule = _ics_value(item, "RRULE")[0]
        if rrule:
            rule = dict(part.split("=", 1) for part in rrule.split(";") if "=" in part)
            until_raw = rule.get("UNTIL", "")
            until = _ics_datetime(until_raw, start_params)
            until_date = None
            if until_raw and until is None:
                try:
                    until_date = datetime.strptime(until_raw, "%Y%m%d").date()
                except ValueError:
                    continue  # an unreadable end date must not turn a past series into an endless one
            base_date = datetime.strptime(start_raw[:8], "%Y%m%d").date()
            occurrences = []
            for date in _ics_days(rule, base_date, horizon.date()):
                raw = f"{date:%Y%m%d}" + start_raw[8:]
                instant = _ics_datetime(raw, start_params)
                if instant and (not until or instant <= until) and (not until_date or date <= until_date):
                    occurrences.append(instant)
        for value, params in item.get("RDATE", []):
            occurrences.extend(dt for part in value.split(",") if (dt := _ics_datetime(part, params)))
        for occurrence in occurrences:
            stamp = int(occurrence.timestamp())
            if stamp not in exdates and stamp not in exceptions:
                add(item, occurrence, occurrence + duration)
    for exception in (e for group in changes.values() for e in group.values()):
        start_raw, start_params = _ics_value(exception, "DTSTART")
        end_raw, end_params = _ics_value(exception, "DTEND")
        add(exception, _ics_datetime(start_raw, start_params), _ics_datetime(end_raw, end_params))
    return sorted(results, key=lambda e: (e["start"], e["end"]))


class GoogleCalendar(QObject):
    """Read-only calendar service; HTTP work runs in threads and returns through Qt signals."""
    changed = Signal()
    events_updated = Signal()
    _finished = Signal(object)

    def __init__(self, store):
        super().__init__()
        self.store = store
        self.events = []
        self.recent_events = []
        self._feed_events = []
        self.calendars = []
        self.status = "Connect Google Calendar to see your next meeting."
        self.busy = False
        self.generation = 0
        self._finished.connect(self._on_finished)
        self.poll = QTimer(self)
        self.poll.setInterval(5 * 60 * 1000)
        self.poll.timeout.connect(self.refresh)
        if self.connected:
            self.refresh()       # network work runs in a thread while the rest of the UI is built

    @property
    def connected(self):
        auth = self.store.settings.get("google_calendar_auth")
        oauth = isinstance(auth, dict) and bool(auth.get("refresh_token") and auth.get("client_id"))
        return oauth or self.feed_connected

    @property
    def feed_connected(self):
        return bool(self.store.settings.get("google_calendar_feeds") or self.store.settings.get("google_calendar_feed"))

    @property
    def feed_items(self):
        """Expose the old single link as one selectable calendar until the next save."""
        items = self.store.settings.get("google_calendar_feeds")
        if isinstance(items, list) and (items or not self.store.settings.get("google_calendar_feed")):
            return [dict(item) for item in items if isinstance(item, dict) and item.get("url")]
        old = self.store.settings.get("google_calendar_feed")
        return [{"id": "legacy", "url": old, "name": "Calendar 1",
                 "color": CALENDAR_COLORS[0], "enabled": True}] if old else []

    def _save_feed_items(self, items):
        self.store.settings["google_calendar_feeds"] = items
        self.store.settings.pop("google_calendar_feed", None)
        self.store.save()

    def _visible_feed_events(self):
        enabled = {item["id"] for item in self.feed_items if item.get("enabled", True)}
        now = datetime.now().astimezone()
        hidden = set(self.store.settings.get("google_calendar_hidden_series") or [])
        return sorted((e for e in self._feed_events if e.get("calendar_id") in enabled and
                       e["end"] > now and e["start"] <= now + timedelta(days=14) and
                       e.get("series_key") not in hidden),
                      key=lambda e: (e["start"], e["end"]))

    def _visible_recent_feed_events(self):
        enabled = {item["id"] for item in self.feed_items if item.get("enabled", True)}
        now = datetime.now().astimezone()
        hidden = set(self.store.settings.get("google_calendar_hidden_series") or [])
        return sorted((e for e in self._feed_events if e.get("calendar_id") in enabled and
                       now - timedelta(days=14) < e["end"] <= now and
                       e.get("series_key") not in hidden),
                      key=lambda e: (e["start"], e["end"]))

    def _sync_feed_views(self):
        self.events = self._visible_feed_events()
        self.recent_events = self._visible_recent_feed_events()

    def hide_event_series(self, event):
        key = event.get("series_key")
        if not key:
            return
        hidden = list(self.store.settings.get("google_calendar_hidden_series") or [])
        if key not in hidden:
            hidden.append(key)
            self.store.settings["google_calendar_hidden_series"] = hidden
            self.store.save()
        self.events = [e for e in self.events if e.get("series_key") != key]
        self.recent_events = [e for e in self.recent_events if e.get("series_key") != key]
        self.events_updated.emit()
        self.changed.emit()

    def show_hidden_event_series(self):
        self.store.settings.pop("google_calendar_hidden_series", None)
        self.store.save()
        if self.feed_connected:
            self._sync_feed_views()
            self.events_updated.emit()
            self.changed.emit()
        elif self.connected:
            if self.busy:
                self.generation += 1
                self.busy = False
            self.refresh()

    def set_feed_enabled(self, feed_id, enabled):
        items = self.feed_items
        for item in items:
            if item["id"] == feed_id:
                item["enabled"] = bool(enabled)
        self._save_feed_items(items)
        self._sync_feed_views()
        self.events_updated.emit()
        self.changed.emit()
        if enabled:
            if self.busy:
                self.generation += 1
                self.busy = False
            self.refresh()

    def set_feed_name(self, feed_id, name):
        items = self.feed_items
        for item in items:
            if item["id"] == feed_id:
                item["name"] = name.strip()[:80] or item["name"]
                item["custom_name"] = True
        self._save_feed_items(items)
        for event in self._feed_events:
            if event.get("calendar_id") == feed_id:
                event["calendar_name"] = next(i["name"] for i in items if i["id"] == feed_id)
        self._sync_feed_views()
        self.events_updated.emit()
        self.changed.emit()

    def set_feed_color(self, feed_id, color):
        items = self.feed_items
        for item in items:
            if item["id"] == feed_id:
                item["color"] = calendar_color(color)
                item["custom_color"] = True
        self._save_feed_items(items)
        for event in self._feed_events:
            if event.get("calendar_id") == feed_id:
                event["calendar_color"] = calendar_color(color)
                if not event.get("source_event_color"):
                    event["event_color"] = event["calendar_color"]
        self._sync_feed_views()
        self.events_updated.emit()
        self.changed.emit()

    def remove_feed(self, feed_id):
        self.generation += 1
        self.busy = False
        items = [item for item in self.feed_items if item["id"] != feed_id]
        self._save_feed_items(items)
        self._feed_events = [e for e in self._feed_events if e.get("calendar_id") != feed_id]
        self._sync_feed_views()
        if not items:
            self.poll.stop()
            self.status = "No calendars connected."
        self.events_updated.emit()
        self.changed.emit()
        if items:
            self.refresh()

    @staticmethod
    def _download_feed(url):
        request = urllib.request.Request(url, headers={"Accept": "text/calendar", "User-Agent": "ParkThatThought/1.1"})
        try:
            with urllib.request.urlopen(request, timeout=15) as response:
                data = response.read(8 * 1024 * 1024 + 1)
        except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError):
            raise RuntimeError("Couldn't read this calendar link. Check the private iCal address and try again.") from None
        if len(data) > 8 * 1024 * 1024:
            raise RuntimeError("This calendar feed is too large to read safely.")
        text = data.decode("utf-8-sig", errors="replace")
        if "BEGIN:VCALENDAR" not in text[:200]:
            raise RuntimeError("This link did not return a calendar. Use Google's Secret address in iCal format.")
        return text

    def connect_feed(self, url):
        """Add one private Google calendar without a developer console or file picker."""
        url = url.strip()
        parsed = urllib.parse.urlparse(url)
        if parsed.scheme != "https" or parsed.hostname != "calendar.google.com" or not parsed.path.endswith(".ics"):
            self.status = "Paste the Secret address in iCal format from Google Calendar settings."
            self.changed.emit()
            return
        try:
            if any(calendar_token_blob(item["url"], encrypt=False) == url for item in self.feed_items):
                self.status = "This calendar is already connected."
                self.changed.emit()
                return
        except Exception:
            self.status = "Couldn't read a saved calendar link. Reconnect it."
            self.changed.emit()
            return
        feed_count = len(self.feed_items)
        self.generation += 1
        generation = self.generation
        self.busy = True
        self.status = "Checking your private calendar link..."
        self.changed.emit()

        def verify():
            try:
                content = self._download_feed(url)
                events = calendar_ics_events(content, datetime.now().astimezone(), past_days=14)
                secured = calendar_token_blob(url)
                name, color = calendar_ics_metadata(content)
                item = {"id": uuid.uuid4().hex, "url": secured,
                        "name": name or f"Calendar {feed_count + 1}",
                        "color": color or CALENDAR_COLORS[feed_count % len(CALENDAR_COLORS)],
                        "enabled": True}
                for event in events:
                    source_color = event.get("event_color")
                    event.update(calendar_id=item["id"], calendar_name=item["name"],
                                 calendar_color=item["color"],
                                 source_event_color=bool(source_color),
                                 event_color=calendar_color(source_color, item["color"]))
                self._finished.emit((generation, "feed_auth", (item, events)))
            except Exception as exc:
                self._finished.emit((generation, "feed_auth_error", str(exc)))
        threading.Thread(target=verify, daemon=True).start()

    def connect_file(self, path):
        if not IS_WIN:
            self.status = "Google Calendar connection needs Windows."
            self.changed.emit()
            return
        try:
            credentials = json.loads(Path(path).read_text(encoding="utf-8"))["installed"]
            client, secret = credentials["client_id"], credentials["client_secret"]
            if not client.endswith(".apps.googleusercontent.com") or not secret:
                raise ValueError()
        except (OSError, KeyError, TypeError, ValueError, AttributeError):
            self.status = "Choose a Google Desktop app OAuth credentials JSON file."
            self.changed.emit()
            return
        state, verifier = secrets.token_urlsafe(32), secrets.token_urlsafe(64)
        challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode()).digest()).rstrip(b"=").decode()
        self.generation += 1
        generation = self.generation
        owner = self
        received = threading.Event()

        class Callback(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_GET(self):
                parsed = urllib.parse.urlparse(self.path)
                values = urllib.parse.parse_qs(parsed.query)
                valid = parsed.path == "/callback" and values.get("state", [None])[0] == state
                code = values.get("code", [""])[0] if valid else ""
                error = values.get("error", [""])[0] if valid else "Invalid callback."
                self.send_response(200 if valid else 400)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.end_headers()
                message = "Calendar connected. You can close this tab." if code else "Sign-in was not completed."
                self.wfile.write(message.encode())
                if valid:
                    received.set()
                    owner._finished.emit((generation, "code", (code, error, client, secret, verifier, redirect)))

        try:
            server = http.server.HTTPServer(("127.0.0.1", 0), Callback)
        except OSError:
            self.status = "Couldn't start local sign-in. Try again."
            self.changed.emit()
            return
        redirect = f"http://127.0.0.1:{server.server_port}/callback"
        auth_url = "https://accounts.google.com/o/oauth2/v2/auth?" + urllib.parse.urlencode({
            "client_id": client, "redirect_uri": redirect, "response_type": "code",
            "scope": GOOGLE_CALENDAR_SCOPE, "access_type": "offline", "prompt": "consent",
            "state": state, "code_challenge": challenge, "code_challenge_method": "S256"})
        if not QDesktopServices.openUrl(QUrl(auth_url)):
            server.server_close()
            self.status = "Couldn't open your browser for Google sign-in."
            self.changed.emit()
            return
        self.busy = True
        self.status = "Complete the read-only Google sign-in in your browser."
        self.changed.emit()

        def wait_for_code():
            try:
                deadline = time.monotonic() + 180
                while not received.is_set() and time.monotonic() < deadline:
                    server.timeout = min(1, max(0.1, deadline - time.monotonic()))
                    server.handle_request()
                if not received.is_set():
                    owner._finished.emit((generation, "timeout", None))
            finally:
                server.server_close()
        threading.Thread(target=wait_for_code, daemon=True).start()

    def _on_finished(self, result):
        generation, kind, data = result
        if generation != self.generation:
            return
        if kind == "timeout":
            if self.busy and self.status.startswith("Complete the"):
                self.busy = False
                self.status = "Sign-in timed out. Try again."
                self.changed.emit()
            return
        if kind == "code":
            code, error, client, secret, verifier, redirect = data
            if not code:
                self.busy = False
                self.status = "Google sign-in was cancelled. Try again."
                self.changed.emit()
                return
            self.status = "Finishing calendar connection..."
            self.changed.emit()

            def exchange():
                try:
                    token = calendar_json("https://oauth2.googleapis.com/token", form={
                        "code": code, "client_id": client, "client_secret": secret,
                        "redirect_uri": redirect, "grant_type": "authorization_code", "code_verifier": verifier})
                    refresh = token.get("refresh_token")
                    if not refresh:
                        raise RuntimeError("Google did not return a reusable connection. Try again.")
                    secured = calendar_token_blob(refresh)
                    self._finished.emit((generation, "auth", {"client_id": client, "client_secret": secret,
                                                               "refresh_token": secured}))
                except Exception as exc:
                    self._finished.emit((generation, "error", str(exc)))
            threading.Thread(target=exchange, daemon=True).start()
            return
        self.busy = False
        if kind == "auth":
            self.store.settings["google_calendar_auth"] = data
            self.store.settings.pop("google_calendar_feed", None)
            self.store.settings.pop("google_calendar_feeds", None)
            self._feed_events = []
            self.events, self.recent_events = [], []
            self.store.save()
            self.status = "Connected. Loading meetings..."
            self.events_updated.emit()
            self.changed.emit()
            self.refresh()
        elif kind == "feed_auth":
            item, events = data
            self._save_feed_items(self.feed_items + [item])
            self._feed_events.extend(events)
            self._sync_feed_views()
            self.calendars = []
            self.status = ("Calendar added. No upcoming timed events in the next 14 days."
                           if not self.events else "Calendar added. Events are up to date.")
            self.poll.start()
            self.events_updated.emit()
            self.changed.emit()
        elif kind == "feed_events":
            self._feed_events, failures, metadata = data
            items = self.feed_items
            changed_items = "google_calendar_feed" in self.store.settings
            for item in items:
                name, color = metadata.get(item["id"], ("", ""))
                if name and not item.get("custom_name") and item["name"] != name:
                    item["name"] = name
                    changed_items = True
                if color and not item.get("custom_color") and item.get("color") != color:
                    item["color"] = color
                    changed_items = True
            if changed_items:
                self._save_feed_items(items)
            sources = {item["id"]: item for item in items}
            for event in self._feed_events:
                item = sources.get(event.get("calendar_id"))
                if item:
                    event["calendar_name"] = item["name"]
                    event["calendar_color"] = calendar_color(item.get("color"))
                    if not event.get("source_event_color"):
                        event["event_color"] = event["calendar_color"]
            self._sync_feed_views()
            self.status = (f"Couldn't update {failures} calendar{'s' if failures != 1 else ''}. Try Refresh now."
                           if failures else "Connected. No upcoming timed events in the next 14 days."
                           if not self.events else "Connected. Events are up to date.")
            self.poll.start()
            self.events_updated.emit()
            self.changed.emit()
        elif kind == "feed_auth_error":
            self.status = data or "Couldn't add this calendar."
            self.changed.emit()
        elif kind == "events":
            self.calendars, all_events = data
            hidden = set(self.store.settings.get("google_calendar_hidden_series") or [])
            now = datetime.now().astimezone()
            self.events = [e for e in all_events if e["end"] > now and e.get("series_key") not in hidden]
            self.recent_events = [e for e in all_events if e["end"] <= now and e.get("series_key") not in hidden]
            self.status = ("Connected. No timed meetings in the next 14 days." if not self.events
                           else "Connected. Meetings are up to date.")
            self.poll.start()
            self.events_updated.emit()
            self.changed.emit()
        elif kind == "error":
            self.status = data or "Couldn't update Google Calendar."
            self.events = []  # never present an old meeting as a fresh one
            self.recent_events = []
            if self.connected:
                self.poll.start()
            self.events_updated.emit()
            self.changed.emit()

    def refresh(self):
        if not self.connected or self.busy:
            return
        self.busy = True
        self.generation += 1
        generation = self.generation
        auth = dict(self.store.settings.get("google_calendar_auth") or {})
        selected = self.store.settings.get("google_calendar_selected")
        self.status = "Updating meetings..."
        self.changed.emit()

        if self.feed_connected:
            items = [dict(item) for item in self.feed_items if item.get("enabled", True)]
            def fetch_feed():
                events, failures, metadata = [], 0, {}
                for item in items:
                    try:
                        url = calendar_token_blob(item["url"], encrypt=False)
                        content = self._download_feed(url)
                        metadata[item["id"]] = calendar_ics_metadata(content)
                        for event in calendar_ics_events(content, datetime.now().astimezone(), past_days=14):
                            source_color = event.get("event_color")
                            event.update(calendar_id=item["id"], calendar_name=item["name"],
                                         calendar_color=calendar_color(item.get("color")),
                                         source_event_color=bool(source_color),
                                         event_color=calendar_color(source_color,
                                                                    calendar_color(item.get("color"))))
                            events.append(event)
                    except Exception:
                        failures += 1
                self._finished.emit((generation, "feed_events", (events, failures, metadata)))
            threading.Thread(target=fetch_feed, daemon=True).start()
            return

        def fetch():
            try:
                refresh_token = calendar_token_blob(auth["refresh_token"], encrypt=False)
                access = calendar_json("https://oauth2.googleapis.com/token", form={
                    "client_id": auth["client_id"], "client_secret": auth["client_secret"],
                    "refresh_token": refresh_token, "grant_type": "refresh_token"})["access_token"]
                calendars = calendar_pages("/users/me/calendarList", access,
                                           {"maxResults": 250, "showHidden": "false"})
                calendars = [c for c in calendars if not c.get("hidden")]
                ids = [c["id"] for c in calendars if (c.get("selected", True) if selected is None
                                                       else c.get("id") in selected)]
                try:
                    palette = calendar_json("https://www.googleapis.com/calendar/v3/colors",
                                            token=access).get("event", {})
                except Exception:
                    palette = {}
                now = datetime.now(timezone.utc)
                params = {"singleEvents": "true", "orderBy": "startTime", "maxResults": 250,
                          "timeMin": (now - timedelta(days=14)).isoformat(),
                          "timeMax": (now + timedelta(days=14)).isoformat()}
                rows = []
                for calendar_id in ids:
                    path = "/calendars/" + urllib.parse.quote(calendar_id, safe="") + "/events"
                    source = next(c for c in calendars if c["id"] == calendar_id)
                    try:
                        metadata = calendar_json("https://www.googleapis.com/calendar/v3" +
                                                 "/calendars/" + urllib.parse.quote(calendar_id, safe=""),
                                                 token=access)
                        labels = {str(label.get("id")): label.get("backgroundColor")
                                  for label in metadata.get("labelProperties", {}).get("eventLabels", [])
                                  if isinstance(label, dict) and label.get("id")}
                    except Exception:
                        labels = {}
                    for row in calendar_pages(path, access, params):
                        row["_calendar_id"] = calendar_id
                        row["_calendar_name"] = str(source.get("summaryOverride") or source.get("summary") or "Calendar")
                        row["_calendar_color"] = calendar_color(source.get("backgroundColor"))
                        row["_event_color"] = google_event_color(row, palette, labels, row["_calendar_color"])
                        rows.append(row)
                self._finished.emit((generation, "events", (calendars, calendar_events(rows, now.astimezone(), past_days=14))))
            except Exception as exc:
                self._finished.emit((generation, "error", str(exc)))
        threading.Thread(target=fetch, daemon=True).start()

    def choose_calendars(self, ids):
        self.store.settings["google_calendar_selected"] = list(ids)
        self.store.save()
        self.events = [e for e in self.events if e.get("calendar_id") in ids]
        self.recent_events = [e for e in self.recent_events if e.get("calendar_id") in ids]
        self.events_updated.emit()
        self.changed.emit()
        if self.busy:
            self.generation += 1
            self.busy = False
        self.refresh()

    def disconnect(self):
        self.generation += 1
        self.poll.stop()
        self.store.settings.pop("google_calendar_auth", None)
        self.store.settings.pop("google_calendar_feed", None)
        self.store.settings.pop("google_calendar_feeds", None)
        self.store.settings.pop("google_calendar_selected", None)
        self.store.save()
        self.busy = False
        self.events, self.recent_events, self.calendars, self._feed_events = [], [], [], []
        self.status = "Google Calendar disconnected."
        self.events_updated.emit()
        self.changed.emit()


class MeetingGlint(QWidget):
    """Slanted light bands cross the whole meeting bar, then leave a quiet gap."""
    def __init__(self, parent):
        super().__init__(parent)
        self.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.style = "triple"
        self.started = time.monotonic()
        self.timer = QTimer(self)
        self.timer.setInterval(40)
        self.timer.timeout.connect(self.update)
        self.hide()

    def set_active(self, active, style="triple"):
        self.style = style
        active = active and style != "off"
        if active and not self.timer.isActive():
            self.started = time.monotonic()
            self.show()
            self.timer.start()
        elif not active and self.timer.isActive():
            self.timer.stop()
            self.hide()
        elif active:
            self.update()

    def paintEvent(self, _event):
        if self.style == "off" or self.width() < 20 or self.height() < 10:
            return
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        clip = QPainterPath()
        clip.addRoundedRect(QRectF(1, 1, self.width() - 2, self.height() - 2), 11, 11)
        p.setClipPath(clip)
        cycle = ((time.monotonic() - self.started) % 6.0) / 6.0
        if self.style == "sun":
            bands = [(0.0, 64, "#ffe1a0", 125)]
        elif self.style == "prism":
            bands = [(0.0, 26, "#fff6d7", 115), (-0.12, 24, "#ffd69a", 100),
                     (-0.24, 22, "#bde9ff", 85)]
        else:
            bands = [(0.0, 30, "#fff5dc", 125), (-0.12, 24, "#ffe4b2", 100),
                     (-0.24, 19, "#ffffff", 90)]
        travel = self.width() + 180
        for offset, width, color, alpha in bands:
            position = (cycle + offset) % 1.0
            # Each band crosses the bar in sequence, with a pause between sweeps.
            if position > 0.62:
                continue
            x = -90 + travel * (position / 0.62)
            tilt = max(12, self.height() * 0.37)
            path = QPainterPath()
            path.moveTo(x, 0)
            path.lineTo(x + width, 0)
            path.lineTo(x + width - tilt, self.height())
            path.lineTo(x - tilt, self.height())
            path.closeSubpath()
            middle = QColor(color)
            middle.setAlpha(alpha)
            edge = QColor(color)
            edge.setAlpha(0)
            gradient = QLinearGradient(x - tilt, 0, x + width, 0)
            gradient.setColorAt(0, edge)
            gradient.setColorAt(0.48, middle)
            gradient.setColorAt(1, edge)
            p.fillPath(path, gradient)


def meeting_cue_copy(stage, minutes, stamp):
    """Plain facts. The heading and time line already say when, so most stages add nothing."""
    return {"started": "It has started.", "halfway": "{minutes} min left."}.get(stage, "").format(minutes=minutes)


class MeetingNotice(QWidget):
    """A compact, persistent cue beside the cloud. Later stages update it in place."""
    dismissed = Signal()

    def __init__(self, bubble):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.bubble = bubble
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setFocusPolicy(Qt.StrongFocus)
        self.current_stamp = None
        self.rank = -1
        self.suspended = False
        self.tail_right = True
        self.accent = QColor(C["accent"])
        self.stage = "lead_calm"
        self.url = ""
        self.arrive = QPropertyAnimation(self, b"pos", self)
        self.arrive.setDuration(220)
        self.arrive.setEasingCurve(QEasingCurve.OutCubic)
        self.setStyleSheet(STYLE + f"""
            QLabel#meetingCueHeading {{ color: {C['accent_text']}; font-size: 11px; font-weight: 700;
                letter-spacing: 1px; }}
            QLabel#meetingCueTitle {{ color: {C['text']}; font-size: 14px; font-weight: 700; }}
            QLabel#meetingCueInfo {{ color: {C['dim']}; font-size: 11px; }}
            QLabel#meetingCueBody {{ color: {C['text']}; font-size: 12px; }}
            QPushButton#meetingCueDone {{ background: {C['accent']}; color: white; border: none;
                border-radius: 7px; padding: 5px 11px; font-weight: 700; }}
            QPushButton#meetingCueOpen {{ background: {C['surface']}; color: {C['text']};
                border: 1px solid {C['border']}; border-radius: 7px; padding: 5px 11px; }}
        """)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(18, 15, 23, 13)
        lay.setSpacing(5)
        header = QHBoxLayout()
        header.setSpacing(6)
        self.face = EmojiFace(26)
        header.addWidget(self.face, 0, Qt.AlignTop)
        heading_text = QVBoxLayout()
        heading_text.setSpacing(1)
        self.heading = QLabel(self)
        self.heading.setObjectName("meetingCueHeading")
        self.heading.setTextFormat(Qt.PlainText)
        heading_text.addWidget(self.heading)
        self.event_title = QLabel(self)
        self.event_title.setObjectName("meetingCueTitle")
        self.event_title.setTextFormat(Qt.PlainText)
        self.event_title.setWordWrap(True)
        heading_text.addWidget(self.event_title)
        header.addLayout(heading_text, 1)
        lay.addLayout(header)
        self.info = QLabel(self)
        self.info.setObjectName("meetingCueInfo")
        self.info.setTextFormat(Qt.PlainText)
        self.info.setWordWrap(True)
        lay.addWidget(self.info)
        self.body = QLabel(self)
        self.body.setObjectName("meetingCueBody")
        self.body.setTextFormat(Qt.PlainText)
        self.body.setWordWrap(True)
        lay.addWidget(self.body)
        buttons = QHBoxLayout()
        buttons.addStretch(1)
        self.open_button = QPushButton("Join", self)
        self.open_button.setObjectName("meetingCueOpen")
        self.open_button.clicked.connect(self.open_event)
        buttons.addWidget(self.open_button)
        self.done_button = QPushButton("Got it", self)
        self.done_button.setObjectName("meetingCueDone")
        self.done_button.clicked.connect(self.dismiss)
        buttons.addWidget(self.done_button)
        lay.addLayout(buttons)

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        r = (QRectF(self.rect()).adjusted(1, 1, -10, -1) if self.tail_right else
             QRectF(self.rect()).adjusted(10, 1, -1, -1))
        path = QPainterPath()
        path.addRoundedRect(r, 15, 15)
        cy = min(r.bottom() - 20, max(r.top() + 20, getattr(self, "_tail_y", r.center().y())))
        tail = QPainterPath()
        if self.tail_right:
            tail.moveTo(r.right() - 1, cy - 9)
            tail.lineTo(r.right() + 9, cy)
            tail.lineTo(r.right() - 1, cy + 9)
        else:
            tail.moveTo(r.left() + 1, cy - 9)
            tail.lineTo(r.left() - 9, cy)
            tail.lineTo(r.left() + 1, cy + 9)
        p.setBrush(QColor(C["surface_hi"]))
        p.setPen(QPen(self.accent, 1.6))
        p.drawPath(path.united(tail))
        p.setPen(Qt.NoPen)
        p.setBrush(self.accent)
        p.drawRoundedRect(QRectF(r.left() + 1, r.top() + 15, 3, r.height() - 30), 1.5, 1.5)

    def place(self):
        circle = self.bubble.geometry()
        area = screen_for(self, circle.center()).availableGeometry()
        desired = 300 if self.stage == "finished" else 318 if self.stage in ("started", "halfway") else 336
        self.setFixedWidth(min(desired, max(240, area.width() - 24)))
        self.tail_right = circle.center().x() > area.center().x()
        self.layout().setContentsMargins(18 if self.tail_right else 23, 15,
                                         23 if self.tail_right else 18, 13)
        self.adjustSize()
        x = circle.left() - self.width() - 4 if self.tail_right else circle.right() + 4
        y = circle.center().y() - self.height() // 2
        x = max(area.left() + 3, min(x, area.right() - self.width() - 2))
        y = max(area.top() + 3, min(y, area.bottom() - self.height() - 2))
        self._tail_y = circle.center().y() - y
        self.move(x, y)
        self.update()

    def show_notice(self, stamp, rank, stage, heading, event, body, emoji, color):
        fresh_stage = stamp != self.current_stamp or rank != self.rank
        self.current_stamp, self.rank = stamp, rank
        self.stage = stage
        self.suspended = False
        self.accent = QColor(color)
        self.heading.setText(heading)
        if theme_dark():
            label_color = self.accent.lighter(145).name() if self.accent.lightness() < 130 else color
        else:   # warm tones like amber wash out on white: take them darker
            label_color = self.accent.darker(165).name() if self.accent.lightness() > 110 else color
        self.heading.setStyleSheet(f"color: {label_color};")
        self.event_title.setText(event.get("title") or "Meeting")
        start = event["start"].strftime("%-I:%M %p") if os.name != "nt" else event["start"].strftime("%#I:%M %p")
        end = event["end"].strftime("%-I:%M %p") if os.name != "nt" else event["end"].strftime("%#I:%M %p")
        when = (f"Ended {end}" if stage == "finished" else
                f"Ends {end}" if stage in ("started", "halfway") else f"{start} to {end}")
        self.info.setText(when + (f" · {event['calendar_name']}" if event.get("calendar_name") else ""))
        self.body.setText(body)
        self.body.setVisible(bool(body))
        self.face.set(emoji, "tilt" if stage == "finished" else "bounce")
        self.url = event.get("url") or ""
        self.open_button.setVisible(bool(self.url) and stage != "finished")
        self.open_button.setText("Join" if event.get("join") else "Open")
        button_text = "white" if self.accent.lightness() < 130 else "#18202b"
        self.done_button.setStyleSheet(f"background: {color}; color: {button_text};")
        self.place()
        destination = self.pos()
        self.arrive.stop()
        if fresh_stage:
            self.move(destination + QPoint(16 if self.tail_right else -16, 0))
        self.show()
        self.raise_()
        apply_share_privacy(self)
        if fresh_stage:
            self.arrive.setStartValue(self.pos())
            self.arrive.setEndValue(destination)
            self.arrive.start()

    def refresh_time(self, now, event):
        """Keep a persistent card's countdown truthful between stage changes."""
        if self.stage.startswith("lead_"):
            left = max(1, math.ceil((event["start"] - now).total_seconds() / 60))
            self.heading.setText(f"IN {left} MIN")
        elif self.stage == "halfway":
            left = max(1, math.ceil((event["end"] - now).total_seconds() / 60))
            self.body.setText(meeting_cue_copy("halfway", left, self.current_stamp))

    def suspend(self):
        if self.current_stamp and self.isVisible():
            self.suspended = True
            self.hide()

    def resume(self):
        if self.current_stamp and self.suspended:
            self.suspended = False
            self.place()
            self.show()
            self.raise_()
            apply_share_privacy(self)

    def dismiss(self):
        self.clear()
        self.dismissed.emit()

    def clear(self):
        self.arrive.stop()
        self.current_stamp = None
        self.rank = -1
        self.suspended = False
        self.hide()

    def open_event(self):
        if self.url:
            QDesktopServices.openUrl(QUrl(self.url))
        self.dismiss()

    def take_keys(self):
        force_foreground(self)
        self.done_button.setFocus()

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Escape, Qt.Key_Return, Qt.Key_Enter, Qt.Key_Space):
            self.dismiss()
            event.accept()
        else:
            super().keyPressEvent(event)


def event_color(event):
    return calendar_color(event.get("event_color"), calendar_color(event.get("calendar_color")))


def event_when(event):
    start, end = event["start"], event["end"]
    day = start.strftime("%a %b %d").replace(" 0", " ")
    return f"{day}, {clock_text(start)} - {clock_text(end)}"


class EventDetails(QFrame):
    """What a calendar event is: title, time, calendar, place and notes, with Join and Open buttons.
    Esc or a click outside closes it."""

    def __init__(self, event, parent=None):
        super().__init__(parent, Qt.Popup | Qt.FramelessWindowHint)
        self.info = event
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setStyleSheet(full_style() + f"""
            QFrame#evInner {{ background: {C['surface_hi']}; border: 1px solid {C['border']}; border-radius: 12px; }}
            QLabel#evTitle {{ color: {C['text']}; font-size: 14px; font-weight: 700; }}
            QLabel#evLine {{ color: {C['text']}; font-size: 12px; }}
            QLabel#evDim {{ color: {C['dim']}; font-size: 12px; }}
            QPushButton#evJoin {{ background: {C['accent']}; border: 1px solid {C['accent']}; color: white;
                border-radius: 8px; padding: 6px 14px; font-weight: 700; }}
            QPushButton#evJoin:hover {{ background: #b54552; }}
            QPushButton#evOpen {{ background: transparent; border: 1px solid {C['border']}; color: {C['text']};
                border-radius: 8px; padding: 6px 12px; }}
            QPushButton#evOpen:hover, QPushButton#evOpen:focus {{ border-color: {C['text']}; }}""")
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        inner = QFrame(self)
        inner.setObjectName("evInner")
        inner.setMinimumWidth(280)
        outer.addWidget(inner)
        v = QVBoxLayout(inner)
        v.setContentsMargins(14, 12, 14, 12)
        v.setSpacing(5)
        head = QHBoxLayout()
        head.setSpacing(8)
        dot = QLabel(inner)
        dot.setFixedSize(10, 10)
        dot.setStyleSheet(f"background: {event_color(event)}; border-radius: 5px;")
        head.addWidget(dot, 0, Qt.AlignTop | Qt.AlignLeft)

        def label(text, name, parent=inner):
            lab = QLabel(text, parent)
            lab.setObjectName(name)
            lab.setWordWrap(True)
            lab.setTextFormat(Qt.PlainText)
            lab.setMaximumWidth(300)
            return lab
        self.title = label(event["title"], "evTitle")
        head.addWidget(self.title, 1)
        v.addLayout(head)
        self.when = label(event_when(event), "evLine")
        v.addWidget(self.when)
        for key in ("calendar_name", "location", "details"):
            if event.get(key):
                v.addWidget(label(event[key], "evDim"))
        buttons = QHBoxLayout()
        buttons.setSpacing(6)
        buttons.addStretch(1)
        self.open_btn = self.join_btn = None
        page = event.get("page") or ("" if event.get("join") else event.get("url", ""))
        if page:
            self.open_btn = QPushButton("Open in Google Calendar", inner)
            self.open_btn.setObjectName("evOpen")
            self.open_btn.clicked.connect(lambda: (QDesktopServices.openUrl(QUrl(page)), self.close()))
            buttons.addWidget(self.open_btn)
        if event.get("join") and event.get("url"):
            self.join_btn = QPushButton("Join call", inner)
            self.join_btn.setObjectName("evJoin")
            self.join_btn.clicked.connect(lambda: (QDesktopServices.openUrl(QUrl(event["url"])), self.close()))
            buttons.addWidget(self.join_btn)
        if self.open_btn or self.join_btn:
            v.addSpacing(4)
            v.addLayout(buttons)
        for b in (self.open_btn, self.join_btn):
            if b:
                b.setCursor(Qt.PointingHandCursor)

    def open_at(self, pos):
        self.adjustSize()
        area = screen_for(self, pos).availableGeometry()
        x = max(area.left(), min(pos.x(), area.right() - self.width()))
        y = max(area.top(), min(pos.y(), area.bottom() - self.height()))
        self.move(x, y)
        self.show()
        apply_share_privacy(self)
        (self.join_btn or self.open_btn or self).setFocus()


class AgendaGrid(QWidget):
    """The 24-hour grid of the floating calendar: one column per day, events as colored blocks, a red line at
    now. Click an event for its details; right-click to open it or hide its series. From the keyboard: Tab
    picks an event, Enter shows its details, the menu key or Shift+F10 shows its menu, Up and Down scroll."""

    HOUR = 48
    GUTTER = 50
    TOP = 8

    def __init__(self, agenda, parent):
        super().__init__(parent)
        self.agenda = agenda
        self.days, self.events, self.now = [], [], datetime.now().astimezone()
        self.blocks = []                    # (QRectF, event), in day then time order
        self.selected = -1
        self.hovered = -1
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setAccessibleName("Calendar hours. Tab picks an event, Enter shows its details.")
        self.details = None
        self.setMinimumHeight(self.TOP * 2 + 24 * self.HOUR)

    def sizeHint(self):
        return QSize(420, self.TOP * 2 + 24 * self.HOUR)

    def hour_y(self, hours):
        return self.TOP + hours * self.HOUR

    def col_rect(self, index):
        width = (self.width() - self.GUTTER - 6) / max(1, len(self.days) or 3)
        return QRectF(self.GUTTER + index * width, 0, width, self.height())

    def set_days(self, days, events, now):
        picked = self.blocks[self.selected][1] if 0 <= self.selected < len(self.blocks) else None
        self.days, self.events, self.now = days, events, now
        self._layout()
        keys = [(e["start"], e["title"]) for _, e in self.blocks]
        self.selected = keys.index((picked["start"], picked["title"])) if picked and \
            (picked["start"], picked["title"]) in keys else -1
        self.update()

    def resizeEvent(self, event):
        self._layout()
        super().resizeEvent(event)

    def _layout(self):
        """Place each day's events. Events that overlap share the column in side-by-side lanes."""
        self.blocks = []
        for index, day in enumerate(self.days):
            col = self.col_rect(index)
            start = datetime(day.year, day.month, day.day).astimezone()
            end = datetime.combine(day + timedelta(days=1), datetime.min.time()).astimezone()
            items = sorted(((max(e["start"], start), min(e["end"], end), e) for e in self.events
                            if e["start"] < end and e["end"] > start),
                           key=lambda t: (t[0], t[0] - t[1]))
            groups, group, lanes, group_end = [], [], [], None
            for s, f, e in items:
                if group and s >= group_end:
                    groups.append((group, len(lanes)))
                    group, lanes = [], []
                group_end = f if not group else max(group_end, f)
                lane = next((n for n, lane_end in enumerate(lanes) if lane_end <= s), len(lanes))
                lanes[lane:lane + 1] = [f]
                group.append((s, f, e, lane))
            if group:
                groups.append((group, len(lanes)))
            for group, count in groups:
                width = (col.width() - 6) / count
                for s, f, e, lane in group:
                    top = self.hour_y((s - start).total_seconds() / 3600)
                    bottom = self.hour_y((f - start).total_seconds() / 3600)
                    self.blocks.append((QRectF(col.x() + 3 + lane * width, top + 1, width - 2,
                                               max(bottom - top, 20) - 2), e))

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        small = QFont(self.font())
        small.setPixelSize(10)
        p.setFont(small)
        line = QColor(C["border"])
        today = self.now.date()
        for index, day in enumerate(self.days):
            col = self.col_rect(index)
            if day == today:
                p.fillRect(col, veil(9))
            p.setPen(QPen(line, 1))
            p.drawLine(QPointF(col.x(), 0), QPointF(col.x(), self.height()))
        for hour in range(25):
            y = self.hour_y(hour)
            p.setPen(QPen(line, 1))
            p.drawLine(QPointF(self.GUTTER - 5, y), QPointF(self.width() - 6, y))
            if 0 < hour < 24:
                p.setPen(QColor(C["dim"]))
                label = datetime(2000, 1, 1, hour).strftime("%I %p").lstrip("0")
                p.drawText(QRectF(0, y - 8, self.GUTTER - 10, 16), Qt.AlignRight | Qt.AlignVCenter, label)
        for n, (rect, e) in enumerate(self.blocks):
            past = e["end"] <= self.now
            color = QColor(event_color(e))
            fill = QColor(color)
            fill.setAlpha(95 if past else 235)
            p.setPen(Qt.NoPen)
            p.setBrush(fill)
            p.drawRoundedRect(rect, 5, 5)
            if n in (self.selected, self.hovered):
                p.setBrush(Qt.NoBrush)
                p.setPen(QPen(QColor(C["text"]), 1.6))
                p.drawRoundedRect(rect.adjusted(0.5, 0.5, -0.5, -0.5), 5, 5)
            ink = QColor(C["text"]) if past else ink_for(color)
            if past:
                ink.setAlpha(170)
            p.save()
            p.setClipRect(rect.adjusted(5, 2, -3, -2))
            text = rect.adjusted(6, 3, -4, -2)
            bold = QFont(small)
            bold.setWeight(QFont.DemiBold)
            p.setFont(bold)
            p.setPen(ink)
            time_text = clock_text(e["start"])
            if rect.height() >= 32:
                p.drawText(text, Qt.AlignLeft | Qt.AlignTop | Qt.TextWordWrap, e["title"])
                p.setFont(small)
                p.drawText(text, Qt.AlignLeft | Qt.AlignBottom, f"{time_text} - {clock_text(e['end'])}")
            else:
                p.drawText(text, Qt.AlignLeft | Qt.AlignVCenter, f"{e['title']}, {time_text}")
            p.restore()
        if today in self.days:
            col = self.col_rect(self.days.index(today))
            y = self.hour_y(self.now.hour + self.now.minute / 60)
            red = QColor("#ea4335")
            p.setPen(QPen(red, 2))
            p.drawLine(QPointF(col.x(), y), QPointF(col.right() - 2, y))
            p.setPen(Qt.NoPen)
            p.setBrush(red)
            p.drawEllipse(QPointF(col.x(), y), 5, 5)
        p.end()

    def block_at(self, pos):
        for n in range(len(self.blocks) - 1, -1, -1):
            if self.blocks[n][0].contains(QPointF(pos)):
                return n
        return -1

    def mouseMoveEvent(self, event):
        n = self.block_at(event.position().toPoint())
        if n != self.hovered:
            self.hovered = n
            self.setCursor(Qt.PointingHandCursor if n >= 0 else Qt.ArrowCursor)
            if n >= 0:
                e = self.blocks[n][1]
                tip = f"{e['title']}\n{event_when(e)}"
                if e.get("calendar_name"):
                    tip += "\n" + e["calendar_name"]
                self.setToolTip(tip + "\nClick for details. Right-click for more.")
            else:
                self.setToolTip("")
            self.update()
        super().mouseMoveEvent(event)

    def leaveEvent(self, event):
        self.hovered = -1
        self.update()
        super().leaveEvent(event)

    def mouseReleaseEvent(self, event):
        n = self.block_at(event.position().toPoint())
        if event.button() == Qt.LeftButton and n >= 0:
            self.selected = n
            self.update()
            self.show_details(n)
        super().mouseReleaseEvent(event)

    def show_details(self, n):
        rect = self.blocks[n][0]
        if self.details:
            self.details.close()
            self.details.deleteLater()
        self.details = EventDetails(self.blocks[n][1], self)
        self.details.open_at(self.mapToGlobal(QPoint(int(rect.right()) + 6, int(rect.top()))))

    def open_event(self, e):
        if e.get("url"):
            QDesktopServices.openUrl(QUrl(e["url"]))

    def event_menu(self, n, global_pos):
        menu = self.build_menu(n)
        apply_share_privacy(menu)
        menu.exec(global_pos)

    def build_menu(self, n):
        e = self.blocks[n][1]
        menu = QMenu(self)
        menu.setStyleSheet(full_style())
        menu.addAction("Open in Google Calendar", lambda: self.open_event(e)).setEnabled(bool(e.get("url")))
        if e.get("join"):
            menu.addAction("Join call", lambda: QDesktopServices.openUrl(QUrl(e["join"])))
        if e.get("series_key"):
            menu.addAction("Hide this series in PTT", lambda: self.agenda.calendar.hide_event_series(e))
        return menu

    def contextMenuEvent(self, event):
        n = self.block_at(event.pos()) if event.reason() == event.Reason.Mouse else self.selected
        if n >= 0:
            self.selected = n
            self.update()
            pos = event.globalPos() if event.reason() == event.Reason.Mouse else \
                self.mapToGlobal(self.blocks[n][0].bottomLeft().toPoint())
            self.event_menu(n, pos)

    def focusNextPrevChild(self, forward):
        if not self.blocks:
            return super().focusNextPrevChild(forward)
        if self.selected < 0:
            self.selected = 0 if forward else len(self.blocks) - 1
        else:
            self.selected = (self.selected + (1 if forward else -1)) % len(self.blocks)
        rect = self.blocks[self.selected][0]
        self.agenda.scroll.ensureVisible(int(rect.center().x()), int(rect.center().y()), 0,
                                         int(rect.height() / 2 + 30))
        self.update()
        return True

    def keyPressEvent(self, event):
        key = event.key()
        bar = self.agenda.scroll.verticalScrollBar()
        if key in (Qt.Key_Return, Qt.Key_Enter) and 0 <= self.selected < len(self.blocks):
            self.show_details(self.selected)
        elif key in (Qt.Key_Up, Qt.Key_Down):
            bar.setValue(bar.value() + (self.HOUR if key == Qt.Key_Down else -self.HOUR))
        elif key in (Qt.Key_PageUp, Qt.Key_PageDown):
            bar.setValue(bar.value() + (bar.pageStep() if key == Qt.Key_PageDown else -bar.pageStep()))
        else:
            self.agenda.keyPressEvent(event)
            return
        event.accept()


class AgendaDays(QWidget):
    """The day strip above the grid: weekday and date for each column, today in a filled circle."""

    def __init__(self, grid, parent):
        super().__init__(parent)
        self.grid = grid
        self.setFixedHeight(50)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        today = self.grid.now.date()
        offset = self.grid.mapTo(self.window(), QPoint(0, 0)).x() - self.mapTo(self.window(), QPoint(0, 0)).x()
        for index, day in enumerate(self.grid.days):
            col = self.grid.col_rect(index).translated(offset, 0)
            is_today = day == today
            past = day < today
            week = QFont(self.font())
            week.setPixelSize(10)
            week.setWeight(QFont.DemiBold)
            p.setFont(week)
            p.setPen(QColor(C["accent"] if is_today else C["faint"] if past else C["dim"]))
            p.drawText(QRectF(col.x(), 2, col.width(), 14), Qt.AlignCenter, day.strftime("%a").upper())
            circle = QRectF(col.center().x() - 15, 18, 30, 30)
            if is_today:
                p.setPen(Qt.NoPen)
                p.setBrush(QColor(C["accent"]))
                p.drawEllipse(circle)
            number = QFont(self.font())
            number.setPixelSize(17)
            number.setWeight(QFont.DemiBold if is_today else QFont.Normal)
            p.setFont(number)
            p.setPen(QColor("white" if is_today else C["faint"] if past else C["text"]))
            p.drawText(circle, Qt.AlignCenter, str(day.day))
        p.setPen(QPen(QColor(C["border"]), 1))
        p.drawLine(QPointF(0, self.height() - 0.5), QPointF(self.width(), self.height() - 0.5))
        p.end()


class CalendarAgenda(QWidget):
    """The floating calendar above the meeting bar: three days side by side over a full 24-hour grid, like
    Google Calendar's day view. It opens scrolled to the time chosen in Settings (around now by default);
    the rest of the day is a scroll away. Left and Right page three days, T returns to today."""

    def __init__(self, bar, calendar):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.bar, self.calendar = bar, calendar
        self.day_offset = 0
        self._refresh_pending = False
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setMinimumSize(390, 300)
        self.setFocusPolicy(Qt.StrongFocus)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        self.card = QFrame(self)
        self.card.setObjectName("agendaCard")
        outer.addWidget(self.card)
        lay = QVBoxLayout(self.card)
        lay.setContentsMargins(12, 10, 10, 8)
        lay.setSpacing(4)
        header = QHBoxLayout()
        header.setSpacing(4)

        def tool(text, tip, fn, name=None):
            b = QToolButton(self.card)
            b.setText(text)
            b.setToolTip(tip)
            b.setAccessibleName(name or tip)
            b.setCursor(Qt.PointingHandCursor)
            b.setAutoRaise(True)
            b.clicked.connect(fn)
            header.addWidget(b)
            return b
        self.today_btn = tool("Today", "Back to today (T)", self.go_today)
        self.today_btn.setObjectName("agendaToday")
        self.prev_btn = tool("‹", "Previous three days (Left arrow)", lambda: self.change_days(-3),
                             "Previous three days")
        self.next_btn = tool("›", "Next three days (Right arrow)", lambda: self.change_days(3), "Next three days")
        self.range_label = QLabel(self.card)
        self.range_label.setObjectName("agendaRange")
        header.addWidget(self.range_label, 1)
        self.new_btn = tool("+", "New event in Google Calendar (N)", self.new_event, "New event")
        self.meet_btn = tool("Meet", "Start a Google Meet now in your browser (M)", self.meet_now, "Meet now")
        self.refresh_btn = tool("↻", "Refresh Google Calendar now", self.manual_refresh)
        tool("✕", "Close calendar (Esc)", self.hide, "Close calendar")
        lay.addLayout(header)
        self.next_label = QLabel(self.card)
        self.next_label.setObjectName("agendaNext")
        self.next_label.setTextFormat(Qt.PlainText)
        lay.addWidget(self.next_label)
        self.scroll = QScrollArea(self.card)
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.viewport().setStyleSheet("background: transparent;")
        self.grid = AgendaGrid(self, self.scroll)
        self.days_strip = AgendaDays(self.grid, self.card)
        lay.addWidget(self.days_strip)
        self.scroll.setWidget(self.grid)
        lay.addWidget(self.scroll, 1)
        self.apply_background()
        calendar.events_updated.connect(self.refresh_later)
        calendar.changed.connect(self._refresh_feedback)
        self._manual = False
        self.minute = QTimer(self)
        self.minute.setInterval(60000)
        self.minute.timeout.connect(self.refresh_later)

    def apply_background(self):
        bg = meeting_bar_background(self.calendar.store.settings)
        self.card.setStyleSheet(
            f"QFrame#agendaCard {{ background: {bg}; border: 1px solid {C['border']}; border-radius: 14px; }}"
            f"QLabel#agendaRange {{ color: {C['text']}; font-size: 14px; font-weight: 700; padding-left: 6px; }}"
            f"QLabel#agendaNext {{ color: {C['dim']}; font-size: 11px; padding: 0 0 4px 2px; }}"
            f"QToolButton {{ color: {C['text']}; background: transparent; border: none; border-radius: 7px;"
            " padding: 3px 8px; font-size: 14px; min-width: 14px; min-height: 18px; }"
            f"QToolButton:hover, QToolButton:focus {{ background: {C['surface_hi']}; }}"
            f"QToolButton:disabled {{ color: {C['faint']}; }}"
            f"QToolButton#agendaToday {{ border: 1px solid {C['border']}; font-size: 12px; font-weight: 600;"
            " padding: 3px 10px; }"
            "QScrollBar:vertical { background: transparent; width: 8px; margin: 2px 0; }"
            f"QScrollBar::handle:vertical {{ background: {C['border']}; border-radius: 4px; min-height: 30px; }}"
            f"QScrollBar::handle:vertical:hover {{ background: {C['faint']}; }}"
            "QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }"
            "QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: transparent; }")

    def place(self):
        area = screen_for(self, self.bar.geometry().center()).availableGeometry()
        width = min(610, area.width() - 16)
        above = max(0, self.bar.geometry().top() - area.top() - 10)
        below = max(0, area.bottom() - self.bar.geometry().bottom() - 10)
        use_above = above >= 300 or above >= below
        room = above if use_above else below
        height = min(700, max(300, room))
        height = min(height, max(300, area.height() - 16))
        x = max(area.left() + 8, min(self.bar.x(), area.right() - width - 7))
        y = self.bar.y() - height - 8 if use_above else self.bar.geometry().bottom() + 8
        y = max(area.top() + 8, min(y, area.bottom() - height - 7))
        self.setGeometry(x, y, width, height)

    def focus_hours(self):
        """Where the grid opens: the hour chosen in Settings, or an hour before now."""
        hour = self.calendar.store.settings.get("agenda_start_hour", -1)
        if isinstance(hour, int) and 0 <= hour <= 23:
            return hour
        now = datetime.now()
        return max(0, now.hour + now.minute / 60 - 1)

    def scroll_to_focus(self):
        self.card.layout().activate()
        self.scroll.verticalScrollBar().setValue(int(self.grid.hour_y(self.focus_hours()) - self.grid.TOP))

    def toggle(self):
        if self.isVisible():
            self.hide()
            return
        if not self.calendar.connected or self.bar.fullscreen_suppressed:
            return
        self.day_offset = 0
        self.refresh()
        self.place()
        self.show()
        self.raise_()
        self.scroll_to_focus()
        self.grid.setFocus(Qt.PopupFocusReason)
        apply_share_privacy(self)
        self.minute.start()

    def hideEvent(self, event):
        self.minute.stop()
        super().hideEvent(event)

    def keyPressEvent(self, event):
        key = event.key()
        if key == Qt.Key_Escape:
            self.hide()
        elif key == Qt.Key_Left:
            self.change_days(-3)
        elif key == Qt.Key_Right:
            self.change_days(3)
        elif key == Qt.Key_T:
            self.go_today()
        elif key == Qt.Key_N:
            self.new_event()
        elif key == Qt.Key_M:
            self.meet_now()
        else:
            super().keyPressEvent(event)
            return
        event.accept()

    def new_event_start(self):
        """The next half hour today, or 9:00 AM on the first day shown when paged away from today."""
        now = datetime.now().astimezone()
        if self.day_offset:
            day = now.date() + timedelta(days=self.day_offset)
            return datetime(day.year, day.month, day.day, 9).astimezone()
        return now.replace(minute=0, second=0, microsecond=0) + timedelta(minutes=30 if now.minute < 30 else 60)

    def new_event(self):
        QDesktopServices.openUrl(QUrl(new_event_url(self.new_event_start())))

    def meet_now(self):
        QDesktopServices.openUrl(QUrl(MEET_NOW_URL))

    def manual_refresh(self):
        """The ↻ button: show it working, then a tick (or the error) so a click never looks ignored."""
        self._manual = True
        self.refresh_btn.setText("…")
        self.refresh_btn.setEnabled(False)
        self.calendar.refresh()
        self._refresh_feedback()

    def _refresh_feedback(self):
        if not self._manual or self.calendar.busy:
            return
        self._manual = False
        status = self.calendar.status
        failed = not status.startswith("Connected")      # every successful update says "Connected. ..."
        self.refresh_btn.setText("!" if failed else "✓")
        self.refresh_btn.setToolTip(status if failed else "Updated just now")
        if failed:     # after the redraw that events_updated queued, or it would be overwritten
            QTimer.singleShot(0, lambda: self.next_label.setText(status))

        def reset():
            self.refresh_btn.setText("↻")
            self.refresh_btn.setToolTip("Refresh Google Calendar now")
            self.refresh_btn.setEnabled(True)
        QTimer.singleShot(4000 if failed else 1500, reset)

    def change_days(self, amount):
        self.day_offset = max(-12, min(12, self.day_offset + amount))
        self.refresh_later()

    def go_today(self):
        self.day_offset = 0
        self.refresh_later()
        self.scroll_to_focus()

    def refresh_later(self):
        if not self.isVisible() or self._refresh_pending:
            return
        self._refresh_pending = True
        QTimer.singleShot(0, self.refresh)

    def refresh(self):
        self._refresh_pending = False
        now = datetime.now().astimezone()
        events = sorted(self.calendar.recent_events + self.calendar.events, key=lambda e: (e["start"], e["end"]))
        base = now.date() + timedelta(days=self.day_offset)
        days = [base + timedelta(days=i) for i in range(3)]
        self.grid.set_days(days, events, now)
        first, last = days[0], days[-1]
        tail = last.strftime("%d").lstrip("0") if first.month == last.month else last.strftime("%b ") + str(last.day)
        self.range_label.setText(f"{first:%b} {first.day} - {tail}" + (f", {last.year}" if last.year != now.year
                                                                          else ""))
        self.prev_btn.setEnabled(self.day_offset > -12)
        self.next_btn.setEnabled(self.day_offset < 12)
        self.today_btn.setEnabled(self.day_offset != 0)
        current = next((e for e in events if e["start"] <= now < e["end"]), None)
        upcoming = next((e for e in events if e["start"] > now), None)
        if current:
            text = f"Now: {current['title']}, {max(1, math.ceil((current['end'] - now).total_seconds() / 60))} min left"
            if upcoming:
                text += f". Then {upcoming['title']} at {clock_text(upcoming['start'])}"
        elif upcoming:
            text = f"Next: {upcoming['title']} in {short_span((upcoming['start'] - now).total_seconds())}"
        else:
            text = "Nothing else coming up."
        self.next_label.setText(text)
        self.days_strip.update()


class MeetingBadge(QWidget):
    """Calendar bar docked over the taskbar or placed freely on the desktop."""
    placement_changed = Signal(str)

    def __init__(self, bubble, calendar):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.bubble, self.calendar = bubble, calendar
        self.current_event = None
        self.fullscreen_suppressed = False
        self.open_settings = lambda: None
        self._ready = False
        self._drag_from = None
        self._drag_start = None
        self._did_drag = False
        self._drag_origin_geometry = None
        self.placement = meeting_bar_placement(calendar.store.settings)
        self._dock_signature = None
        self._last_dock_raise = 0
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMinimumSize(*meeting_bar_minimum(calendar.store.settings))
        self.resize(284, 62)
        self._resize_edge = ""
        self.apply_background()
        THEME["hooks"].append(lambda: (self.apply_background(), self._fit_text()))
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        inner = QFrame(self)
        self.inner = inner
        inner.setObjectName("meetingInner")
        inner.setCursor(Qt.PointingHandCursor)       # a click opens the calendar; the stripe and edges say otherwise
        inner.setMouseTracking(True)
        inner.installEventFilter(self)
        outer.addWidget(inner)
        row = QHBoxLayout(inner)
        self.row = row
        row.setContentsMargins(11, 7, 5, 9)
        row.setSpacing(7)
        self.source_color = QFrame(inner)
        self.source_color.setFixedSize(4, 30)
        self.source_color.setAttribute(Qt.WA_TransparentForMouseEvents)
        row.addWidget(self.source_color, 0, Qt.AlignVCenter)
        labels = QVBoxLayout()
        labels.setSpacing(0)
        self.title = QLabel(inner)
        self.title.setObjectName("meetingTitle")
        self.title.setTextFormat(Qt.PlainText)
        self.title.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.title.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        self.detail = QLabel(inner)
        self.detail.setObjectName("meetingTime")
        self.detail.setAttribute(Qt.WA_TransparentForMouseEvents)
        self.detail.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        labels.addWidget(self.title)
        labels.addWidget(self.detail)
        row.addLayout(labels, 1)
        self.open_button = QToolButton(inner)
        self.open_button.setObjectName("meetingOpen")
        self.open_button.setText("↗")
        self.open_button.setToolTip("Open meeting")
        self.open_button.setCursor(Qt.PointingHandCursor)
        self.open_button.clicked.connect(self.open_event)
        self.grip = QSizeGrip(inner)
        self.grip.setFixedSize(15, 15)
        self.grip.setToolTip("Drag to resize meeting bar")
        self.grip.installEventFilter(self)
        self.glint = MeetingGlint(inner)
        self._glint_preview_until = 0.0
        self._restore_geometry()
        self._ready = True
        self._fit_text()
        self.agenda = CalendarAgenda(self, calendar)
        self.notice = MeetingNotice(bubble)
        self.notice.dismissed.connect(lambda: QTimer.singleShot(0, self.update_meeting))
        calendar.changed.connect(self.update_meeting)
        self.tick = QTimer(self)
        self.tick.setInterval(15000)
        self.tick.timeout.connect(self.update_meeting)
        self.tick.start()

    def _inks(self):
        """Title and detail colours: the theme's, or whatever reads best on a chosen bar colour."""
        raw = QColor(str(self.calendar.store.settings.get("meeting_bar_bg") or ""))
        if not raw.isValid():
            return C["text"], C["dim"]
        k = ink_for(raw)
        return k.name(), f"rgba({k.red()}, {k.green()}, {k.blue()}, 180)"

    def apply_background(self):
        bg = meeting_bar_background(self.calendar.store.settings)
        text, dim = self._inks()
        self.setStyleSheet(f"QFrame#meetingInner {{ background: {bg}; border: 1px solid {C['border']}; "
                           f"border-radius: 12px; }} QLabel#meetingTitle {{ color: {text}; "
                           f"font-size: 13px; font-weight: 700; }} QLabel#meetingTime {{ color: {dim}; "
                           f"font-size: 13px; }} QToolButton#meetingOpen {{ color: {C['accent_text']}; border: none; "
                           "font-size: 15px; padding: 2px; }")
        if hasattr(self, "agenda"):
            self.agenda.apply_background()

    def _restore_floating_geometry(self):
        self.setMinimumSize(*meeting_bar_minimum(self.calendar.store.settings))
        saved = self.calendar.store.settings.get("meeting_bar_geometry")
        if isinstance(saved, list) and len(saved) == 4:
            try:
                x, y, w, h = (int(v) for v in saved)
                old = QRect(x, y, max(1, w), max(1, h))
                screens = QGuiApplication.screens()
                screen = max(screens, key=lambda s: (old.intersected(s.availableGeometry()).width() *
                                                      old.intersected(s.availableGeometry()).height())) if screens else None
                area = (screen or QGuiApplication.primaryScreen()).availableGeometry()
                w, h = min(max(self.minimumWidth(), w), area.width()), min(max(self.minimumHeight(), h), area.height())
                visible = old.intersected(area)
                if visible.width() < 30 or visible.height() < 20:
                    x = max(area.left(), min(x, area.right() - w + 1))
                    y = max(area.top(), min(y, area.bottom() - h + 1))
                self.setGeometry(x, y, w, h)
                return
            except (TypeError, ValueError):
                pass
        area = screen_for(self, self.bubble.geometry().center()).availableGeometry()
        self.move(area.left() + 12, area.bottom() - self.height() - 11)

    def _taskbar_target(self, point=None):
        screens = QGuiApplication.screens()
        saved = self.calendar.store.settings.get("meeting_bar_taskbar_geometry")
        screen = QGuiApplication.screenAt(point) if point is not None else None
        if screen is None and isinstance(saved, list) and saved:
            screen = next((s for s in screens if s.name() == saved[0]), None)
        if screen is None:
            screen = QGuiApplication.screenAt(self.bubble.geometry().center()) or QGuiApplication.primaryScreen()
        strip = meeting_bar_taskbar_strip(screen)
        if strip is None:
            for candidate in screens:
                candidate_strip = meeting_bar_taskbar_strip(candidate)
                if candidate_strip is not None:
                    screen, strip = candidate, candidate_strip
                    break
        return screen, strip

    def _place_on_taskbar(self, point=None):
        screen, strip = self._taskbar_target(point)
        if strip is None or strip.width() < 140:
            self._dock_signature = None
            self._restore_floating_geometry()
            return False
        screen_for(self, screen.geometry().center())
        saved = self.calendar.store.settings.get("meeting_bar_taskbar_geometry")
        same_screen = isinstance(saved, list) and len(saved) == 3 and saved[0] == screen.name()
        preferred_width = meeting_bar_minimum(self.calendar.store.settings)[0]
        try:
            offset = self.x() - strip.left() if point is not None else int(saved[1]) if same_screen else 12
            width = self.width() if point is not None else int(saved[2]) if same_screen else 220
        except (TypeError, ValueError):
            offset, width = 12, 220
        width = min(max(preferred_width, width), strip.width() - 16)
        height = max(32, min(62, strip.height() - 4))
        self.setMinimumSize(min(preferred_width, width), min(meeting_bar_minimum(self.calendar.store.settings)[1], height))
        x = max(strip.left() + 8, min(strip.left() + offset, strip.right() - width - 7))
        y = strip.top() + (strip.height() - height) // 2
        self.setGeometry(x, y, width, height)
        self._dock_signature = (screen.name(), strip.x(), strip.y(), strip.width(), strip.height())
        return True

    def _restore_geometry(self):
        if self.placement == "taskbar" and self._place_on_taskbar():
            return
        self._restore_floating_geometry()

    def reset_position(self, save=True):
        if self.placement == "taskbar":
            self.calendar.store.settings.pop("meeting_bar_taskbar_geometry", None)
            self._place_on_taskbar()
            if save:
                self._save_geometry()
            return
        area = screen_for(self, self.bubble.geometry().center()).availableGeometry()
        self.move(area.left() + 12, area.bottom() - self.height() - 11)
        if save:
            self._save_geometry()

    def set_placement(self, placement, dragged=False):
        if placement not in ("taskbar", "floating") or placement == self.placement:
            return
        if self.placement == "floating":
            g = self._drag_origin_geometry if dragged and self._drag_origin_geometry else self.geometry()
            self.calendar.store.settings["meeting_bar_geometry"] = [g.x(), g.y(), g.width(), g.height()]
        self.placement = placement
        self.calendar.store.settings["meeting_bar_placement"] = placement
        if placement == "taskbar":
            self._place_on_taskbar(self.geometry().center() if dragged else None)
        elif dragged:
            self.setMinimumSize(*meeting_bar_minimum(self.calendar.store.settings))
        else:
            self._restore_floating_geometry()
        self._save_geometry()
        self.placement_changed.emit(placement)

    def sync_taskbar_position(self):
        if self.placement != "taskbar" or self._drag_from is not None:
            return
        screen, strip = self._taskbar_target()
        signature = (screen.name(), strip.x(), strip.y(), strip.width(), strip.height()) if strip else None
        if signature != self._dock_signature:
            self._place_on_taskbar()

    def _finish_user_geometry(self):
        if IS_WIN:
            screen = QGuiApplication.screenAt(self.geometry().center())
            strip = meeting_bar_taskbar_strip(screen)
            if strip and strip.adjusted(0, -8, 0, 8).contains(self.geometry().center()):
                if self.placement != "taskbar":
                    self.set_placement("taskbar", dragged=True)
                    return
            elif self.placement == "taskbar":
                self.set_placement("floating", dragged=True)
                self._keep_floating_visible()
                self._save_geometry()
                return
        if self.placement == "taskbar":
            self._place_on_taskbar(self.geometry().center())
            self._save_geometry()
        else:
            self._keep_floating_visible()
            self._save_geometry()

    def _keep_floating_visible(self):
        screens = QGuiApplication.screens()
        if not screens:
            return
        g = self.geometry()
        screen = max(screens, key=lambda s: g.intersected(s.availableGeometry()).width() *
                     g.intersected(s.availableGeometry()).height())
        area = screen.availableGeometry()
        visible = g.intersected(area)
        if visible.width() < 30 or visible.height() < 20:
            self.move(max(area.left(), min(g.x(), area.right() - g.width() + 1)),
                      max(area.top(), min(g.y(), area.bottom() - g.height() + 1)))

    def set_minimum_size(self):
        if self.placement == "taskbar":
            self._place_on_taskbar()
            self._fit_text()
            self._save_geometry()
            return
        self.setMinimumSize(*meeting_bar_minimum(self.calendar.store.settings))
        self.resize(max(self.width(), self.minimumWidth()), max(self.height(), self.minimumHeight()))
        self._fit_text()
        self._save_geometry()

    def _save_geometry(self):
        if self._ready:
            g = self.geometry()
            if self.placement == "taskbar" and self._dock_signature:
                self.calendar.store.settings["meeting_bar_taskbar_geometry"] = [
                    self._dock_signature[0], g.x() - self._dock_signature[1], g.width()]
            elif self.placement == "floating":
                self.calendar.store.settings["meeting_bar_geometry"] = [g.x(), g.y(), g.width(), g.height()]
            self.calendar.store.save()

    def moveEvent(self, event):
        super().moveEvent(event)
        if self._ready:
            if self.agenda.isVisible():
                self.agenda.place()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self, "glint"):
            self.glint.setGeometry(0, 0, self.width(), self.height())
        if hasattr(self, "grip"):
            self._place_corner_controls()
        if self._ready:
            self._fit_text()
            if self.agenda.isVisible():
                self.agenda.place()

    EDGE_CURSORS = {"move": Qt.SizeAllCursor, "click": Qt.PointingHandCursor, "l": Qt.SizeHorCursor,
                    "r": Qt.SizeHorCursor, "t": Qt.SizeVerCursor, "b": Qt.SizeVerCursor, "lt": Qt.SizeFDiagCursor,
                    "rb": Qt.SizeFDiagCursor, "rt": Qt.SizeBDiagCursor, "lb": Qt.SizeBDiagCursor}

    def zone_at(self, pos):
        """What a press at this point of the bar does: resize from an edge ("l", "r", "t", "b" or a corner), move
        from the colour stripe, or click to open the calendar. Docked on the taskbar the height is fixed."""
        w, h = self.inner.width(), self.inner.height()
        edge = ("l" if pos.x() < 5 else "r" if pos.x() >= w - 6 else "")
        if self.placement == "floating":
            edge += "t" if pos.y() < 4 else "b" if pos.y() >= h - 4 else ""
        if edge:
            return edge
        return "move" if pos.x() <= self.source_color.geometry().right() + 7 else "click"

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self._drag_from = event.globalPosition().toPoint() - self.pos()
            self._drag_start = event.globalPosition().toPoint()
            self._drag_origin_geometry = QRect(self.geometry())
            self._did_drag = False
            zone = self.zone_at(self.inner.mapFromGlobal(self._drag_start))
            self._resize_edge = zone if zone not in ("move", "click") else ""
            self.setFocus(Qt.MouseFocusReason)
            event.accept()
        else:
            super().mousePressEvent(event)

    def eventFilter(self, watched, event):
        if watched is getattr(self, "grip", None) and event.type() == QEvent.MouseButtonRelease:
            QTimer.singleShot(0, self._finish_user_geometry)  # after QSizeGrip finishes its native resize
        if watched is self.inner:
            if event.type() == QEvent.MouseButtonPress and event.button() == Qt.LeftButton:
                self.mousePressEvent(event)
                return True
            if event.type() == QEvent.MouseMove and self._drag_from is not None:
                self.mouseMoveEvent(event)
                return True
            if event.type() == QEvent.MouseMove:
                self.inner.setCursor(self.EDGE_CURSORS[self.zone_at(event.position().toPoint())])
            if event.type() == QEvent.MouseButtonRelease and self._drag_from is not None:
                self.mouseReleaseEvent(event)
                return True
        return super().eventFilter(watched, event)

    def _resize_by(self, delta):
        g = QRect(self._drag_origin_geometry)
        min_w, min_h = self.minimumWidth(), self.minimumHeight()
        if "r" in self._resize_edge:
            g.setRight(max(g.left() + min_w - 1, g.right() + delta.x()))
        if "l" in self._resize_edge:
            g.setLeft(min(g.right() - min_w + 1, g.left() + delta.x()))
        if "b" in self._resize_edge:
            g.setBottom(max(g.top() + min_h - 1, g.bottom() + delta.y()))
        if "t" in self._resize_edge:
            g.setTop(min(g.bottom() - min_h + 1, g.top() + delta.y()))
        self.setGeometry(g)

    def mouseMoveEvent(self, event):
        if self._drag_from is not None and event.buttons() & Qt.LeftButton:
            if (event.globalPosition().toPoint() - self._drag_start).manhattanLength() >= 5:
                self._did_drag = True
            if self._did_drag and self._resize_edge:
                self._resize_by(event.globalPosition().toPoint() - self._drag_start)
            elif self._did_drag:
                self.move(event.globalPosition().toPoint() - self._drag_from)
            event.accept()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        was_click = (event.button() == Qt.LeftButton and self._drag_from is not None and not self._did_drag
                     and not self._resize_edge)
        was_drag = self._did_drag
        self._drag_from = None
        self._drag_start = None
        self._did_drag = False
        self._resize_edge = ""
        if was_drag:
            self._finish_user_geometry()
        elif was_click:
            self.agenda.toggle()
        self._drag_origin_geometry = None
        super().mouseReleaseEvent(event)

    def keyPressEvent(self, event):
        arrows = {Qt.Key_Left: (-10, 0), Qt.Key_Right: (10, 0),
                  Qt.Key_Up: (0, -10), Qt.Key_Down: (0, 10)}
        if event.key() in arrows and event.modifiers() & Qt.AltModifier:
            dx, dy = arrows[event.key()]
            if event.modifiers() & Qt.ShiftModifier:
                self.resize(max(self.minimumWidth(), self.width() + dx),
                            max(self.minimumHeight(), self.height() + dy))
            else:
                self.move(self.pos() + QPoint(dx, dy))
            self._finish_user_geometry()
            event.accept()
        else:
            super().keyPressEvent(event)

    def contextMenuEvent(self, event):
        menu = QMenu(self)
        menu.addAction("Calendar settings", self.open_settings)
        menu.addAction("Float above taskbar" if self.placement == "taskbar" else "Place on taskbar",
                       lambda: self.set_placement("floating" if self.placement == "taskbar" else "taskbar"))
        menu.addAction("Reset bar position", self.reset_position)
        menu.exec(event.globalPos())

    def open_event(self):
        if self.current_event and self.current_event.get("url"):
            QDesktopServices.openUrl(QUrl(self.current_event["url"]))

    def set_fullscreen_suppressed(self, suppressed):
        if self.fullscreen_suppressed != suppressed:
            self.fullscreen_suppressed = suppressed
            if suppressed:
                self.agenda.hide()
                self.notice.suspend()
            self.update_meeting()

    def preview_glint(self):
        self._glint_preview_until = time.monotonic() + 6.0
        self.update_meeting()
        QTimer.singleShot(6200, self.update_meeting)

    def wants_visible(self):
        return (self.calendar.connected and self.calendar.store.settings.get("meeting_bar_show", True)
                and not self.fullscreen_suppressed)

    def _fit_text(self):
        tiny = self.width() < 160 or self.height() < 38
        compact = tiny or self.width() < 260 or self.height() < 52
        self.row.setContentsMargins(5 if tiny else 7 if compact else 10,
                                    1 if tiny else 2 if compact else 5,
                                    1 if tiny else 2 if compact else 4,
                                    1 if tiny else 2 if compact else 6)
        self.row.setSpacing(2 if tiny else 3 if compact else 6)
        self.source_color.setFixedSize(3 if compact else 4,
                                       min(34, max(18, self.height() - (8 if compact else 14))))
        self.grip.setFixedSize(12 if tiny else 15, 12 if tiny else 15)
        self.open_button.setFixedSize(13 if tiny else 17 if compact else 20,
                                      13 if tiny else 17 if compact else 20)
        self._place_corner_controls()
        font_size = 11 if tiny else 12 if compact else 13
        text, dim = self._inks()
        self.title.setStyleSheet(f"color: {text}; font-size: {font_size}px; font-weight: 700;")
        self.detail.setStyleSheet(f"color: {dim}; font-size: {font_size}px;")
        QTimer.singleShot(0, self._update_title)

    def _place_corner_controls(self):
        self.grip.move(max(0, self.width() - self.grip.width() - 4),
                       max(0, self.height() - self.grip.height() - 3))
        self.open_button.move(max(0, self.grip.x() - self.open_button.width() - 3),
                              max(0, self.height() - self.open_button.height() - 3))
        self.open_button.raise_()
        self.grip.raise_()

    def _set_stripe(self, color):
        tone = QColor(color)
        if getattr(self, "_stripe_color", None) == tone.name():
            return
        self._stripe_color = tone.name()
        self.source_color.setStyleSheet(
            "QFrame { background: qlineargradient(x1:0, y1:0, x2:0, y2:1, "
            f"stop:0 {tone.lighter(125).name()}, stop:0.5 {tone.name()}, "
            f"stop:1 {tone.darker(120).name()}); border-radius: 2px; }}")

    def _update_title(self):
        margins = self.row.contentsMargins()
        width = (self.width() - margins.left() - margins.right() - self.source_color.width() -
                 self.row.spacing() - 2)
        width = max(1, width)
        title = (self.current_event["title"] if self.current_event else
                 "Checking calendar..." if self.calendar.busy else
                 ("No upcoming events" if self.width() >= 260 else "No events"))
        self.title.setText(self.title.fontMetrics().elidedText(title, Qt.ElideRight, width))
        detail = getattr(self, "_detail_text", "")
        controls_width = self.grip.width() + 4
        if not self.open_button.isHidden():
            controls_width += self.open_button.width() + 3
        self.detail.setText(self.detail.fontMetrics().elidedText(
            detail, Qt.ElideRight, max(1, width - controls_width)))

    def _notify_meetings(self, now):
        """One visible cue at a time. A later stage of that event replaces the earlier cue."""
        if self.fullscreen_suppressed or not self.bubble.isVisible():
            self.notice.suspend()
            return
        self.notice.resume()
        if self.notice.isVisible():
            self.notice.place()
        settings = self.calendar.store.settings
        thresholds = calendar_alert_minutes(settings)
        sent = settings.get("calendar_notice_sent") or []
        if not isinstance(sent, list):
            sent = []
        sent_set = set(sent)
        candidates = []
        events = {((e.get("series_key") or e.get("id") or e.get("title", "")), e["start"].isoformat()): e
                  for e in self.calendar.recent_events + self.calendar.events}
        if self.notice.current_stamp:
            for event in events.values():
                stamp = f"{event.get('series_key') or event.get('id') or event.get('title', '')}|{event['start'].isoformat()}"
                if stamp == self.notice.current_stamp:
                    self.notice.refresh_time(now, event)
                    break
        for event in events.values():
            event_id = event.get("series_key") or event.get("id") or event.get("title", "")
            stamp = f"{event_id}|{event['start'].isoformat()}"
            start_s = (event["start"] - now).total_seconds()
            end_s = (event["end"] - now).total_seconds()
            if start_s > 0 and thresholds and start_s <= max(thresholds) * 60:
                due = [n for n in thresholds if start_s <= n * 60]
                keys = [hashlib.sha256(f"{stamp}|{n}".encode()).hexdigest()[:20] for n in due]
                pending = [key for key in keys if key not in sent_set]
                if pending:
                    left = max(1, math.ceil(start_s / 60))
                    if left <= 5:
                        stage, emoji, tone = "lead_urgent", "🔔", "#ff9b69"
                    elif left <= 15:
                        stage, emoji, tone = "lead_near", "⏳", "#f3c16e"
                    else:
                        stage, emoji, tone = "lead_calm", "🗓️", C["accent"]
                    heading = f"IN {left} MIN"
                    candidates.append((1000 - min(due), event["start"], stamp, pending, stage, heading,
                                       event, meeting_cue_copy(stage, left, stamp), emoji, tone))
            during = settings.get("calendar_cues_during", False)
            if during and 0 <= -start_s < 120 and end_s > 0:
                start_key = hashlib.sha256(f"{stamp}|start".encode()).hexdigest()[:20]
                if start_key not in sent_set:
                    candidates.append((1000, event["start"], stamp, [start_key], "started", "STARTED", event,
                                       meeting_cue_copy("started", 0, stamp), "🤫", "#ff9b69"))
            midpoint = event["start"] + (event["end"] - event["start"]) / 2
            half_s = (now - midpoint).total_seconds()
            if during and 0 <= half_s < 120 and end_s > 0:
                half_key = hashlib.sha256(f"{stamp}|half".encode()).hexdigest()[:20]
                if half_key not in sent_set:
                    left = max(1, math.ceil(end_s / 60))
                    prior = hashlib.sha256(f"{stamp}|start".encode()).hexdigest()[:20]
                    candidates.append((1100, event["start"], stamp, [prior, half_key], "halfway", "HALFWAY", event,
                                       meeting_cue_copy("halfway", left, stamp), "🕒", "#78c9d6"))
            if 0 <= -end_s < 180:
                finish_key = hashlib.sha256(f"{stamp}|finish".encode()).hexdigest()[:20]
                if finish_key not in sent_set:
                    prior = [hashlib.sha256(f"{stamp}|{stage}".encode()).hexdigest()[:20]
                             for stage in ("start", "half")]
                    candidates.append((1200, event["start"], stamp, prior + [finish_key], "finished", "ENDED", event,
                                       meeting_cue_copy("finished", 0, stamp), "🌤️", "#8bd3a5"))
        if not candidates:
            return
        current = self.notice.current_stamp
        if current:
            newer = [c for c in candidates if c[2] == current and c[0] > self.notice.rank]
            if not newer:
                return
            choice = max(newer, key=lambda c: (c[0], -c[1].timestamp()))
        else:
            choice = max(candidates, key=lambda c: (c[0], -c[1].timestamp()))
        rank, _start, stamp, keys, stage, heading, event, body, emoji, tone = choice
        sent.extend(keys)
        settings["calendar_notice_sent"] = list(dict.fromkeys(sent))[-400:]
        self.calendar.store.save()
        self.bubble.hop()
        self.notice.show_notice(stamp, rank, stage, heading, event, body, emoji, tone)

    def update_meeting(self):
        if not self.wants_visible():
            self.glint.set_active(False)
            self.notice.suspend() if self.fullscreen_suppressed else self.notice.clear()
            self.agenda.hide()
            self.hide()
            return
        now = datetime.now().astimezone()
        future = [e for e in self.calendar.events if e["start"] > now and e["end"] > now]
        current = next((e for e in self.calendar.events if e["start"] <= now < e["end"]), None)
        self.current_event = current or (future[0] if future else None)
        if self.current_event:
            e = self.current_event
            color = calendar_color(e.get("event_color"), calendar_color(e.get("calendar_color")))
            self._set_stripe(color)
            minutes = math.ceil((e["start"] - now).total_seconds() / 60)
            if minutes <= 0:
                left = max(0, math.ceil((e["end"] - now).total_seconds() / 60))
                detail = f"Now · {left} min left"
            elif minutes < 60:
                detail = f"In {minutes} min · {e['start']:%I:%M %p}".replace(" 0", " ")
            elif minutes < 1440:
                detail = f"In {minutes // 60}h {minutes % 60}m · {e['start']:%I:%M %p}".replace(" 0", " ")
            else:
                detail = f"In {short_span(minutes * 60)} · {e['start']:%a %I:%M %p}".replace(" 0", " ")
            self._detail_text = detail
            self.open_button.setVisible(bool(e.get("url")))
            self._update_title()
            self.setToolTip(f"{e['title']}\n{e.get('calendar_name') or 'Calendar'} · "
                            f"{e['start']:%a, %b %d at %I:%M %p}\nClick for calendar. Drag to move.")
            self.open_button.setToolTip("Join meeting" if e.get("join") else "Open calendar event")
            urgent = any(0 < (next_event["start"] - now).total_seconds() <=
                         calendar_flow_minutes(self.calendar.store.settings) * 60 for next_event in future)
            preview = time.monotonic() < self._glint_preview_until
            self.glint.set_active(urgent or preview, meeting_glint_style(self.calendar.store.settings))
        else:
            self._set_stripe(C["dim"])
            self._detail_text = "Loading next event" if self.calendar.busy else "Calendar is clear for now"
            self.open_button.hide()
            self._update_title()
            self.setToolTip("No timed events in the next 14 days. Click for calendar. Drag to move.")
            self.glint.set_active(time.monotonic() < self._glint_preview_until,
                                  meeting_glint_style(self.calendar.store.settings))
        first_show = not self.isVisible()
        if first_show:
            self.show()
            apply_share_privacy(self)
        self.glint.raise_()
        self.open_button.raise_()
        self.grip.raise_()
        if first_show:
            QTimer.singleShot(0, self._update_title)
        self._notify_meetings(now)


class SettingsWindow(QWidget):
    """All settings in one window: groups on the left, each page grouped into cards with switches, sliders,
    segmented choices and previews. Every change applies at once (no OK button). `ctx` carries the callbacks
    from main() (set_setting, set_look, set_opacity, ...), so the window holds no app logic of its own."""
    PAGES = [("appearance", "\U0001F3A8", "Appearance"), ("focus", "⏱️", "Focus & breaks"),
             ("checkins", "\U0001F4AC", "Check-ins"), ("sound", "\U0001F3A7", "Sound & peeks"),
             ("calendar", "\U0001F4C5", "Calendar"),
             ("flags", "\U0001F6A9", "Flags"), ("controls", "⌨️", "Controls"),
             ("privacy", "\U0001F512", "Privacy & data"), ("about", "ℹ️", "About")]

    push_result = Signal(bool, str)

    def __init__(self, ctx):
        super().__init__(None, Qt.Window)
        self.ctx = ctx
        ctx.calendar.changed.connect(self._calendar_changed)
        self.push_result.connect(lambda ok, info: self.push_status.setText(
            "\u2713 Sent. If it only shows inside the ntfy app, allow ntfy notifications on your phone." if ok
            else f"\u2717 Couldn't reach ntfy.sh. Check your internet. ({info[:60]})"))
        self.setObjectName("settingsRoot")
        self.setAttribute(Qt.WA_AlwaysShowToolTips)
        self.setAttribute(Qt.WA_StyledBackground, True)
        self.setWindowTitle(f"{APP_NAME}: settings")
        self.setWindowIcon(app_icon())
        self.setStyleSheet(STYLE + SETTINGS_STYLE)
        self.resize(720, 560)
        self.setMinimumSize(600, 420)
        h = QHBoxLayout(self)
        h.setContentsMargins(0, 0, 0, 0)
        h.setSpacing(0)
        self.side = QListWidget(self)
        self.side.setObjectName("side")
        self.side.setFixedWidth(180)
        self.side.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.stack = QStackedWidget(self)
        h.addWidget(self.side)
        h.addWidget(self.stack, 1)
        self.builders = {}
        for key, icon, label in self.PAGES:
            it = QListWidgetItem(f"{icon}   {label}")
            it.setToolTip(label)
            it.setData(Qt.UserRole, key)
            self.side.addItem(it)
            holder = QWidget(self.stack)
            QVBoxLayout(holder).setContentsMargins(0, 0, 0, 0)
            self.stack.addWidget(holder)
        self.side.currentRowChanged.connect(self._show_page)
        QShortcut(QKeySequence("Escape"), self, self.close)

    # ---- small builders
    def _s(self, k, d):
        return self.ctx.setting(k, d)

    def _set(self, k, v):
        self.ctx.set_setting(k, v)

    def _page(self, title, sub):
        area = QScrollArea()
        area.setObjectName("page")
        area.setWidgetResizable(True)
        area.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        body = QWidget()
        body.setObjectName("pageBody")
        v = QVBoxLayout(body)
        v.setContentsMargins(24, 20, 24, 24)
        v.setSpacing(8)
        t = QLabel(title, body)
        t.setObjectName("pageTitle")
        s = QLabel(sub, body)
        s.setObjectName("pageSub")
        s.setWordWrap(True)
        v.addWidget(t)
        v.addWidget(s)
        area.setWidget(body)
        return area, v

    def _group(self, v, title=None):
        if title:
            lab = QLabel(title.upper())
            lab.setObjectName("section")
            v.addWidget(lab)
        g = QFrame()
        g.setObjectName("group")
        gl = QVBoxLayout(g)
        gl.setContentsMargins(14, 8, 14, 8)
        gl.setSpacing(2)
        v.addWidget(g)
        return gl

    def _fold_group(self, v, title, summary):
        """A group that starts folded to one line; click or Space opens it. For rarely changed settings."""
        head = QToolButton()
        head.setObjectName("fold")
        head.setCheckable(True)
        head.setToolButtonStyle(Qt.ToolButtonTextOnly)
        head.setCursor(Qt.PointingHandCursor)
        head.setAccessibleName(title)
        v.addWidget(head)
        gl = self._group(v)
        frame = gl.parentWidget()
        frame.setVisible(False)

        def fold(on):
            head.setText(("\u25BE  " if on else "\u25B8  ") + title.upper() + ("" if on else f"   {summary}"))
            frame.setVisible(on)
        head.toggled.connect(fold)
        fold(False)
        self.fold_heads = getattr(self, "fold_heads", {})
        self.fold_heads[title] = head
        return gl

    def _row(self, gl, title, desc, control=None, stretch_control=False):
        w = QWidget()
        hl = QHBoxLayout(w)
        hl.setContentsMargins(0, 6, 0, 6)
        hl.setSpacing(12)
        tv = QVBoxLayout()
        tv.setSpacing(1)
        t = QLabel(title, w)
        t.setObjectName("rowTitle")
        tv.addWidget(t)
        if desc:
            d = QLabel(desc, w)
            d.setObjectName("rowDesc")
            d.setWordWrap(True)
            tv.addWidget(d)
        hl.addLayout(tv, 1)
        if control is not None:
            control.setParent(w)
            hl.addWidget(control, 1 if stretch_control else 0, Qt.AlignVCenter | Qt.AlignRight)
        gl.addWidget(w)
        return w

    def _toggle(self, gl, title, desc, key, default, on_change=None):
        sw = ToggleSwitch(self._s(key, default))

        def changed(on):
            self._set(key, on)
            if on_change:
                on_change(on)
        sw.toggled.connect(changed)
        self._row(gl, title, desc, sw)
        return sw

    def _slider(self, gl, title, desc, lo, hi, value, fmt, on_change, step=1):
        box = QWidget()
        bl = QHBoxLayout(box)
        bl.setContentsMargins(0, 0, 0, 0)
        bl.setSpacing(8)
        sl = NoWheelSlider(Qt.Horizontal, box)
        sl.setRange(lo, hi)
        sl.setSingleStep(step)
        sl.setPageStep(step * 5)
        sl.setValue(int(value))
        sl.setFixedWidth(170)
        val = QLabel(fmt(int(value)), box)
        val.setObjectName("value")
        sl.valueChanged.connect(lambda x: (val.setText(fmt(x)), on_change(x)))
        bl.addWidget(sl)
        bl.addWidget(val)
        self._row(gl, title, desc, box)
        return sl

    def _seg(self, gl, title, desc, options, current, on_change, stacked=False):
        sg = Segmented(options, current)
        sg.changed.connect(on_change)
        if stacked:
            wrap = QWidget()
            v = QVBoxLayout(wrap)
            v.setContentsMargins(0, 6, 0, 6)
            v.setSpacing(4)
            label = QLabel(title, wrap)
            label.setObjectName("rowTitle")
            v.addWidget(label)
            if desc:
                detail = QLabel(desc, wrap)
                detail.setObjectName("rowDesc")
                detail.setWordWrap(True)
                v.addWidget(detail)
            v.addWidget(sg, 0, Qt.AlignLeft)
            gl.addWidget(wrap)
        else:
            self._row(gl, title, desc, sg)
        return sg

    def _button(self, text, fn):
        b = QPushButton(text)
        b.setObjectName("act")
        b.setCursor(Qt.PointingHandCursor)
        b.clicked.connect(fn)
        return b

    # ---- pages (built the first time they're shown, and again each time the window opens)
    def open_at(self, key="appearance"):
        self.calendar_status = None
        for i in range(self.stack.count()):
            self._clear(self.stack.widget(i))
        self.builders = {}
        row = next((i for i, p in enumerate(self.PAGES) if p[0] == key), 0)
        if self.side.currentRow() == row:
            self._show_page(row)
        self.side.setCurrentRow(row)
        if not self.isVisible():
            self.place()
        self.show()
        apply_share_privacy(self)
        self.raise_()
        self.activateWindow()

    def place(self):
        """On the circle's screen, in the biggest free space beside the circle and the full list (never on top
        of them), sized to fit; centred on the screen only when there's no room anywhere else."""
        b = self.ctx.bubble.frameGeometry()
        screen = screen_for(self, b.center())
        a = screen.availableGeometry().adjusted(12, 12, -12, -12)
        avoid = b
        pnl = self.ctx.panel
        if pnl.isVisible() and screen.geometry().intersects(pnl.frameGeometry()):
            avoid = avoid.united(pnl.frameGeometry())
        w, h = 720, min(560, a.height())
        left = avoid.left() - 16 - a.left()
        right = a.right() - avoid.right() - 16
        room, side = max((left, "left"), (right, "right"))
        if room >= 600:
            w = min(w, room)
            x = (a.left() + (left - w) // 2) if side == "left" else (avoid.right() + 16 + (right - w) // 2)
        else:
            w = min(w, a.width())
            x = a.center().x() - w // 2
        self.resize(w, h)
        self.move(x, a.center().y() - h // 2)

    @staticmethod
    def _clear(holder):
        lay = holder.layout()
        while lay.count():
            w = lay.takeAt(0).widget()
            if w:
                w.hide()
                w.deleteLater()

    def _show_page(self, row):
        if row < 0:
            return
        key = self.PAGES[row][0]
        holder = self.stack.widget(row)
        if key not in self.builders:
            self._clear(holder)
            area = getattr(self, "page_" + key)()
            holder.layout().addWidget(area)
            self.builders[key] = area
        self.stack.setCurrentIndex(row)

    def _calendar_changed(self):
        if getattr(self, "calendar_status", None) is not None:
            self.calendar_status.setText(self.ctx.calendar.status)
        cal = self.ctx.calendar
        signature = (len(cal.calendars), tuple((i["id"], i["name"], i.get("color"),
                                              i.get("enabled", True)) for i in cal.feed_items),
                     len(self._s("google_calendar_hidden_series", [])))
        changed_layout = (cal.connected != getattr(self, "_calendar_page_connected", cal.connected) or
                          signature != getattr(self, "_calendar_page_count", signature))
        if changed_layout and self.side.currentRow() == next(i for i, p in enumerate(self.PAGES) if p[0] == "calendar"):
            QTimer.singleShot(0, self._rebuild_calendar)

    def _rebuild_calendar(self):
        row = next(i for i, p in enumerate(self.PAGES) if p[0] == "calendar")
        if self.side.currentRow() != row or "calendar" not in self.builders:
            return
        holder = self.stack.widget(row)
        self.calendar_status = None
        self._clear(holder)
        area = self.page_calendar()
        holder.layout().addWidget(area)
        self.builders["calendar"] = area

    def _choose_calendar_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Google Desktop app credentials", "", "JSON files (*.json)")
        if path:
            self.ctx.calendar.connect_file(path)

    def _rename_calendar_feed(self, item):
        name = ask(self, "Rename calendar", item["name"])
        if name:
            self.ctx.calendar.set_feed_name(item["id"], name)
            QTimer.singleShot(0, self._rebuild_calendar)

    def _color_calendar_feed(self, item):
        color = QColorDialog.getColor(QColor(calendar_color(item.get("color"))), self,
                                      "Fallback color")
        if color.isValid():
            self.ctx.calendar.set_feed_color(item["id"], color.name())
            QTimer.singleShot(0, self._rebuild_calendar)

    def page_calendar(self):
        cal = self.ctx.calendar
        meeting_bar = getattr(self.ctx, "meeting_bar", None)
        self._calendar_page_connected = cal.connected
        self._calendar_page_count = (len(cal.calendars), tuple((i["id"], i["name"], i.get("color"),
                                                              i.get("enabled", True)) for i in cal.feed_items),
                                     len(self._s("google_calendar_hidden_series", [])))
        area, v = self._page("Google Calendar", "Click the floating bar for a three-day, 24-hour view of your events. "
                             "A private link covers one calendar. Google sign-in also reads event colors.")
        gl = self._group(v, "Connection")
        self.calendar_status = QLabel(cal.status)
        self.calendar_status.setObjectName("rowDesc")
        self.calendar_status.setWordWrap(True)
        gl.addWidget(self.calendar_status)
        if not cal.connected:
            self.feed_input = QLineEdit()
            self.feed_input.setEchoMode(QLineEdit.Password)
            self.feed_input.setPlaceholderText("Paste your private iCal link")
            self.feed_input.setAccessibleName("Private Google Calendar iCal link")
            self.feed_input.returnPressed.connect(lambda: cal.connect_feed(self.feed_input.text()))
            self._row(gl, "Private calendar link", "In Google Calendar: Settings > your calendar > "
                      "Integrate calendar > Secret address in iCal format.", self.feed_input, True)
            self._row(gl, "Connect calendar", "Paste the link above, then connect. No developer credentials needed.",
                      self._button("Connect", lambda: cal.connect_feed(self.feed_input.text())))
            self._row(gl, "Find your link", "Open Google Calendar settings in your browser.",
                      self._button("Open Google Calendar", lambda: QDesktopServices.openUrl(
                          QUrl("https://calendar.google.com/calendar/u/0/r/settings"))))
            advanced_toggle = QPushButton("▸  Advanced Google sign-in")
            advanced_toggle.setObjectName("act")
            advanced_toggle.setCheckable(True)
            advanced_toggle.setToolTip("Requires a Google Cloud Desktop OAuth client")
            v.addWidget(advanced_toggle)
            advanced_frame = QFrame()
            advanced_frame.setObjectName("group")
            advanced = QVBoxLayout(advanced_frame)
            advanced.setContentsMargins(14, 8, 14, 8)
            v.addWidget(advanced_frame)
            advanced_frame.hide()
            advanced_toggle.toggled.connect(lambda on: (
                advanced_frame.setVisible(on),
                advanced_toggle.setText(("▾" if on else "▸") + "  Advanced Google sign-in")))
            self._row(advanced, "Desktop OAuth", "For a Google Cloud Desktop app you've set up. "
                      "Choose its credentials JSON to sign in through your browser.",
                      self._button("Choose OAuth JSON...", self._choose_calendar_file))
        else:
            self._row(gl, "Events", "PTT checks every five minutes. Google's private feed may update later.",
                      self._button("Refresh now", cal.refresh))
            self._row(gl, "Connection", "Remove this computer's saved calendar connection.",
                      self._button("Disconnect", cal.disconnect))
            if cal.feed_connected:
                choices = self._group(v, "Calendars to show")
                hint = QLabel("This link cannot list your other Google calendars or reliably read "
                              "individual event colors. Add one link per calendar. For automatic choices "
                              "and exact colors, disconnect and use Advanced Google sign-in.")
                hint.setObjectName("rowDesc")
                hint.setWordWrap(True)
                choices.addWidget(hint)
                for item in cal.feed_items:
                    row = QWidget()
                    line = QHBoxLayout(row)
                    line.setContentsMargins(0, 2, 0, 2)
                    line.setSpacing(6)
                    box = QCheckBox(item["name"])
                    box.setChecked(item.get("enabled", True))
                    box.setAccessibleName("Show " + item["name"])
                    box.toggled.connect(lambda on, id=item["id"]: cal.set_feed_enabled(id, on))
                    line.addWidget(box, 1)
                    color = self._button("Fallback color", lambda _=False, i=item: self._color_calendar_feed(i))
                    color.setToolTip("Color used when this link has no event color for " + item["name"])
                    color.setAccessibleName("Change fallback color for " + item["name"])
                    color.setStyleSheet(f"border-left: 8px solid {calendar_color(item.get('color'))};")
                    line.addWidget(color)
                    line.addWidget(self._button("Rename", lambda _=False, i=item: self._rename_calendar_feed(i)))
                    line.addWidget(self._button("Remove", lambda _=False, id=item["id"]: cal.remove_feed(id)))
                    choices.addWidget(row)
                self.feed_input = QLineEdit()
                self.feed_input.setEchoMode(QLineEdit.Password)
                self.feed_input.setPlaceholderText("Paste another private iCal link")
                self.feed_input.setAccessibleName("Another private Google Calendar iCal link")
                self.feed_input.returnPressed.connect(lambda: cal.connect_feed(self.feed_input.text()))
                self._row(choices, "Add a calendar", "Its link stays private on this Windows account.",
                          self.feed_input, True)
                choices.addWidget(self._button("Add calendar", lambda: cal.connect_feed(self.feed_input.text())))
            elif cal.calendars:
                choices = self._group(v, "Calendars to show")
                selected = self._s("google_calendar_selected", None)
                boxes = []
                for item in cal.calendars:
                    name = str(item.get("summaryOverride") or item.get("summary") or "Calendar")
                    line = QWidget()
                    row = QHBoxLayout(line)
                    row.setContentsMargins(0, 2, 0, 2)
                    stripe = QFrame(line)
                    stripe.setFixedSize(8, 22)
                    stripe.setStyleSheet(f"background: {calendar_color(item.get('backgroundColor'))}; border-radius: 4px;")
                    row.addWidget(stripe)
                    box = QCheckBox(name)
                    box.setProperty("calendar_id", item["id"])
                    box.setChecked(item.get("selected", True) if selected is None else item["id"] in selected)
                    boxes.append(box)
                    row.addWidget(box, 1)
                    choices.addWidget(line)
                for box in boxes:
                    box.toggled.connect(lambda _=False, bs=boxes: cal.choose_calendars(
                        [b.property("calendar_id") for b in bs if b.isChecked()]))
            hidden_count = len(self._s("google_calendar_hidden_series", []))
            if hidden_count:
                self._row(v, "Hidden event series",
                          f"{hidden_count} hidden in PTT. Google Calendar is unchanged.",
                          self._button("Show all", cal.show_hidden_event_series))
        bar_group = self._group(v, "Meeting bar")
        self._toggle(bar_group, "Show bar", "Keep the next event visible. The bar hides during full screen.",
                     "meeting_bar_show", True, lambda _: meeting_bar.update_meeting() if meeting_bar else None)
        placement_control = self._seg(
            bar_group, "Placement", "On the taskbar by default, or free on the desktop.",
            [("taskbar", "Taskbar"), ("floating", "Floating")],
            meeting_bar_placement(self.ctx.store.settings),
            lambda mode: meeting_bar.set_placement(mode) if meeting_bar else self._set("meeting_bar_placement", mode))
        if meeting_bar:
            meeting_bar.placement_changed.connect(placement_control.set_value)
        alert_values = calendar_alert_minutes(self.ctx.store.settings)[:3]
        alert_values += [0] * (3 - len(alert_values))
        alert_box = QWidget()
        alert_row = QHBoxLayout(alert_box)
        alert_row.setContentsMargins(0, 0, 0, 0)
        alert_row.setSpacing(5)
        alert_spins = []
        for value in alert_values:
            spin = QSpinBox(alert_box)
            spin.setRange(0, 240)
            spin.setSuffix(" min")
            spin.setSpecialValueText("Off")
            spin.setValue(value)
            spin.setFixedWidth(81)
            spin.setAccessibleName(f"Heads-up {len(alert_spins) + 1}, minutes before")
            alert_row.addWidget(spin)
            alert_spins.append(spin)

        def save_alerts(_=None):
            self._set("calendar_alert_minutes", [spin.value() for spin in alert_spins])
            if meeting_bar:
                meeting_bar.update_meeting()
        for spin in alert_spins:
            spin.valueChanged.connect(save_alerts)
        self._row(bar_group, "Heads-ups", "A meeting card stays by the cloud until you press Got it or Esc. "
                  "Set a slot to Off to skip it.", alert_box)
        self._toggle(bar_group, "Cards during meetings", "Also show a card when a meeting starts and at halfway.",
                     "calendar_cues_during", False)
        start_hour = QComboBox()
        start_hour.addItem("Around now", -1)
        for hour in range(24):
            start_hour.addItem(datetime(2000, 1, 1, hour).strftime("%I:%M %p").lstrip("0"), hour)
        start_hour.setMaxVisibleItems(12)
        start_hour.setCurrentIndex(max(0, start_hour.findData(self._s("agenda_start_hour", -1))))
        start_hour.setAccessibleName("Calendar view opens at")
        start_hour.currentIndexChanged.connect(lambda _: self._set("agenda_start_hour", start_hour.currentData()))
        self._row(bar_group, "Calendar opens at", "The hour the calendar view scrolls to when it opens. "
                  "The rest of the day is a scroll away.", start_hour)
        bar_group = self._fold_group(v, "Bar appearance", "Glint, size, position and color")
        self._seg(bar_group, "Bar glint", "Slanted light crosses the whole bar when a meeting is close.",
                  [("off", "Off"), ("sun", "Sun glint"), ("triple", "Triple glint"),
                   ("prism", "Prism")], meeting_glint_style(self.ctx.store.settings),
                  lambda key: (self._set("meeting_glint_style", key),
                               meeting_bar.preview_glint() if meeting_bar and key != "off" else
                               meeting_bar.update_meeting() if meeting_bar else None), stacked=True)
        urgent = QSpinBox()
        urgent.setRange(1, 60)
        urgent.setSuffix(" min")
        urgent.setValue(calendar_flow_minutes(self.ctx.store.settings))
        urgent.setAccessibleName("Start meeting bar glint when event is this many minutes away")
        urgent.valueChanged.connect(lambda n: (self._set("calendar_urgent_minutes", n),
                                               meeting_bar.update_meeting() if meeting_bar else None))
        self._row(bar_group, "Glint starts", "The shine begins this many minutes before a meeting.", urgent)
        self._row(bar_group, "Preview", "See the selected glint on the bar for six seconds.",
                  self._button("Preview glint", meeting_bar.preview_glint if meeting_bar else lambda: None))
        self._row(bar_group, "Position", "Drag the color stripe to move it; drag across the taskbar edge to switch placement. "
                  "Drag an edge to resize. Alt + arrows move it, Alt + Shift + arrows resize it.",
                  self._button("Reset position", meeting_bar.reset_position if meeting_bar else lambda: None))
        minimum_box = QWidget()
        minimum_row = QHBoxLayout(minimum_box)
        minimum_row.setContentsMargins(0, 0, 0, 0)
        minimum_row.setSpacing(6)
        min_width, min_height = meeting_bar_minimum(self.ctx.store.settings)
        for label, key, value, low, high in (("Width", "meeting_bar_min_width", min_width, 120, 600),
                                             ("Height", "meeting_bar_min_height", min_height, 32, 180)):
            minimum_row.addWidget(QLabel(label, minimum_box))
            spin = QSpinBox(minimum_box)
            spin.setRange(low, high)
            spin.setSuffix(" px")
            spin.setValue(value)
            spin.setFixedWidth(82)
            spin.setAccessibleName("Minimum meeting bar " + label.lower())
            spin.valueChanged.connect(lambda n, k=key: (self._set(k, n),
                                       meeting_bar.set_minimum_size() if meeting_bar else None))
            minimum_row.addWidget(spin)
        self._row(bar_group, "Minimum size", "Choose its minimum size. On the taskbar, height fits the taskbar.",
                  minimum_box)
        background_controls = QWidget()
        background_row = QHBoxLayout(background_controls)
        background_row.setContentsMargins(0, 0, 0, 0)
        background_row.setSpacing(5)
        color_button = self._button("Choose color", lambda: None)
        color_button.setStyleSheet(f"border-left: 8px solid {meeting_bar_background(self.ctx.store.settings)};")

        def set_bar_color(color):
            self._set("meeting_bar_bg", color)
            color_button.setStyleSheet(f"border-left: 8px solid {meeting_bar_background(self.ctx.store.settings)};")
            if meeting_bar:
                meeting_bar.apply_background()

        def choose_bar_color():
            picked = QColorDialog.getColor(QColor(meeting_bar_background(self.ctx.store.settings)), self,
                                           "Meeting bar background")
            if picked.isValid():
                set_bar_color(picked.name())
        color_button.clicked.disconnect()
        color_button.clicked.connect(choose_bar_color)
        background_row.addWidget(color_button)
        background_row.addWidget(self._button("Default", lambda: set_bar_color("")))
        self._row(bar_group, "Background color", "Choose a shade that blends with your desktop. "
                  "Event-color stripes stay the same.", background_controls)
        v.addStretch(1)
        return area

    def page_appearance(self):
        ctx, b = self.ctx, self.ctx.bubble
        area, v = self._page("Appearance", "How the circle and the windows look. Changes show right away.")
        top = QHBoxLayout()
        self.big = QLabel()
        self.big.setFixedSize(96, 96)
        self.big.setAlignment(Qt.AlignCenter)
        self.big.setStyleSheet(f"background: {C['field']}; border: 1px solid {C['border']}; border-radius: 12px;")
        cap = QLabel("This is your circle.\nPick a color, a shape and a size.")
        cap.setObjectName("rowDesc")
        top.addWidget(self.big)
        top.addSpacing(12)
        top.addWidget(cap, 1)
        v.addLayout(top)

        gl = self._group(v, "Theme")
        self._seg(gl, "Light or dark", "System follows the Windows setting.",
                  [("system", "System"), ("light", "Light"), ("dark", "Dark")], self._s("theme", "system"),
                  ctx.set_theme, stacked=True)
        THEME["hooks"].append(lambda: (refresh_big(), refresh_shapes()))   # the circle previews are pictures

        def refresh_big():
            self.big.setPixmap(bubble_preview(b).scaled(72, 72, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        refresh_big()

        gl = self._group(v, "Color")
        roww = QWidget()
        rl = QHBoxLayout(roww)
        rl.setContentsMargins(0, 6, 0, 6)
        rl.setSpacing(4)
        grp = QButtonGroup(roww)
        looks = [("auto", ("Auto: white on dark, midnight on light", "#ffffff"))] + list(CIRCLE_COLORS.items())
        for k, (label, body, *_rest) in looks:
            sw = Swatch(body, label, roww, half=CIRCLE_COLORS["midnight"][1] if k == "auto" else None)
            sw.setChecked(k == b.color_key)
            grp.addButton(sw)
            sw.clicked.connect(lambda _=False, kk=k: (ctx.set_look("circle_color", kk), refresh_big(), refresh_shapes()))
            rl.addWidget(sw)
        rl.addStretch(1)
        gl.addWidget(roww)

        gl = self._group(v, "Shape")
        roww = QWidget()
        rl = QGridLayout(roww)
        rl.setContentsMargins(0, 6, 0, 6)
        rl.setSpacing(8)
        roww.setFixedWidth(3 * 84 + 2 * 8)
        grp2 = QButtonGroup(roww)
        tiles = {}
        for i, (k, label) in enumerate(CIRCLE_SHAPES.items()):
            t = PreviewTile(bubble_preview(b, shape=k), label.split(" (")[0], roww)
            t.setChecked(k == b.shape)
            grp2.addButton(t)
            t.clicked.connect(lambda _=False, kk=k: (ctx.set_look("circle_shape", kk), refresh_big()))
            rl.addWidget(t, i // 3, i % 3, Qt.AlignCenter)
            tiles[k] = t
        gl.addWidget(roww, 0, Qt.AlignHCenter)

        def refresh_shapes():
            for k, t in tiles.items():
                t.pix = bubble_preview(b, shape=k)
                t.update()

        gl = self._group(v, "Size and count")
        self._seg(gl, "Size", "Resizing keeps the circle where it is.",
                  [(k, v_[0]) for k, v_ in CIRCLE_SIZES.items()], self._s("circle_size", "medium"),
                  lambda k: (ctx.set_look("circle_size", k), refresh_big()), stacked=True)
        self._toggle(gl, "Show the count", "The number of open thoughts in the middle (off: just a dot).",
                     "show_count", True, lambda on: (ctx.set_count_vis(on), refresh_big()))

        gl = self._group(v, "Opacity")
        for label, key, desc in (("Circle", "opacity_circle", "See through it a little when it sits over your work."),
                                 ("Quick note", "opacity_quick", ""), ("Full list", "opacity_list", "")):
            w = ctx.windows[key]
            self._slider(gl, label, desc, 40, 100, round(100 * self._s(key, 1.0)), lambda x: f"{x}%",
                         lambda x, kk=key, ww=w: ctx.set_opacity(kk, ww, x / 100), step=5)

        gl = self._group(v, "Countdown on the outline")
        display = self._seg(gl, "Show the countdown", "Time left replaces the note count while a timer runs.",
                            [("ring", "Outline"), ("time", "Time left"), ("hidden", "Off")],
                            b.timer_display, lambda key: (ctx.set_display(key), cards.setEnabled(key != "hidden")),
                            stacked=True)
        cards = QWidget()
        cg = QGridLayout(cards)
        cg.setContentsMargins(0, 4, 0, 6)
        cg.setSpacing(6)
        grp3 = QButtonGroup(cards)
        for i, (k, label, tip) in enumerate(RING_STYLES):
            c = ChoiceCard(label, tip, cards)
            c.setChecked(k == b.ring_style)
            grp3.addButton(c)
            c.clicked.connect(lambda _=False, kk=k: ctx.set_ring_style(kk))   # also previews for 10 s
            cg.addWidget(c, i // 2, i % 2)
        cards.setEnabled(display.value != "hidden")
        gl.addWidget(cards)
        self._row(gl, "Preview", "Watch the circle for 10 seconds (picking a style also previews it).",
                  self._button("Preview", ctx.preview_ring))
        v.addStretch(1)
        return area

    def page_focus(self):
        ctx = self.ctx
        area, v = self._page("Focus & breaks", "Timers start from the full list. This is how they behave.")
        gl = self._group(v, "Lengths")
        self._slider(gl, "Focus", "Default length of a focus round.", 5, 120,
                     round(self._s("focus_min", DEFAULT_FOCUS_MIN)), lambda x: f"{x} min",
                     lambda x: ctx.set_length("focus_min", x), step=5)
        self._slider(gl, "Break", "Default length of a break.", 1, 30, round(self._s("break_min", DEFAULT_BREAK_MIN)),
                     lambda x: f"{x} min", lambda x: ctx.set_length("break_min", x))
        gl_nap = self._group(v, "Nap presets")
        buttons = QWidget()
        nap_list = QVBoxLayout(buttons)
        nap_list.setContentsMargins(0, 0, 0, 0)
        nap_list.setSpacing(5)
        for index, minutes in enumerate(nap_presets({"nap_presets": self._s("nap_presets", DEFAULT_NAP_PRESETS)})):
            row = QHBoxLayout()
            row.setSpacing(6)
            start_btn = self._button(f"Start {minutes} min", lambda _=False, i=index: ctx.start_nap(
                nap_presets({"nap_presets": self._s("nap_presets", DEFAULT_NAP_PRESETS)})[i]))
            edit_btn = QPushButton("Edit")
            edit_btn.setObjectName("act")
            edit_btn.setCursor(Qt.PointingHandCursor)

            def edit_nap(_=False, i=index, button=start_btn):
                current = nap_presets({"nap_presets": self._s("nap_presets", DEFAULT_NAP_PRESETS)})
                value = ask(self, "Nap length", current[i], (10, 15, 20, 30), "min", (1, 120))
                if value:
                    current[i] = value
                    self._set("nap_presets", current)
                    button.setText(f"Start {value} min")

            edit_btn.clicked.connect(edit_nap)
            row.addWidget(start_btn)
            row.addWidget(edit_btn)
            row.addStretch(1)
            nap_list.addLayout(row)
        nap_title = QLabel("Three quick lengths")
        nap_title.setObjectName("rowTitle")
        nap_desc = QLabel("A nap runs as a break. Start one from the circle's right-click menu.")
        nap_desc.setObjectName("rowDesc")
        nap_desc.setWordWrap(True)
        gl_nap.addWidget(nap_title)
        gl_nap.addWidget(nap_desc)
        gl_nap.addWidget(buttons)
        gl = self._group(v, "When a round ends")
        self._toggle(gl, "Start the break by itself", "Handy if you tend to skip breaks.", "auto_break", False,
                     lambda on: ctx.panel.update_timer_row())
        self._toggle(gl, "Sound when done", "A short system sound.", "timer_sound", True)
        self._seg(gl, "Remind me when the break is over", "If you haven't come back, the circle asks again this often.",
                  [(0, "Off"), (3, "3 min"), (5, "5 min"), (10, "10 min")], self._s("overrun_nudge_min", 5),
                  lambda k: self._set("overrun_nudge_min", k))
        gl = self._group(v, "What a round is for")
        self._toggle(gl, "Ask what each round is for", "When a round or break starts, the circle asks (a project, "
                     "a calendar event, Meal, Call). Skip is fine. Shows on the session card and in the AI export.",
                     "focus_tags", True)
        self._toggle(gl, "Track apps during focus", "Every few seconds of a focus round, note the app and window title "
                     "you're in. Stays on this PC. Idle time doesn't count. Pick the distracting ones on the "
                     "session card.", "track_apps", True)
        gl3 = self._group(v, "Phone alert")
        intro = QLabel("Get a buzz on your phone when a break ends, even in another room. Install the free <b>ntfy</b> "
                       "app, tap + and subscribe to this topic. Only \"Break's over\" is sent, never your notes.")
        intro.setObjectName("rowDesc")
        intro.setTextFormat(Qt.RichText)
        intro.setWordWrap(True)
        gl3.addWidget(intro)
        if not self._s("ntfy_topic", ""):
            self._set("ntfy_topic", "parkinglot-" + uuid.uuid4().hex[:16])
        tbox = QWidget()
        tl = QHBoxLayout(tbox)
        tl.setContentsMargins(0, 0, 0, 0)
        tl.setSpacing(6)
        topic = QLineEdit(self._s("ntfy_topic", ""), tbox)
        topic.setToolTip("Works like a password: anyone who knows it can see these alerts. Keep it random.")
        topic.editingFinished.connect(lambda: self._set("ntfy_topic", re.sub(r"[^-_A-Za-z0-9]", "", topic.text())[:64]))
        cp = self._button("Copy", lambda: (QGuiApplication.clipboard().setText(self._s("ntfy_topic", "")),
                                           cp.setText("Copied \u2713"), QTimer.singleShot(1500, lambda: cp.setText("Copy"))))
        tl.addWidget(topic, 1)
        tl.addWidget(cp)
        self._row(gl3, "Topic", "", tbox, stretch_control=True)
        self._toggle(gl3, "When a break ends", "", "ntfy_break", True)
        self._toggle(gl3, "When a focus round ends", "", "ntfy_focus", False)
        self.push_status = QLabel("")
        self.push_status.setObjectName("rowDesc")
        self.push_status.setWordWrap(True)
        test = self._button("Send a test", lambda: (self.push_status.setText("Sending..."), send_phone_push(
            self._s("ntfy_topic", ""), APP_NAME + " test", "If your phone buzzed, break alerts will reach you.",
            priority=5, on_done=self.push_result.emit)))
        self._row(gl3, "Test it", "Your phone should buzz within a few seconds.", test)
        gl3.addWidget(self.push_status)
        gl = self._group(v, "Today")
        n, total = FocusTimer.today_stats()
        self._row(gl, f"{n} rounds done · {total} min focused", "Everything is in the focus log.",
                  self._button("Open focus log", lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(str(FOCUS_LOG)))
                               if FOCUS_LOG.exists() else None))
        v.addStretch(1)
        return area

    def page_checkins(self):
        ctx = self.ctx
        area, v = self._page("Check-ins", "The circle notices when you've been on the computer a while without a focus "
                                          "round. It stays quiet in full screen, calls and presentations.")
        gl = self._group(v, "Check-ins")
        stat = QLabel(ctx.nudges.status())
        stat.setObjectName("rowTitle")
        stat.setStyleSheet(f"color: {C['glimmer']};")
        gl.addWidget(stat)
        self._toggle(gl, "Friendly check-ins", "Only counts time you're actually using the computer (and it keeps "
                     "counting through a restart).", "nudge_on", True)
        self._toggle(gl, "Mention important work", "Used when Calendar is disconnected. Name the nearest "
                     "unfinished work at most once every 2 hours.", "nudge_work_on", True)
        self._toggle(gl, "Mention calendar events", "When connected, some check-ins name the next event "
                     "before it starts. Event names stay out of the focus log and AI export.",
                     "nudge_calendar_on", True)
        self._seg(gl, "Every", "Minutes of screen time between check-ins.",
                  [(m, f"{m}") for m in (20, 30, 45, 60, 90)], self._s("nudge_every_min", 45),
                  lambda k: self._set("nudge_every_min", k))
        paused = self._s("nudge_paused_until", 0) > time.time()
        pause_box = QWidget()
        pb = QHBoxLayout(pause_box)
        pb.setContentsMargins(0, 0, 0, 6)
        pb.setSpacing(6)
        if paused:
            pb.addWidget(self._button("Turn back on", lambda: (self._set("nudge_paused_until", 0),
                                                               self.open_at("checkins"))))
        else:
            for label, secs in NudgeManager.PAUSES:
                short = {"Rest of today": "Today", "Until I turn them back on": "Until I turn it on"}.get(label, label)
                b = self._button(short, lambda _=False, s_=secs: (ctx.nudges.pause(s_), self.open_at("checkins")))
                b.setToolTip(label)
                pb.addWidget(b)
        until = NudgeManager.paused_text(self._s("nudge_paused_until", 0)) if paused else ""
        self._row(gl, "Pause check-in messages", f"Paused {until}." if paused else "Quiet for a while, or until you "
                  "turn them back on.")
        gl.addWidget(pause_box)                # the choices get their own line, so none gets squeezed
        self._row(gl, "Try one", "See what a check-in looks like.",
                  self._button("Check in now", lambda: ctx.nudges.check_in(preview=True)))
        gl = self._group(v, "When focus starts")
        self._toggle(gl, "A few words of boost", "A short line from the circle as a round begins.", "boost_on", True)
        self._seg(gl, "Style", "Help to start, a mix, or keep-you-in-flow lines.",
                  [("yes", "Help me start"), ("sometimes", "A mix"), ("no", "Keep me in flow")],
                  self._s("procrastinator", "sometimes"), lambda k: self._set("procrastinator", k))
        gl = self._group(v, "Little touches")
        self._toggle(gl, "\"Saved!\" pop", "A word above the circle after a quick note.", "saved_pop", True)
        v.addStretch(1)
        return area

    def page_sound(self):
        ctx = self.ctx
        area, v = self._page("Sound & peeks", "Background noise to mask the room, and small reminders during focus.")
        gl = self._group(v, "Background noise")
        self._toggle(gl, "Play noise", "Also on the ♫ button in the list.", "noise_on", False,
                     lambda on: ctx.noise_sync())
        cards = QWidget()
        cl = QHBoxLayout(cards)
        cl.setContentsMargins(0, 4, 0, 6)
        cl.setSpacing(6)
        grp = QButtonGroup(cards)
        for k, label, tip in NOISE_KINDS:
            c = ChoiceCard(label, tip.split(". ")[0], cards)
            c.setToolTip(tip)
            c.setChecked(k == self._s("noise_kind", "brown"))
            grp.addButton(c)
            c.clicked.connect(lambda _=False, kk=k: (self._set("noise_kind", kk), ctx.noise_sync()))
            cl.addWidget(c)
        gl.addWidget(cards)
        self._slider(gl, "Volume", "", 5, 100, round(100 * ctx.noise_vol()), lambda x: f"{x}%",
                     lambda x: (self._set("noise_vol", x / 100), ctx.noise.set_volume(x / 100)), step=5)
        self._toggle(gl, "Only during focus rounds", "Starts and stops with the timer.", "noise_focus_only", False,
                     lambda on: ctx.noise_sync())
        gl = self._group(v, "Music")
        songs = ctx.music.tracks()
        box = QComboBox(self)
        box.setMinimumWidth(200)
        box.addItem("Off")
        for f in songs:
            box.addItem(f.stem)
        if ctx.music.track in songs:
            box.setCurrentIndex(songs.index(ctx.music.track) + 1)
        box.currentIndexChanged.connect(lambda i: ctx.music_pick(songs[i - 1], True) if i else ctx.music.stop())
        self._row(gl, "Song on repeat", "Songs from the music folder. Also on the ♫ button in the list.", box)
        self._row(gl, "Add songs", "Drop audio files in, then reopen Settings.",
                  self._button("Open music folder", ctx.open_music_folder))
        gl = self._group(v, "Note reminders")
        self._seg(gl, "Tone", "A reminder pops up even when its tone is muted.",
                  [("soft", "Soft"), ("alert", "Alert"), ("system", "System"), ("mute", "Mute")],
                  self._s("reminder_tone", "soft"), lambda key: self._set("reminder_tone", key), stacked=True)
        self._row(gl, "Try the sound", "Hear the selected reminder tone now.",
                  self._button("Play reminder tone", lambda: play_reminder_tone(self._s("reminder_tone", "soft"))))
        for index, default in enumerate((5, 10, 30), 1):
            key = f"reminder_snooze_{index}"
            spin = QSpinBox(self)
            spin.setRange(1, 240)
            spin.setValue(max(1, min(240, int(self._s(key, default)))))
            spin.setSuffix(" min")
            spin.valueChanged.connect(lambda n, k=key: self._set(k, n))
            self._row(gl, f"Snooze button {index}", "Minutes shown on each reminder.", spin)
        gl = self._group(v, "Water and eye breaks")
        self._seg(gl, "Count", "Focus rounds only, or any time you're at the keyboard (breaks and 1 min away "
                  "don't count).", [("focus", "Focus rounds"), ("always", "Any screen time")],
                  self._s("peek_when", "focus"), lambda key: self._set("peek_when", key))
        self._toggle(gl, "Water reminder", "Every 40 minutes, across rounds.", "peek_water", True)
        self._toggle(gl, "Look-away reminder", "Every 20 minutes, across rounds.", "peek_eyes", True)
        self._toggle(gl, "Look-away countdown", "Look at something 20 ft (6 m) away for 20 s. The 20-20-20 rule "
                     "from the American Academy of Ophthalmology. Off: a short peek, gone in 5 s.", "eye_guide", False)
        self._toggle(gl, "Sound first", "A short soft tone just before it shows.", "peek_sound", True)
        self._row(gl, "Try one", "", self._button("Preview a peek", lambda: ctx.peek.peek(random.choice(list(PEEKS)))))
        v.addStretch(1)
        return area

    def page_flags(self):
        ctx = self.ctx
        area, v = self._page("Flags", "Tags for a parked thought. Reorder them (the order you see here is the order in "
                                      "the quick note and the list), turn off the ones you don't use, or make your own. "
                                      "Your own flags work everywhere: search, filter, history, the AI export.")
        gl = self._group(v, "Your flags")
        st = ctx.store.settings
        for i, key in enumerate(list(FLAG_KEYS)):
            _k, icon, word, tip = FLAG_DEFS[i]
            box = QWidget()
            bl = QHBoxLayout(box)
            bl.setContentsMargins(0, 0, 0, 0)
            bl.setSpacing(4)
            for arrow, d, tipd in (("\u2191", -1, "Move up"), ("\u2193", 1, "Move down")):
                ab = self._button(arrow, lambda _=False, k=key, dd=d: self._move_flag(k, dd))
                ab.setToolTip(tipd)
                ab.setFixedWidth(30)
                ab.setEnabled(0 <= i + d < len(FLAG_KEYS))
                bl.addWidget(ab)
            if key not in BUILTIN_FLAG_KEYS:
                ed = self._button("Edit", lambda _=False, k=key: self._edit_flag(k))
                rm = self._button("Remove", lambda _=False, k=key: self._remove_flag(k))
                rm.setToolTip("Notes keep it in their history; it just stops showing")
                bl.addWidget(ed)
                bl.addWidget(rm)
            sw = ToggleSwitch(flag_on(st, key))
            sw.setToolTip("Show or hide this flag everywhere")
            sw.toggled.connect(lambda on, k=key: ctx.set_flag_on(k, on))
            bl.addSpacing(6)
            bl.addWidget(sw)
            d = tip.split(": ", 1)[-1]
            self._row(gl, f"{icon}  {word[0].upper() + word[1:]}", d[:1].upper() + d[1:], box)

        # add / edit a flag of your own
        gl2 = self._group(v, "Make your own")
        self.flag_edit_key = None
        form = QWidget()
        fl = QGridLayout(form)
        fl.setContentsMargins(0, 6, 0, 6)
        fl.setHorizontalSpacing(8)
        fl.setVerticalSpacing(6)
        self.f_icon = QLineEdit(form)
        self.f_icon.setPlaceholderText("\U0001F4A1")
        self.f_icon.setMaxLength(8)
        self.f_icon.setFixedWidth(56)
        self.f_icon.setAlignment(Qt.AlignCenter)
        self.f_icon.setToolTip("An emoji or a symbol. On Windows press Win + . (period) for the emoji picker")
        self.f_word = QLineEdit(form)
        self.f_word.setPlaceholderText("Name, e.g. \"people\" or \"money\"")
        self.f_word.setMaxLength(18)
        self.f_tip = QLineEdit(form)
        self.f_tip.setPlaceholderText("What it means (optional)")
        self.f_tip.setMaxLength(90)
        fl.addWidget(self.f_icon, 0, 0)
        fl.addWidget(self.f_word, 0, 1)
        fl.addWidget(self.f_tip, 1, 0, 1, 2)
        colors = QWidget(form)
        cl = QHBoxLayout(colors)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(2)
        self.f_colors = QButtonGroup(colors)
        for j, col in enumerate(CUSTOM_FLAG_COLORS):
            sw = Swatch(col, col, colors)
            sw.setChecked(j == 0)
            self.f_colors.addButton(sw, j)
            cl.addWidget(sw)
        cl.addStretch(1)
        fl.addWidget(colors, 2, 0, 1, 2)
        btns = QHBoxLayout()
        self.f_save = self._button("Add flag", self._save_flag)
        self.f_cancel = self._button("Cancel", lambda: self._edit_flag(None))
        self.f_cancel.hide()
        self.f_msg = QLabel("", form)
        self.f_msg.setObjectName("rowDesc")
        btns.addWidget(self.f_save)
        btns.addWidget(self.f_cancel)
        btns.addWidget(self.f_msg, 1)
        fl.addLayout(btns, 3, 0, 1, 2)
        self.f_word.returnPressed.connect(self._save_flag)
        gl2.addWidget(form)
        v.addStretch(1)
        return area

    def _flags_changed(self):
        self.ctx.flags_changed()
        self.open_at("flags")

    def _move_flag(self, key, d):
        order = list(FLAG_KEYS)
        i = order.index(key)
        j = i + d
        if 0 <= j < len(order):
            order[i], order[j] = order[j], order[i]
            self._set("flag_order", order)
            self._flags_changed()

    def _edit_flag(self, key):
        c = next((c for c in self.ctx.store.settings.get("custom_flags", []) if c["key"] == key), None)
        self.flag_edit_key = key if c else None
        self.f_icon.setText(c.get("icon", "") if c else "")
        self.f_word.setText(c.get("word", "") if c else "")
        self.f_tip.setText(c.get("tip", "").split(": ", 1)[1] if c and ": " in c.get("tip", "") else "")
        col = c.get("color") if c else CUSTOM_FLAG_COLORS[0]
        j = CUSTOM_FLAG_COLORS.index(col) if col in CUSTOM_FLAG_COLORS else 0
        self.f_colors.button(j).setChecked(True)
        self.f_save.setText("Save changes" if c else "Add flag")
        self.f_cancel.setVisible(bool(c))
        self.f_msg.setText("")
        if c:
            self.f_word.setFocus()

    def _save_flag(self):
        word = " ".join(self.f_word.text().split()).lower()
        if not word:
            self.f_msg.setText("Give it a name first.")
            return
        taken = {w.lower() for k, _i, w, _t in FLAG_DEFS if k != self.flag_edit_key}
        if word in taken:
            self.f_msg.setText("There's already a flag with that name.")
            return
        icon = self.f_icon.text().strip() or "\u2022"
        tip = self.f_tip.text().strip()
        col = CUSTOM_FLAG_COLORS[max(0, self.f_colors.checkedId())]
        flags = [dict(c) for c in self.ctx.store.settings.get("custom_flags", [])]
        if self.flag_edit_key:
            for c in flags:
                if c["key"] == self.flag_edit_key:
                    c.update(icon=icon, word=word, tip=tip, color=col)
        else:
            flags.append({"key": "f_" + uuid.uuid4().hex[:8], "icon": icon, "word": word,
                          "tip": f"{word[0].upper() + word[1:]}: {tip}" if tip else word[0].upper() + word[1:],
                          "color": col})
        if self.flag_edit_key:
            for c in flags:
                if c["key"] == self.flag_edit_key:
                    c["tip"] = f"{word[0].upper() + word[1:]}: {tip}" if tip else word[0].upper() + word[1:]
        self._set("custom_flags", flags)
        self._flags_changed()

    def _remove_flag(self, key):
        flags = [c for c in self.ctx.store.settings.get("custom_flags", []) if c["key"] != key]
        self._set("custom_flags", flags)
        self._set("flag_order", [k for k in FLAG_KEYS if k != key])
        FLAG_COLORS.pop(key, None)
        self._flags_changed()

    def page_controls(self):
        ctx = self.ctx
        area, v = self._page("Controls", "How you open things.")
        gl = self._group(v, "Mouse and keys")
        sw = self._toggle(gl, "Scribble gestures", "Up and down for a quick note, left and right for the list.",
                          "gesture", True, lambda on: [x.setEnabled(on) for x in (near, calls, sens, radius, g_quick, g_list)]
                          + [ctx.set_gesture(on)])
        sw.setEnabled(ctx.gesture_available)
        self._overlay = getattr(self, "_overlay", None) or GestureOverlay()
        sens = self._slider(gl, "Scribble sensitivity", "Drag to see on screen how big a scribble has to be.", 1, 5,
                            int(self._s("scribble_level", 3)), lambda x: SCRIBBLE_LEVEL_NAMES[x].split()[0],
                            lambda x: (self._set("scribble_level", x),
                                       SCRIBBLE_TUNE.update(zip(("revs", "min_seg"), SCRIBBLE_LEVELS[x])),
                                       self._overlay.show_scribble(ctx.bubble, x, self._s("gesture_near", True))))
        sens.sliderPressed.connect(lambda: self._overlay.show_scribble(ctx.bubble, sens.value(),
                                                                       self._s("gesture_near", True)))
        near = self._toggle(gl, "Only near the circle", "Scribble on or around the circle. Off: anywhere on screen.",
                            "gesture_near", True, lambda on: (radius_row.setVisible(on),
                                                             self._overlay.show_zone(ctx.bubble, radius.value())
                                                             if on else None))
        radius = self._slider(gl, "How near", "Drag to see the area around the circle where scribbles count.", 120, 700,
                              int(self._s("gesture_near_px", GESTURE_NEAR_PX)), lambda x: f"{x} px",
                              lambda x: (self._set("gesture_near_px", x), self._overlay.show_zone(ctx.bubble, x)),
                              step=10)
        radius.sliderPressed.connect(lambda: self._overlay.show_zone(ctx.bubble, radius.value()))
        radius_row = radius.parentWidget().parentWidget()      # the whole "How near" row
        radius_row.setVisible(bool(self._s("gesture_near", True)))
        calls = self._toggle(gl, "Off during calls", "No scribbles while your mic or camera is on, so a meeting "
                             "never pops the list open.", "gesture_calls_off", True)
        g_quick = self._toggle(gl, "Up and down: quick note", "Off: that scribble does nothing.", "gesture_quick", True)
        g_list = self._toggle(gl, "Left and right: full list", "Off: that scribble does nothing.", "gesture_list", True)
        for x in (near, calls, sens, radius, g_quick, g_list):
            x.setEnabled(ctx.gesture_available and self._s("gesture", True))
        gl2 = self._group(v, "Hotkeys")
        note = QLabel("Click a box and press the new combo (Ctrl, Alt or Shift plus a key). It's saved right away.")
        note.setObjectName("rowDesc")
        note.setWordWrap(True)
        gl2.addWidget(note)
        self.hk_status = QLabel("")
        self.hk_status.setObjectName("rowDesc")
        self.hk = {}
        for key, label, default in (("hotkey_quick", "Quick note", DEFAULT_HOTKEY_QUICK),
                                    ("hotkey_panel", "Full list", DEFAULT_HOTKEY_PANEL)):
            box = QWidget()
            bl = QHBoxLayout(box)
            bl.setContentsMargins(0, 0, 0, 0)
            bl.setSpacing(6)
            ed = HotkeyEdit(self._s(key, default), ctx.hotkeys_stop, ctx.hotkeys_resume, box)
            ed.setFixedWidth(170)
            ed.editingFinished.connect(self._save_hotkeys)
            clr = self._button("Clear", lambda _=False, e=ed: (e.clear(), self._save_hotkeys()))
            bl.addWidget(ed)
            bl.addWidget(clr)
            self._row(gl2, label, "", box)
            self.hk[key] = ed
        gl2.addWidget(self.hk_status)
        gl = self._group(v, "Help")
        days = max(0, TIPS_DAYS - int((time.time() - TIPS["first_seen"]) / 86400))
        self._seg(gl, "Hover tips", f"Auto shows them for your first week ({days} day{'s' if days != 1 else ''} left), "
                  "then keeps out of your way.", [("auto", "Auto"), ("on", "Always"), ("off", "Off")],
                  TIPS["mode"], lambda k: (self._set("tips", k), TIPS.update(mode=k)))
        gl = self._group(v, "Dropping files on the circle")
        self._toggle(gl, "Ask what to keep", "After a drop: keep the file and its name, just the file, or just the "
                     "name. No answer in 8 s keeps both.", "drop_ask", True)
        gl = self._group(v, "The full list")
        self._toggle(gl, "Close it when I click elsewhere", "Like a popup. It stays open for its own menus and drops.",
                     "close_on_outside", False)
        self._row(gl, "Tour", "A 30 second walk through, from the circle.", self._button("Take the tour", ctx.start_tour))
        v.addStretch(1)
        return area

    def _save_hotkeys(self):
        vals = {k: e.keySequence().toString(QKeySequence.PortableText) for k, e in self.hk.items()}
        for (k, seq), name in zip(vals.items(), ("Quick note", "Full list")):
            if seq and not qt_to_pynput(seq):
                self.hk_status.setText(f"\u2717 {name}: '{seq}' needs Ctrl, Alt or Shift plus a normal key.")
                return
        if vals["hotkey_quick"] and vals["hotkey_quick"] == vals["hotkey_panel"]:
            self.hk_status.setText("\u2717 Both hotkeys are the same.")
            return
        for k, seq in vals.items():
            self._set(k, seq)
        self.ctx.hotkeys_resume()
        self.hk_status.setText("\u2713 Saved. Try it now.")

    def page_privacy(self):
        ctx = self.ctx
        area, v = self._page("Privacy & data", "Thoughts stay local. Google Calendar access is optional and read-only.")
        gl = self._group(v, "On screen")
        self._toggle(gl, "Hide from screen share", "The app doesn't show up in screen shares or screenshots.",
                     "hide_from_share", PRIVACY["hide_from_share"], ctx.set_priv)
        self._toggle(gl, "Hide the circle in full screen", "Movies, games, presentations.", "hide_fullscreen", True,
                     ctx.set_fs)
        gl = self._group(v, "Patterns")
        self._toggle(gl, "Note if music is playing", "When you park a thought: only the app and whether it's playing, "
                     "never the song. Windows only.", "music_log", False, lambda on: ctx.media.apply())
        gl = self._group(v, "Your thoughts")
        self._row(gl, "History", "Every thought you've ever parked.", self._button("Browse", ctx.panel.open_history))
        box = QWidget()
        bl = QHBoxLayout(box)
        bl.setContentsMargins(0, 0, 0, 0)
        bl.setSpacing(6)
        for label, days in (("7 days", 7), ("30 days", 30), ("All", None)):
            bl.addWidget(self._button(label, lambda _=False, d=days: ctx.copy_export(d)))
        self._row(gl, "Copy for AI", "Your thoughts with instructions, to paste into an AI chat.", box)
        self._row(gl, "AI analyses", "Save an AI's answer so the next export builds on it.",
                  self._button("Open...", ctx.open_analyses))
        self._row(gl, "Data folder", str(DATA_DIR), self._button("Open", lambda: QDesktopServices.openUrl(
            QUrl.fromLocalFile(str(DATA_DIR)))))
        v.addStretch(1)
        return area

    def page_about(self):
        ctx = self.ctx
        area, v = self._page(APP_NAME, APP_TAGLINE)
        gl = self._group(v)
        self._row(gl, f"Version {APP_VERSION}", f"Made by {APP_AUTHOR}.")
        for label, url in (("GitHub", GITHUB_URL), ("Buy me a coffee", COFFEE_URL)):
            b = self._button("Open" if url else "Coming soon", lambda _=False, u=url: QDesktopServices.openUrl(QUrl(u)))
            b.setEnabled(bool(url))
            self._row(gl, label, "", b)
        self._row(gl, "Updates", "Gets the newest version from GitHub, then restarts. Your notes stay.",
                  self._button("Restart / update", ctx.restart))
        v.addStretch(1)
        return area


class HotkeyDialog(QDialog):
    def __init__(self, quick_seq, panel_seq):
        super().__init__(None, Qt.WindowStaysOnTopHint)
        self.setWindowTitle(APP_NAME + " hotkeys")
        self.setObjectName("panel")
        self.setStyleSheet(STYLE + "QKeySequenceEdit, QLineEdit { min-width: 160px; }")
        form = QFormLayout(self)
        self.quick = QKeySequenceEdit(QKeySequence(quick_seq))
        self.panel = QKeySequenceEdit(QKeySequence(panel_seq))
        for ed in (self.quick, self.panel):
            if hasattr(ed, "setMaximumSequenceLength"):
                ed.setMaximumSequenceLength(1)
        form.addRow("Private quick note:", self._row(self.quick))
        form.addRow("Full list:", self._row(self.panel))
        note = QLabel("Click a box, press the new combo. Use Ctrl, Alt or Shift plus a key.\n"
                      "Clear = no hotkey. Changes apply right away.")
        note.setObjectName("hint")
        form.addRow(note)
        self.err = QLabel("")
        self.err.setStyleSheet(f"color: {C['idea']};")
        form.addRow(self.err)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._check)
        bb.rejected.connect(self.reject)
        form.addRow(bb)

    @staticmethod
    def _row(ed):
        w = QWidget()
        h = QHBoxLayout(w)
        h.setContentsMargins(0, 0, 0, 0)
        h.addWidget(ed, 1)
        b = QToolButton()
        b.setText("Clear")
        b.clicked.connect(ed.clear)
        h.addWidget(b)
        return w

    def values(self):
        return (self.quick.keySequence().toString(QKeySequence.PortableText),
                self.panel.keySequence().toString(QKeySequence.PortableText))

    def _check(self):
        q, p = self.values()
        for name, seq in (("Quick note", q), ("Full list", p)):
            if seq and not qt_to_pynput(seq):
                self.err.setText(f"{name}: '{seq}' needs Ctrl/Alt/Shift plus a normal key.")
                return
        if q and q == p:
            self.err.setText("Both hotkeys are the same.")
            return
        self.accept()


# ---------------------------------------------------------------- updates
def update_script(path=None):
    """Restart / update: swap in the newest parking_lot.py from GitHub. Only this file changes; notes stay.
    A git checkout (someone working on the code) is left alone. Returns updated, current, dev or failed."""
    path = Path(path or __file__).resolve()
    if (path.parent / ".git").exists():
        return "dev"
    try:
        with urllib.request.urlopen(UPDATE_URL, timeout=10) as r:   # ponytail: blocks up to 10 s, it's a restart anyway
            new = r.read()
        if f'APP_NAME = "{APP_NAME}"'.encode() not in new:
            raise ValueError("download is not Park That Thought")
        compile(new, str(path), "exec")          # never swap in a broken file
        if new == path.read_bytes():
            return "current"
        tmp = path.with_name(path.name + ".new")
        tmp.write_bytes(new)
        shutil.copy2(path, path.with_name(path.name + ".bak"))   # the previous version, in case
        os.replace(tmp, path)
        return "updated"
    except Exception as e:
        log_error(f"update failed: {e}")
        return "failed"


# ---------------------------------------------------------------- single instance
def ping_running(message="show"):
    """True if a running copy (this version or newer) answered."""
    sock = QLocalSocket()
    sock.connectToServer(SERVER_NAME)
    if not sock.waitForConnected(600):
        return False
    sock.write(message.encode())
    sock.flush()
    sock.waitForBytesWritten(600)
    sock.disconnectFromServer()
    return True


def recover_stuck_lock(lock):
    """The lock is held but nobody answers: usually an older version still running in the background.
    Offer to close it. Returns True if we now hold the lock."""
    pid, app_name = None, ""
    try:
        lines = (DATA_DIR / ".lock").read_text(encoding="utf-8", errors="ignore").splitlines()
        pid = int(lines[0]) if lines and lines[0].strip().isdigit() else None
        app_name = lines[1] if len(lines) > 1 else ""
    except Exception:
        pass
    box = QMessageBox(QMessageBox.Question, APP_NAME,
                      "Another copy of " + APP_NAME + " seems to be running in the background"
                      + (f" (process {pid})" if pid else "") + ", but it isn't responding.\n\n"
                      "This usually means an older version is still open.\n"
                      "Close it and start this one? Anything typed in the last second might not be saved.")
    box.setStandardButtons(QMessageBox.Yes | QMessageBox.No)
    box.setWindowFlag(Qt.WindowStaysOnTopHint)
    if box.exec() != QMessageBox.Yes:
        return False
    if pid and "python" in app_name.lower() and IS_WIN:
        try:
            subprocess.run(["taskkill", "/PID", str(pid), "/F"], capture_output=True,
                           creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0), timeout=10)
        except Exception as e:
            log_error(f"could not close old copy (pid {pid}): {e}")
    time.sleep(0.6)
    lock.removeStaleLockFile()
    return lock.tryLock(3000)


# ---------------------------------------------------------------- app
def main():
    def hook(etype, value, tb):  # pythonw has no console: log every crash
        import traceback
        log_error("".join(traceback.format_exception(etype, value, tb)))
    sys.excepthook = hook
    if IS_WIN:
        os.environ.setdefault("QT_QPA_PLATFORM", "windows:fontengine=directwrite")
        try:   # own taskbar identity, so the list's taskbar button shows our icon instead of Python's
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("ParkThatThought.App")
        except Exception as e:
            log_error(f"app id failed: {e}")
    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)
    tip_gate = TipGate(app)
    app.installEventFilter(tip_gate)
    app.setApplicationName(APP_NAME)
    app.setWindowIcon(app_icon())
    if IS_WIN:
        f = QFont("Segoe UI Variable Text")
        if not QFont(f).exactMatch():
            f = QFont("Segoe UI")
        f.setPointSize(10)
        app.setFont(f)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    lock = QLockFile(str(DATA_DIR / ".lock"))
    replacing = "--replace" in sys.argv      # started by Restart: the old copy is on its way out
    if not lock.tryLock(0):
        if replacing:
            if not lock.tryLock(4000):
                ping_running("quit")             # still there? ask it to go
                if not lock.tryLock(6000) and not recover_stuck_lock(lock):
                    return
        else:
            if ping_running("show"):
                return  # already running: that copy opens its list instead
            if not lock.tryLock(3000) and not recover_stuck_lock(lock):  # wait covers "Restart" handover
                return
    store = Store()
    apply_theme(store.settings.get("theme", "system"))
    app.styleHints().colorSchemeChanged.connect(lambda _s: apply_theme())
    calendar = GoogleCalendar(store)
    if not store.settings.get("first_seen"):
        store.settings["first_seen"] = time.time()
    TIPS.update(mode=store.settings.get("tips", "auto"), first_seen=store.settings["first_seen"])
    app._caret_sync = CaretSync(app)  # keeps the accessibility caret aligned (kept alive on app)
    gesture = ScribbleDetector()
    SCRIBBLE_TUNE.update(zip(("revs", "min_seg"), SCRIBBLE_LEVELS[int(store.settings.get("scribble_level", 3))]))
    gesture.enabled = store.settings.get("gesture", True)
    PRIVACY["hide_from_share"] = store.settings.get("hide_from_share", True)
    hotkeys = HotkeyManager()
    timer = FocusTimer(store)
    confetti = Confetti()
    session_card = SessionCard()
    holder = {}

    def setting(key, default):
        return store.settings.get(key, default)

    def set_setting(key, value):
        store.settings[key] = value
        store.save()

    def set_count_vis(on):
        bubble.show_count = on
        set_setting("show_count", on)
        bubble.update()

    def set_gesture(on):
        gesture.enabled = on
        set_setting("gesture", on)

    def set_fs(on):
        set_setting("hide_fullscreen", on)
        if holder.get("guard"):
            holder["guard"].enabled_fs = on
            if not on and holder["guard"].hidden_for_fs:
                holder["guard"].hidden_for_fs = False
                bubble.show()
                holder["meeting_badge"].update_meeting()

    def set_priv(on):
        PRIVACY["hide_from_share"] = on
        set_setting("hide_from_share", on)
        for w in (bubble, holder["panel"], holder["quickbox"], holder["meeting_badge"],
                  holder["meeting_badge"].agenda, holder["meeting_badge"].notice):
            if w.isVisible():
                apply_share_privacy(w)

    def set_length(key, minutes):
        set_setting(key, float(minutes))
        p = holder["panel"]
        spin = p.focus_spin if key == "focus_min" else p.break_spin
        spin.blockSignals(True)
        spin.setValue(float(minutes))
        spin.blockSignals(False)
        p.update_timer_row()

    def open_settings(page="appearance"):
        w = holder.get("settings_win")
        if w is None:
            class Ctx:
                pass
            ctx = Ctx()
            ctx.setting, ctx.set_setting, ctx.store = setting, set_setting, store
            ctx.bubble, ctx.panel, ctx.calendar = bubble, holder["panel"], calendar
            ctx.meeting_bar = holder["meeting_badge"]
            ctx.windows = {"opacity_circle": bubble, "opacity_quick": holder["quickbox"],
                           "opacity_list": holder["panel"]}
            ctx.set_look, ctx.set_opacity, ctx.set_display = set_look, set_opacity, set_display
            ctx.set_theme = set_theme
            ctx.set_ring_style, ctx.preview_ring, ctx.set_count_vis = set_ring_style, preview_ring, set_count_vis
            ctx.set_flag_on, ctx.set_gesture, ctx.gesture_available = set_flag_on, set_gesture, gesture.available
            ctx.edit_hotkeys, ctx.set_length = edit_hotkeys, set_length
            ctx.start_nap = start_nap
            ctx.set_fs, ctx.set_priv, ctx.restart = set_fs, set_priv, restart
            ctx.hotkeys_stop = hotkeys.stop
            ctx.flags_changed = lambda: (holder["panel"].flags_changed(), holder["quickbox"].build_flags())
            ctx.hotkeys_resume = lambda: hotkeys.apply(setting("hotkey_quick", DEFAULT_HOTKEY_QUICK),
                                                       setting("hotkey_panel", DEFAULT_HOTKEY_PANEL))
            ctx.copy_export, ctx.open_analyses = copy_export, open_analyses
            ctx.nudges, ctx.noise, ctx.peek, ctx.media = holder["nudges"], holder["noise"], holder["peek"], holder["media"]
            ctx.noise_sync, ctx.noise_vol, ctx.start_tour = holder["noise_sync"], holder["noise_vol"], holder["start_tour"]
            ctx.music, ctx.music_pick, ctx.open_music_folder = holder["music"], music_pick, open_music_folder
            w = holder["settings_win"] = SettingsWindow(ctx)
        w.open_at(page)

    def build_menu():
        """The right-click menu: things you do now. Everything you set once lives in the Settings window."""
        m = QMenu()
        panel_, quick_ = holder["panel"], holder["quickbox"]
        m.addAction("Full list" + ("  (hide)" if panel_.isVisible() else ""), panel_.toggle)
        m.addAction("Quick note", quick_.popup)
        if timer.running or timer.overrun_since:
            m.addSeparator()
            if timer.overrun_since and not timer.running:
                m.addAction("I'm back from the break", timer.clear_overrun)
            elif timer.kind == "break":
                m.addAction("End break", timer.stop)
            else:
                m.addAction("Resume focus" if timer.paused else "Pause focus",
                            timer.resume if timer.paused else timer.pause)
                m.addAction("Stop focus", timer.stop)
                dr = m.addAction("Drifted: take out minutes...", lambda: take_out_drift(timer, None))
                dr.setToolTip(DRIFT_TIP)
                m.setToolTipsVisible(True)
        if not timer.running:
            nap_menu = m.addMenu("Nap timer")
            for minutes in nap_presets(store.settings):
                nap_menu.addAction(f"{minutes} min", lambda n=minutes: start_nap(n))
        m.addSeparator()
        gm = m.addMenu("Scribble gestures")
        gm.setEnabled(gesture.available and setting("gesture", True))
        for label, key in (("Up and down: quick note", "gesture_quick"), ("Left and right: full list", "gesture_list")):
            ga = gm.addAction(label)
            ga.setCheckable(True)
            ga.setChecked(setting(key, True))
            ga.toggled.connect(lambda on, k=key: set_setting(k, on))
        nz = m.addAction("Background noise")
        nz.setCheckable(True)
        nz.setChecked(setting("noise_on", False))
        nz.toggled.connect(lambda on: (set_setting("noise_on", on), holder["noise_sync"]()))
        nd = holder.get("nudges")
        if nd:
            info = m.addAction(nd.status())
            info.setEnabled(False)
        if setting("nudge_paused_until", 0) > time.time():
            m.addAction("Turn check-in messages back on", lambda: set_setting("nudge_paused_until", 0))
        else:
            pm = m.addMenu("Pause check-in messages")
            for label, secs in NudgeManager.PAUSES:
                pm.addAction(label, lambda s_=secs: nd and nd.pause(s_))
        m.addSeparator()
        m.addAction("Google Calendar...", lambda: open_settings("calendar"))
        m.addAction("Settings...", open_settings)
        tl = m.addMenu("Thought log")
        fill_ai_menu(tl)
        m.addSeparator()
        m.addAction("Restart / update", restart)
        m.addAction("Quit", app.quit)
        holder["menu"] = m
        keep_menu_open(m)
        return m

    def music_pick(path, on):
        if not on:
            music.stop()
        elif not music.play(path):
            toast("Couldn't play that file", 3000)

    def fill_music_menu(mu):
        songs = music.tracks()
        for f in songs:
            ma = mu.addAction(f.stem)
            ma.setCheckable(True)
            ma.setChecked(f == music.track)
            ma.toggled.connect(lambda on, f_=f: music_pick(f_, on))
        if not songs:
            mu.addAction("No songs yet. Open the folder and add some.").setEnabled(False)
        mu.addSeparator()
        if music.track:
            mu.addAction("Stop", music.stop)
        mu.addAction("Open music folder", open_music_folder)

    def open_music_folder():
        MUSIC_DIR.mkdir(exist_ok=True)
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(MUSIC_DIR)))

    def restart():
        """Start a fresh copy (it loads the current file) and make sure this one really goes: the new copy is
        told to take over (--replace), and this one quits, with a hard exit as a backstop if something
        (a menu's own event loop, a stuck thread) keeps it alive."""
        store.flush_on_quit()
        toast("Checking for updates...")
        app.processEvents()
        status = update_script()
        exe = Path(sys.executable)
        pyw = exe.with_name("pythonw.exe")
        if IS_WIN and pyw.exists():
            exe = pyw  # no console window
        if QProcess.startDetached(str(exe), [str(Path(__file__).resolve()), "--replace", f"--update={status}"],
                                  str(APP_DIR)):
            hard_quit()
        else:
            toast("Couldn't restart. Quit, then open Park That Thought again.")

    def hard_quit():
        QTimer.singleShot(0, app.quit)
        QTimer.singleShot(1500, lambda: (store.flush_on_quit(), os._exit(0)))

    def toast(msg, ms=4500):
        QToolTip.showText(bubble.mapToGlobal(QPoint(0, 40)), msg, bubble, bubble.rect(), ms)

    def fill_ai_menu(menu):
        menu.addAction("Browse history...", panel.open_history)
        menu.addSeparator()
        menu.addAction("Copy last 7 days for AI", lambda: copy_export(7))
        menu.addAction("Copy last 30 days for AI", lambda: copy_export(30))
        menu.addAction("Copy everything for AI", lambda: copy_export(None))
        menu.addAction("Copy as a file (everything)", lambda: copy_export(None, as_file=True))
        menu.addSeparator()
        menu.addAction("Add AI analysis (paste the answer)...", lambda: open_analyses(new=True))
        n = len(load_analyses())
        menu.addAction(f"Open AI analyses ({n} saved)...", open_analyses)

    def build_ai_menu():
        am = QMenu()
        am.setStyleSheet(STYLE)
        fill_ai_menu(am)
        return am

    def open_analyses(new=False):
        dlg = holder.get("analyses")
        if dlg is None:
            dlg = holder["analyses"] = AnalysesDialog(store)
        dlg.open_dialog(new=new)

    def copy_export(days, as_file=False):
        store.save_now()
        now = datetime.now()
        set_setting("last_ai_export", {"days": days, "to": now.isoformat(timespec="seconds"),
                                       "from": (now - timedelta(days=days)).isoformat(timespec="seconds") if days else ""})
        text, n = build_ai_export(store, days, calendar_events=calendar.recent_events + calendar.events)
        n_prev = len(analyses_for(days))
        md = QMimeData()
        if as_file:
            EXPORT_DIR.mkdir(parents=True, exist_ok=True)
            path = EXPORT_DIR / f"parking-lot-thoughts-{datetime.now():%Y%m%d-%H%M}.md"
            path.write_text(text, encoding="utf-8")
            md.setUrls([QUrl.fromLocalFile(str(path))])
            msg = f"Copied a file with {n} thoughts. Paste it into your AI chat as an attachment."
        else:
            md.setText(text)
            msg = f"Copied {n} thoughts with instructions. Paste into your AI chat."
        if n_prev:
            msg += f" Includes {n_prev} earlier analys{'is' if n_prev == 1 else 'es'} to build on."
        QGuiApplication.clipboard().setMimeData(md)
        toast(msg, 4000)

    def start_timer(minutes, kind="focus"):
        timer.start(minutes, kind)
        bubble.refresh_shape()

    def start_nap(minutes):
        if timer.running:
            toast("A timer is already running", 2500)
            return
        start_timer(minutes, "break")

    def set_display(key):
        bubble.timer_display = key
        set_setting("timer_display", key)
        bubble.refresh_shape()

    def set_theme(mode):
        set_setting("theme", mode)
        apply_theme(mode)

    def set_look(key, value):
        set_setting(key, value)
        bubble.set_look(color=value if key == "circle_color" else None, shape=value if key == "circle_shape" else None,
                        size=value if key == "circle_size" else None)

    def set_opacity(key, w, value):
        set_setting(key, value)
        w.setWindowOpacity(value)

    def set_flag_on(key, on):
        flags = dict(setting("flags_on", {}))
        flags[key] = bool(on)
        set_setting("flags_on", flags)
        panel.apply_flag_settings()

    def set_ring_style(key):
        bubble.ring_style = key
        set_setting("ring_style", key)
        bubble.refresh_shape()
        if not timer.running:
            preview_ring()

    def preview_ring():
        """Show the chosen outline on a fake countdown for a few seconds, without touching the real timer or logs."""
        if timer.running:
            toast("The circle is already showing it", 2500)
            return
        real = bubble.timer

        class _Fake:
            running, paused, kind, overrun_since = True, False, "focus", None
            t0 = time.monotonic()

            def progress(self):
                return max(0.0, 0.85 - (time.monotonic() - self.t0) / 40)

            def remaining(self):
                return 600

        bubble.timer = _Fake()
        bubble.refresh_shape()

        def done():
            bubble.timer = real
            bubble.refresh_shape()
        QTimer.singleShot(10000, done)

    def edit_hotkeys():
        hotkeys.stop()  # so pressing the old combo while editing doesn't fire
        dlg = HotkeyDialog(setting("hotkey_quick", DEFAULT_HOTKEY_QUICK), setting("hotkey_panel", DEFAULT_HOTKEY_PANEL))
        apply_share_privacy(dlg)
        if dlg.exec() == QDialog.Accepted:
            q, p = dlg.values()
            set_setting("hotkey_quick", q)
            set_setting("hotkey_panel", p)
        hotkeys.apply(setting("hotkey_quick", DEFAULT_HOTKEY_QUICK), setting("hotkey_panel", DEFAULT_HOTKEY_PANEL))

    bubble = Bubble(build_menu)
    panel = Panel(store, bubble)
    panel.important.calendar = calendar
    calendar.events_updated.connect(panel.important.refresh_later)
    holder["panel"] = panel
    quickbox = QuickBox(panel)
    holder["quickbox"] = quickbox
    app._note_alarms = NoteAlarmManager(store, app, panel.refresh_later, bubble, panel)
    for key, w in (("opacity_circle", bubble), ("opacity_quick", quickbox), ("opacity_list", panel)):
        w.setWindowOpacity(max(0.3, min(1.0, float(setting(key, 1.0)))))
    hotkeys.quick.connect(quickbox.toggle)
    def panel_hotkey():
        """A showing question takes the list hotkey first, so it can be answered from the keyboard."""
        mb = holder.get("meeting_badge")
        sp = holder.get("speech")
        for w in (sp if sp is not None and sp._btns else None, session_card, mb.notice if mb else None):
            if w is not None and w.isVisible() and not w.isActiveWindow():
                w.take_keys()
                return
        panel.toggle()
    hotkeys.panel.connect(panel_hotkey)
    hotkeys.apply(setting("hotkey_quick", DEFAULT_HOTKEY_QUICK), setting("hotkey_panel", DEFAULT_HOTKEY_PANEL))

    bubble.show_count = setting("show_count", True)
    display_setting = setting("timer_display", "ring")
    bubble.timer_display = display_setting if display_setting in ("ring", "time", "hidden") else "ring"
    bubble.ring_style = setting("ring_style", "ember") if setting("ring_style", "ember") in RING_STYLE_KEYS else "ember"
    bubble.set_look(color=setting("circle_color", "auto"), shape=setting("circle_shape", "cloud"),
                    size=setting("circle_size", "medium"))
    THEME["hooks"].append(bubble.update)
    bubble.timer = timer
    panel.timer = timer
    panel.menu_builder = build_menu
    panel.ai_menu_builder = build_ai_menu
    timer.tick.connect(panel.update_timer_row)

    def focus_context():
        """Timer state at the moment a thought is parked. state: focus, paused, break, break_over, none."""
        if timer.running and timer.kind == "break":
            return {"in_focus": False, "on_break": True, "state": "break"}
        if not timer.running:
            if timer.overrun_since:   # break ended, not back yet
                return {"in_focus": False, "on_break": False, "state": "break_over",
                        "late_min": round(timer.overrun_min(), 1)}
            return {"in_focus": False, "on_break": False, "state": "none"}
        st = timer.state
        return {"in_focus": True, "minute": round((st["minutes"] * 60 - timer.remaining()) / 60, 1),
                "planned": st["minutes"], "paused": timer.paused, "state": "paused" if timer.paused else "focus"}
    store.context_fn = focus_context

    drop_state = {"t": None}

    def on_drop(md):
        t = panel.task_from_mime(md, source="circle_drop")
        if not t:
            return False
        bubble.set_count(store.open_count())
        files = [a for a in t.get("attachments", []) if a.get("kind") != "image" or md.hasUrls()]
        if files and md.hasUrls() and setting("drop_ask", True):
            drop_state["t"] = t
            n = len(files)
            what = f"\"{t['title']}\"" if n == 1 else f"{n} files"
            QTimer.singleShot(150, lambda: (bubble.hop(), speech.say(
                bubble.geometry(), f"Parked {what}. Keep the file and its name?",
                [("File + name", "drop_both"), ("Just the file", "drop_file"), ("Just the name", "drop_name")],
                emoji="\U0001F4CE", anim="bounce", timeout_ms=8000)))
        return True

    def drop_answer(key):
        t, drop_state["t"] = drop_state["t"], None
        if t is None or not key.startswith("drop_") or key == "drop_both":
            return
        if key == "drop_name":
            for a in list(t.get("attachments", [])):
                store.remove_attachment(t, a)          # the copy goes to trash; your original is never touched
        elif key == "drop_file":
            t["title"] = f"File {datetime.now():%H:%M}"
        store.save()
        panel.refresh_later()
    bubble.drop_handler = on_drop
    timer.tick.connect(bubble.refresh_shape)
    next_focus_confirmation = {"minutes": None}

    def start_next_focus(minutes):
        next_focus_confirmation["minutes"] = minutes
        timer.start(minutes, "focus")
        started = timer.running and timer.kind == "focus"
        if not started:
            next_focus_confirmation["minutes"] = None
        return started

    def on_finished(kind, minutes):
        bubble.refresh_shape()
        panel.update_timer_row()
        topic = setting("ntfy_topic", "")
        if kind == "break":
            QTimer.singleShot(300, lambda m=minutes: nudges.break_over(m))   # the circle hops and says so
            if topic and setting("ntfy_break", True):
                _f, line = pick_fresh(BREAK_END_LINES, "break_end_phone")
                send_phone_push(topic, "Break's over", line, priority=5)
        else:
            confetti.burst(bubble.geometry().center(), [])
            ls = getattr(timer, "last_session", None) or {"start": time.time() - minutes * 60, "end": time.time()}
            parked, urges, dists = session_stats(store, ls["start"], ls["end"])
            bm, fm = setting("break_min", DEFAULT_BREAK_MIN), setting("focus_min", DEFAULT_FOCUS_MIN)
            auto = bool(setting("auto_break", False))
            if auto:
                # linked: the break starts by itself (after this signal returns, so the timer isn't re-entered)
                QTimer.singleShot(0, lambda: (timer.start(bm, "break"), bubble.refresh_shape(), panel.update_timer_row()))
            def start_chosen_break(length):
                timer.start(length, "break")
                return timer.running and timer.kind == "break"
            session_card.on_break = start_chosen_break
            session_card.on_again = start_next_focus
            start_iso = datetime.fromtimestamp(ls["start"]).isoformat(timespec="seconds")

            def mark_app(_app, _verdict):     # this round only; the log is append-only, the last row wins
                timer._write({"kind": "app_marks", "session_start": start_iso,
                              "end": datetime.now().isoformat(timespec="seconds"),
                              "distracting": sorted(a for a, v in session_card.marks.items() if v == "distracting")})

            def take_out(n):
                timer.trim_away(n, False, start_iso)
                return n
            session_card.on_mark, session_card.on_take_out = mark_app, take_out
            glim = session_glimmers(store, ls["start"], ls["end"]) if flag_on(store.settings, "glimmer") else 0
            session_card.show_for(bubble.geometry(), minutes, parked, urges, dists, bm, fm, auto_break=auto,
                                  glimmers=glim, today=today_summary(store), on=ls.get("on", ""),
                                  apps=timer.last_apps)
            if topic and setting("ntfy_focus", False):
                send_phone_push(topic, "Focus session done", f"{fmt_min(minutes)} min done. Time for a break.", priority=3)
        if setting("timer_sound", True):
            try:
                if IS_WIN:
                    import winsound
                    winsound.MessageBeep(winsound.MB_OK)
                else:
                    QApplication.beep()
            except Exception:
                pass
    timer.finished.connect(on_finished)

    area = QGuiApplication.primaryScreen().availableGeometry()
    bx, by = store.settings.get("bubble", [area.right() - 44, area.center().y()])
    bx = max(area.left(), min(bx, area.right() - bubble.width()))
    by = max(area.top(), min(by, area.bottom() - bubble.height()))
    bubble.move(bx, by)

    def remember_bubble(p):
        store.settings["bubble"] = [p.x(), p.y()]
        store.save()
    bubble.moved.connect(remember_bubble)

    def rescue_bubble(*_):
        """A monitor or TV was unplugged or changed: bring the circle back if it's now off every screen."""
        c = bubble.geometry().center()
        if QGuiApplication.screenAt(c) is None:
            a = QGuiApplication.primaryScreen().availableGeometry()
            bubble.move(a.right() - bubble.width() - 4, a.center().y())
            remember_bubble(bubble.pos())
    QGuiApplication.instance().screenRemoved.connect(lambda *_: QTimer.singleShot(500, rescue_bubble))
    QGuiApplication.instance().primaryScreenChanged.connect(lambda *_: QTimer.singleShot(500, rescue_bubble))
    bubble.clicked.connect(panel.toggle)
    def gesture_ok():
        """Scribbles only count near the circle (on by default), and never while you're in a call."""
        if setting("gesture_calls_off", True) and mic_or_camera_in_use():
            return False
        if setting("gesture_near", True):
            if not bubble.isVisible():
                return False
            c, p = bubble.geometry().center(), QCursor.pos()
            return math.hypot(c.x() - p.x(), c.y() - p.y()) <= setting("gesture_near_px", GESTURE_NEAR_PX)
        return True
    gesture.vertical.connect(lambda: quickbox.toggle() if setting("gesture_quick", True) and gesture_ok() else None)
    gesture.horizontal.connect(lambda: panel.toggle() if setting("gesture_list", True) and gesture_ok() else None)
    bubble.show()
    bubble.refresh_shape()
    meeting_badge = MeetingBadge(bubble, calendar)
    holder["meeting_badge"] = meeting_badge
    meeting_badge.open_settings = lambda: open_settings("calendar")
    guard = PresenceGuard(bubble, lambda: [panel, quickbox, confetti, session_card] +
                          ([holder["speech"]] if holder.get("speech") else []) +
                          [meeting_badge, meeting_badge.agenda, meeting_badge.notice])
    guard.visibility_changed = meeting_badge.update_meeting
    guard.calendar_bar = meeting_badge
    guard.enabled_fs = setting("hide_fullscreen", True)
    holder["guard"] = guard
    if guard.ok:
        guard._check()  # decide full-screen visibility before the bar's first show
    meeting_badge.update_meeting()
    speech = SpeechBubble()
    holder["speech"] = speech
    holder["speech"] = speech
    nudges = NudgeManager(store, timer, bubble, speech, lambda: holder.get("guard"), calendar)
    holder["nudges"] = nudges
    nudges.wants_focus.connect(lambda minutes: timer.start(minutes, "focus"))
    nudges.wants_break.connect(lambda minutes: timer.start(minutes, "break"))
    nudges.wants_more_break.connect(timer.extend_break)
    timer.started.connect(lambda: setattr(nudges, "break_parts", []) if timer.kind == "focus" else None)
    def tag_ok():
        """Ask what a round is for unless it's off or now is a bad moment (a meeting on the calendar is fine:
        that's often what the round is for)."""
        q = nudges.quiet_reason()
        return setting("focus_tags", True) and (not q or q == "calendar event in progress")

    def on_focus_started():
        """Starting a focus session tucks the full list away and asks what it's for (or shows the boost line).
        A break asks too, unless the session card is up."""
        if timer.kind != "focus":
            if tag_ok() and not session_card.isVisible():
                QTimer.singleShot(400, lambda: nudges.ask_tag("break") if timer.kind == "break" else None)
            return
        panel.hide()
        chosen = next_focus_confirmation["minutes"]
        next_focus_confirmation["minutes"] = None
        if tag_ok():
            lead = f"Focus started for {fmt_min(chosen)} min." if chosen else ""
            QTimer.singleShot(300, lambda: nudges.ask_tag("focus", lead) if timer.kind == "focus" else None)
        elif chosen:
            QTimer.singleShot(250, lambda m=chosen: confirm_focus_started(bubble, speech, timer, m))
        else:
            QTimer.singleShot(400, nudges.boost)
    panel.ask_tag = lambda: nudges.ask_tag_text()
    timer.started.connect(on_focus_started)
    timer.away_back.connect(nudges.away_back)
    timer.overrun_return.connect(nudges.back_from_break)
    if not store.settings.get("procrastinator_asked"):      # first run: one question for the boost style
        QTimer.singleShot(4000, lambda: None if nudges.quiet_reason() else nudges.ask_style())

    # ---- background noise
    noise = NoisePlayer()
    holder["noise"] = noise
    music = MusicPlayer()
    holder["music"] = music

    def noise_vol():
        v = setting("noise_vol", 0.25)
        return float(v) if isinstance(v, (int, float)) else dict((k, x) for k, _, x in NOISE_VOLUMES).get(v, 0.25)

    def noise_should_play():
        if not setting("noise_on", False):
            return False
        return not setting("noise_focus_only", False) or (timer.running and timer.kind == "focus")

    def noise_sync():
        want = noise_should_play()
        kind = setting("noise_kind", "brown")
        if want and (not noise.playing or noise.kind != kind):
            if not noise.play(kind, noise_vol()):
                toast("Couldn't start the sound (no audio output?)", 3000)
                set_setting("noise_on", False)
        elif not want and noise.playing:
            noise.stop()
        on = setting("noise_on", False)
        panel.noise_btn.setStyleSheet(f"color: {C['accent_text']};" if on else "")

    def fill_noise_menu(menu):
        on = menu.addAction("Play")
        on.setCheckable(True)
        on.setChecked(setting("noise_on", False))
        on.toggled.connect(lambda v: (set_setting("noise_on", v), noise_sync()))
        menu.addSeparator()
        g = QActionGroup(menu)
        for key, label, tip in NOISE_KINDS:
            a = menu.addAction(label)
            a.setToolTip(tip)
            a.setCheckable(True)
            a.setChecked(setting("noise_kind", "brown") == key)
            g.addAction(a)
            a.triggered.connect(lambda _=False, k=key: (set_setting("noise_kind", k), set_setting("noise_on", True),
                                                        noise_sync()))
        menu.addSeparator()
        g2 = QActionGroup(menu)
        for key, label, v in NOISE_VOLUMES:
            a = menu.addAction(f"Volume: {label}")
            a.setCheckable(True)
            a.setChecked(abs(noise_vol() - v) < 0.03)
            g2.addAction(a)
            a.triggered.connect(lambda _=False, vv=v: (set_setting("noise_vol", vv), noise.set_volume(vv)))
        menu.addSeparator()
        fo = menu.addAction("Only during focus sessions")
        fo.setCheckable(True)
        fo.setChecked(setting("noise_focus_only", False))
        fo.toggled.connect(lambda v: (set_setting("noise_focus_only", v), noise_sync()))
        menu.setToolTipsVisible(True)
        keep_menu_open(menu)

    def noise_popup(anchor):
        m = QMenu(panel)
        m.setStyleSheet(STYLE)
        fill_noise_menu(m)
        m.addSeparator()
        fill_music_menu(m.addMenu("Music" + (f"  ({music.track.stem})" if music.track else "")))
        m.exec(anchor.mapToGlobal(anchor.rect().bottomLeft()))

    timer.started.connect(noise_sync)
    timer.ended.connect(lambda: QTimer.singleShot(0, noise_sync))
    app.aboutToQuit.connect(noise.stop)
    QTimer.singleShot(0, noise_sync)

    # ---- peeks during focus: elapsed focus carries across rounds and restarts
    peek = PeekBuddy(bubble, store.settings)
    holder["peek"] = peek
    peek_clock = store.settings.get("peek_focus_clock")
    if not isinstance(peek_clock, dict):
        peek_clock = {}
        store.settings["peek_focus_clock"] = peek_clock
    peek_saved_at = [time.monotonic()]

    def peek_can_show():
        # A calendar event alone is not proof of a call or a reason to lose a focus reminder.
        return (bubble.isVisible() and not guard.hidden_for_fs and
                not mic_or_camera_in_use() and not windows_says_quiet())

    def peek_tick():
        kind = focus_peek_step(peek_clock, timer.state, timer.remaining(), store.settings, peek_can_show,
                               idle=idle_seconds())
        if kind:
            peek.peek(kind)
        counting = (timer.running and timer.kind == "focus") or store.settings.get("peek_when") == "always"
        if kind or (counting and time.monotonic() - peek_saved_at[0] >= 300):
            store.save()
            peek_saved_at[0] = time.monotonic()
    peek_timer = QTimer(app)
    peek_timer.setInterval(20000)
    peek_timer.timeout.connect(peek_tick)
    peek_timer.start()
    timer.started.connect(peek_tick)
    app.aboutToQuit.connect(store.save)

    # ---- break over and not back: ask again every few minutes
    over = {"n": 0}

    def overrun_tick():
        every = setting("overrun_nudge_min", 5)
        if not timer.overrun_since or timer.running or not every:
            over["n"] = 0
            return
        n = int(timer.overrun_min() // every)
        if n > over["n"]:
            over["n"] = n
            nudges.overrun_nudge(timer.overrun_min())
    over_timer = QTimer(app)
    over_timer.setInterval(15000)
    over_timer.timeout.connect(overrun_tick)
    over_timer.start()

    # ---- music logging
    holder["media"] = MediaWatch(store)

    # ---- quick tour: a few speech bubbles from the circle
    TOUR = [("\U0001F44B", "Hi! I'm your parking spot for stray thoughts. Here's the 30 second tour."),
            ("\U0001F4AD", "Mid-focus and a thought pulls at you? Scribble the mouse up and down (or use the hotkey) "
                             "and type it. It's parked. Back to work."),
            ("\U0001F4E5", "I'm a drop shelf too. Drag a file, screenshot, link or text onto me and I hold it. "
                             "Later, drag it back out of the list into an email, a chat or a folder."),
            ("\U0001F5C2\uFE0F", "Click me to open the full list. Flag notes as urgent, itch, distraction, lift, drain or idea."),
            ("\u23F1\uFE0F", "Start a focus round from the list. I show the countdown on my outline."),
            ("\U0001F50E", "Ctrl+F in the list searches and filters. History shows everything you've ever parked."),
            ("\u2699\uFE0F", "Right-click me for settings: noise, peeks, check-ins, look. That's it. Go focus!")]
    tour_state = {"i": None}

    def tour_step():
        i = tour_state["i"]
        if i is None or i >= len(TOUR):
            tour_state["i"] = None
            return
        face, text = TOUR[i]
        last = i == len(TOUR) - 1
        bubble.hop()
        speech.say(bubble.geometry(), text, [("Done" if last else "Next", "tour_next")] +
                   ([] if last else [("Skip", "tour_skip")]), emoji=face, anim="bounce", timeout_ms=60000)

    def tour_answer(key):
        if tour_state["i"] is None:
            return
        if key == "tour_next":
            tour_state["i"] += 1
            QTimer.singleShot(0, tour_step)
        else:
            tour_state["i"] = None

    def start_tour():
        panel.hide()
        tour_state["i"] = 0
        QTimer.singleShot(200, tour_step)
    speech.closed.connect(tour_answer)
    speech.closed.connect(drop_answer)
    holder["start_tour"] = start_tour

    holder["noise_sync"], holder["noise_vol"] = noise_sync, noise_vol
    panel.settings_opener = open_settings
    panel.noise_menu = lambda anchor: noise_popup(anchor)
    panel.tour_starter = start_tour


    def on_status(ok):
        bubble.set_save_ok(ok)
        panel.status.setStyleSheet("" if ok else f"color: {C['idea']};")
        if not ok:
            panel.status.setText("Save retrying (OneDrive busy?). Safe copy kept locally.")
    store.on_status = on_status

    server = QLocalServer()
    QLocalServer.removeServer(SERVER_NAME)  # clear a leftover from a crash
    if not server.listen(SERVER_NAME):
        log_error(f"single-instance server failed: {server.errorString()}")

    def on_ping():
        c = server.nextPendingConnection()
        if not c:
            return
        c.waitForReadyRead(300)
        msg = bytes(c.readAll()).decode(errors="ignore")
        c.disconnectFromServer()
        if "quit" in msg:                         # a newer copy (Restart) is taking over
            hard_quit()
            return
        if "show" in msg:
            bubble.show()
            bubble.raise_()
            panel.show_near_bubble()
    server.newConnection.connect(on_ping)

    def on_quit():
        server.close()
        store.flush_on_quit()
        gesture.stop()
        hotkeys.stop()
        lock.unlock()
    app.aboutToQuit.connect(on_quit)
    said = {"--update=updated": "Updated to the newest version.", "--update=current": "You have the newest version.",
            "--update=failed": "Couldn't reach GitHub, so no update this time."}
    for arg in sys.argv:
        if arg in said:
            QTimer.singleShot(1500, lambda m=said[arg]: toast(m))
    code = app.exec()
    os._exit(code)          # never linger after the loop ends (a leftover thread would keep the lock and the old UI)


if __name__ == "__main__":
    try:
        main()
    except Exception:  # pythonw has no console: make startup crashes visible in error.log
        import traceback
        log_error("startup crash:\n" + traceback.format_exc())
        raise
