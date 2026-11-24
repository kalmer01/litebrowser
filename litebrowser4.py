#!/usr/bin/env python3
"""LiteBrowser 4 - light, fast Chromium browser: dark-red "liquid glass" UI, Google search,
extensions, built-in ad/tracker blocker and a start page with lifetime blocking stats.

Install:  pip install -U "PyQt6>=6.10" "PyQt6-WebEngine>=6.10"
Run:      python litebrowser4.py [url]

Extensions: unpacked Manifest V3 folders in ~/.litebrowser/extensions/ (or  ⋯ > Extensions).
Shortcuts: Ctrl+T new tab | Ctrl+W close | Ctrl+L address bar | Ctrl+Tab next tab
           F5 reload | Alt+Left/Right back/forward | Ctrl +/-/0 zoom
"""
import time as _time
_T0 = _time.perf_counter()      # used by the built-in benchmark (--bench-out)
_MARKS = {}


def _mark(name):
    _MARKS[name] = (_time.perf_counter() - _T0) * 1000


import hashlib
import json
import math
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
from datetime import datetime
from pathlib import Path
from functools import lru_cache

os.environ["QTWEBENGINE_CHROMIUM_FLAGS"] = " ".join([
    "--disable-sync", "--disable-background-networking", "--disable-default-apps",
    "--disable-breakpad", "--disable-component-update", "--no-first-run", "--no-pings",
    "--disable-features=Translate,TranslateUI,MediaRouter,OptimizationHints",
    "--enable-gpu-rasterization", "--enable-zero-copy", "--renderer-process-limit=4",
    "--disable-domain-reliability", "--disable-client-side-phishing-detection", "--disable-hang-monitor",
    "--metrics-recording-only", "--log-level=3",
])

try:
    import PyQt6.QtWebEngineWidgets, PyQt6.QtWebEngineCore, PyQt6.QtNetwork       # noqa: F401
except Exception as _e:                      # double-clicked with a Python that lacks PyQt6: say so instead of vanishing
    _msg = ("LiteBrowser needs PyQt6, but this Python (%s) can't load it:\n%s\n\nOpen Command Prompt and run:\n"
            "python -m pip install -U \"PyQt6>=6.10\" \"PyQt6-WebEngine>=6.10\"\n\nThen start LiteBrowser again "
            "(use run_litebrowser.bat from the folder)." % (sys.executable, _e))
    try:
        import ctypes
        ctypes.windll.user32.MessageBoxW(0, _msg, "LiteBrowser", 0x10)
    except Exception:
        print(_msg)
        input("Press Enter to close...")
    sys.exit(1)
from PyQt6.QtCore import (QEasingCurve, QEvent, QRect, QStandardPaths, QVariantAnimation, QObject, QParallelAnimationGroup, QPoint, QPointF, QPropertyAnimation,
                          QRectF, QSize, Qt, QTimer, QUrl, QDateTime, pyqtProperty, pyqtSignal)
from PyQt6.QtGui import QBitmap, QBrush, QCursor, QLinearGradient, QRadialGradient
from PyQt6.QtNetwork import QLocalServer, QLocalSocket, QNetworkCookie
from PyQt6.QtGui import (QAction, QColor, QDesktopServices, QFont, QFontMetrics, QIcon, QKeySequence,
                         QPainter, QPainterPath, QPalette, QPen, QPixmap, QPolygonF, QShortcut)
from PyQt6.QtWebEngineCore import (QWebEngineDownloadRequest, QWebEnginePage, QWebEngineProfile, QWebEngineScript,
                                   QWebEngineSettings, QWebEngineUrlRequestInfo,
                                   QWebEngineUrlRequestInterceptor)
from PyQt6.QtWebEngineWidgets import QWebEngineView
try:
    from PyQt6.QtWebEngineCore import QWebEnginePermission
except ImportError:                      # Qt older than 6.8: no permission prompts
    QWebEnginePermission = None
from PyQt6.QtWidgets import (QAbstractButton, QApplication, QGraphicsOpacityEffect, QScrollArea, QFileDialog, QHBoxLayout, QInputDialog, QLabel, QLineEdit,
                             QFrame, QMainWindow, QMenu, QProgressBar, QStackedWidget, QTabBar,
                             QToolButton, QVBoxLayout, QWidget)

DATA = Path(os.environ.get("LITEBROWSER_DATA") or (Path.home() / ".litebrowser"))   # benchmark.py points this at a temp folder
_mark("imports_done")

# ---------------------------------------------------------------- self-update (single file)
APP_VERSION = "4.0.6"          # bump this whenever you publish a new litebrowser4.py
UPDATE_URL = ""                # direct link to the raw litebrowser4.py (e.g. a GitHub "Raw" link); or set it in the menu
UPDATE_FILE = DATA / "litebrowser_update.py"   # used by the .exe build, which can't overwrite itself


def _fatal(title, text):
    """Start-up problems: write them to error.log and show a message box (a console would just flash and vanish)."""
    try:
        DATA.mkdir(parents=True, exist_ok=True)
        with open(DATA / "error.log", "a", encoding="utf-8") as f:
            f.write(title + "\n" + text + "\n")
    except Exception:
        pass
    try:
        import ctypes
        ctypes.windll.user32.MessageBoxW(0, text[-1800:], title, 0x10)
    except Exception:
        try:
            print(title + "\n" + text)
            input("Press Enter to close...")
        except Exception:
            pass


def _ver(text):
    m = re.search(r'^APP_VERSION\s*=\s*"([\d.]+)"', text, re.M)
    return tuple(int(x) for x in m.group(1).split(".") if x) if m else ()


if getattr(sys, "frozen", False) and __name__ == "__main__" and UPDATE_FILE.exists():
    # .exe build: run the downloaded newer source instead of the bundled copy (falls back if it fails)
    try:
        _src = UPDATE_FILE.read_text(encoding="utf-8")
        if _ver(_src) > _ver('APP_VERSION = "%s"' % APP_VERSION):
            exec(compile(_src, str(UPDATE_FILE), "exec"), {"__name__": "__main__", "__file__": str(UPDATE_FILE)})
            sys.exit(0)
    except SystemExit:
        raise
    except BaseException:
        try:
            import traceback
            (DATA / "error.log").open("a", encoding="utf-8").write("update failed:\n" + traceback.format_exc())
            UPDATE_FILE.replace(UPDATE_FILE.with_suffix(".bad"))
            os.execv(sys.executable, [sys.executable] + sys.argv[1:])
        except Exception:
            pass

EXT_DIR = DATA / "extensions"
LIST_FILE = DATA / "blocklist.txt"
STATS_FILE = DATA / "stats.json"
COOKIE_FILE = DATA / "cookies.json"       # our own copy of every cookie (see CookieJar)
BM_FILE = DATA / "bookmarks.json"
SESSION_FILE = DATA / "session.json"
HISTORY_DB = DATA / "history.db"
FAV_DIR = DATA / "favicons"
EXT_UI_FILE = DATA / "extensions_ui.json"
STORE_URL = "https://chromewebstore.google.com/"
# Google refuses to sign in browsers built on Qt WebEngine ("This browser or app may not be secure").
# While a tab is on a Google sign-in page we identify as Firefox instead, which is the usual workaround.
SIGNIN_COMPAT = True
# Login pages ask for a passkey as soon as they open ("conditional" passkey sign-in, shown by Chrome in its autofill list).
# Without that list, Windows pops up a full "Sign in with a passkey / insert your security key" dialog on every login page.
# With this on, sites are told that quiet passkey autofill is unavailable. Clicking "use a passkey" yourself still works.
BLOCK_CONDITIONAL_PASSKEYS = True
SIGNIN_HOSTS = ("accounts.google.com", "accounts.youtube.com")
# Anti-bot / captcha providers: blocking these (some big blocklists do) makes "verifying your browser" pages loop forever.
NEVER_BLOCK = ("challenges.cloudflare.com", "arkoselabs.com", "funcaptcha.com", "hcaptcha.com", "recaptcha.net",
               "captcha-delivery.com", "datadome.co", "geetest.com", "perimeterx.net", "px-cdn.net", "px-cloud.net",
               "gstatic.com", "rbxcdn.com", "roblox.com", "cloudflare.com", "recaptcha.net", "friendlycaptcha.com",
               "mtcaptcha.com", "captcha.com", "arkoselabs.com", "client-api.arkoselabs.com",
               # sign-in providers (Microsoft, Apple, GitHub, Discord, Twitch, Steam, PayPal, Okta, Auth0, Facebook, X)
               "login.microsoftonline.com", "login.live.com", "msauth.net", "msftauth.net", "appleid.apple.com",
               "idmsa.apple.com", "appleid.cdn-apple.com", "github.com", "githubassets.com", "discord.com",
               "discordapp.com", "id.twitch.tv", "steamcommunity.com", "steampowered.com", "paypal.com",
               "paypalobjects.com", "okta.com", "oktacdn.com", "auth0.com", "login.facebook.com", "m.facebook.com",
               "x.com", "api.twitter.com", "accounts.spotify.com", "id.atlassian.com", "auth.openai.com",
               "accounts.google.com", "ssl.gstatic.com", "play.google.com")
FIREFOX_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:159.0) Gecko/20100101 Firefox/159.0"
ROUND_CONTENT = True   # round the corners of the page area (set False if pages ever show up blank)
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
LIST_URL = "https://pgl.yoyo.org/adservers/serverlist.php?hostformat=nohtml&showintro=0"
SEARCH = "https://www.google.com/search?q="
Life = QWebEnginePage.LifecycleState

# ---------------------------------------------------------------- liquid-glass theme
BG_GRAD = ("qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #3a0916,stop:0.5 #1a050d,stop:1 #0c0206)")
GLASS = ("qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 rgba(255,255,255,52),"
         "stop:0.5 rgba(255,255,255,26),stop:1 rgba(255,255,255,14))")
STYLE = f"""
QMainWindow, QWidget#root {{ background:{BG_GRAD}; }}
QWidget#tabwrap, QWidget#barwrap, QWidget#content, QWidget#storewrap {{ background:transparent; }}
QTabBar {{ background:transparent; qproperty-drawBase:0; outline:0; }}
QTabBar::tab {{ background:transparent; color:#d9b4ba; padding:8px 8px; margin:0 2px; border:none; }}
QTabBar::tab:selected {{ color:#fff3f4; }}
QTabBar::tab:hover:!selected {{ color:#f3d6da; }}
QWidget#bar {{ background:transparent; border:none; }}
QToolButton#nav, QToolButton#shield, QToolButton#wc {{ background:transparent; border:none; }}
QToolButton#shield {{ padding:0 14px 0 10px; font-size:12px; font-weight:600; color:#ffc2c8; }}
QTabBar::close-button {{ image:url("__CLOSE__"); subcontrol-position:right; margin-right:4px;
  border-radius:8px; padding:2px; }}
QTabBar::close-button:hover {{ background:rgba(255,255,255,60); }}
QLineEdit {{ background:rgba(255,255,255,20); color:#fff3f4; border:1px solid rgba(255,255,255,26);
  border-radius:12px; padding:0 12px; selection-background-color:#ff4d5e; font-size:13px; }}
QLineEdit:hover {{ background:rgba(255,255,255,28); }}
QLineEdit:focus {{ border:1px solid rgba(255,110,125,230); background:rgba(0,0,0,110); }}
QWidget#bmbar {{ background:transparent; }}
QToolButton#chip {{ background:transparent; border:none; color:#f3d6da; padding:0 11px 0 8px; font-size:12px; }}
QToolButton#chip:hover {{ color:#ffffff; }}
QLabel#clock {{ color:#f3d6da; font-size:13px; font-weight:600; padding:0 8px; }}
QLabel#hint {{ color:#a77880; font-size:12px; padding-left:6px; }}
QFrame#extpanel {{ background:rgba(30,8,15,252); border:1px solid rgba(255,255,255,34); border-radius:18px; }}
QLabel#exttitle {{ color:#fff3f4; font-size:16px; font-weight:600; }}
QLabel#extname {{ color:#fbe6e8; font-size:13px; }}
QLabel#extmuted {{ color:#a77880; font-size:12px; padding:10px; }}
QFrame#extrow {{ background:transparent; }}
QFrame#extsep {{ background:rgba(255,255,255,40); border:none; min-height:1px; max-height:1px; }}
QToolButton#flat {{ background:transparent; border:none; padding:4px; }}
QPushButton#extaction {{ background:transparent; border:none; border-radius:12px; padding:9px 12px;
  text-align:left; color:#fbe6e8; font-size:13px; }}
QPushButton#extaction:hover {{ background:rgba(255,255,255,28); }}
QLabel#extmeta {{ color:#b88a92; font-size:11.5px; }}
QFrame#storepill {{ background:rgba(255,255,255,20); border:1px solid rgba(255,255,255,30); border-radius:16px; }}
QFrame#settings {{ background:rgba(28,7,14,252); border:1px solid rgba(255,255,255,34); border-radius:20px; }}
QLabel#settitle {{ color:#fff3f4; font-size:22px; font-weight:600; }}
QScrollArea {{ background:transparent; border:none; }}
QScrollArea > QWidget > QWidget {{ background:transparent; }}
QScrollBar:vertical {{ background:transparent; width:8px; margin:2px; }}
QScrollBar::handle:vertical {{ background:rgba(255,255,255,60); border-radius:3px; min-height:30px; }}
QScrollBar::handle:vertical:hover {{ background:rgba(255,255,255,105); }}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height:0; }}
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {{ background:transparent; }}
QProgressBar {{ background:transparent; border:none; max-height:2px; min-height:2px; margin:0 14px; }}
QProgressBar::chunk {{ background:qlineargradient(x1:0,y1:0,x2:1,y2:0,stop:0 #ff4d5e,stop:1 #ff9aa5);
  border-radius:1px; }}
QMenu {{ background:rgba(30,8,15,250); color:#fbe6e8; border:1px solid rgba(255,255,255,34);
  border-radius:14px; padding:6px; }}
QMenu::item {{ padding:7px 26px 7px 14px; border-radius:8px; margin:1px 0; }}
QMenu::item:selected {{ background:rgba(255,255,255,28); }}
QMenu::item:disabled {{ color:#9a6f76; }}
QMenu::separator {{ height:1px; background:rgba(255,255,255,24); margin:5px 8px; }}
QLabel#toast {{ background:rgba(40,10,19,245); color:#fff3f4; border:1px solid rgba(255,255,255,44);
  border-radius:14px; padding:9px 16px; }}
QToolTip {{ background:#3d0a15; color:#fbe6e8; border:1px solid rgba(255,255,255,60);
  border-radius:6px; padding:4px 8px; }}
"""


def make_palette():
    p = QPalette()
    for role, col in [(QPalette.ColorRole.Window, "#1a0408"), (QPalette.ColorRole.WindowText, "#fbe6e8"),
                      (QPalette.ColorRole.Base, "#12030a"), (QPalette.ColorRole.Text, "#fff3f4"),
                      (QPalette.ColorRole.Button, "#3d0a15"), (QPalette.ColorRole.ButtonText, "#fbe6e8"),
                      (QPalette.ColorRole.Highlight, "#ff4d5e"), (QPalette.ColorRole.HighlightedText, "#ffffff"),
                      (QPalette.ColorRole.ToolTipBase, "#3d0a15"), (QPalette.ColorRole.ToolTipText, "#fbe6e8")]:
        p.setColor(role, QColor(col))
    return p


@lru_cache(maxsize=512)
def pm_icon(kind, color="#fbe6e8", size=96, width=3.4, off=False, fill=False):
    """Draw a crisp rounded line icon (48x48 design grid) so no icon fonts/files are needed."""
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.scale(size / 48, size / 48)
    c = QColor(color)
    p.setPen(QPen(c, width, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
    p.setBrush(Qt.BrushStyle.NoBrush)
    P = QPointF
    if kind == "back":
        p.drawPolyline(QPolygonF([P(29, 12), P(17, 24), P(29, 36)]))
    elif kind == "forward":
        p.drawPolyline(QPolygonF([P(19, 12), P(31, 24), P(19, 36)]))
    elif kind == "reload":
        p.drawArc(QRectF(11, 11, 26, 26), 70 * 16, 290 * 16)
        p.setBrush(c)
        p.drawPolygon(QPolygonF([P(37, 15), P(31, 25), P(43, 25)]))
    elif kind == "plus":
        p.drawLine(P(24, 13), P(24, 35))
        p.drawLine(P(13, 24), P(35, 24))
    elif kind == "dots":
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(c)
        for x in (12, 24, 36):
            p.drawEllipse(P(x, 24), 3.4, 3.4)
    elif kind == "close":
        p.drawLine(P(15, 15), P(33, 33))
        p.drawLine(P(33, 15), P(15, 33))
    elif kind == "shield":
        path = QPainterPath()
        path.moveTo(24, 7)
        path.lineTo(38, 12)
        path.lineTo(38, 23)
        path.cubicTo(38, 32, 31, 39, 24, 42)
        path.cubicTo(17, 39, 10, 32, 10, 23)
        path.lineTo(10, 12)
        path.closeSubpath()
        fill = QColor(c)
        fill.setAlpha(55)
        p.setBrush(fill)
        p.drawPath(path)
        p.setBrush(Qt.BrushStyle.NoBrush)
        if off:
            p.drawLine(P(15, 35), P(33, 13))
        else:
            p.drawPolyline(QPolygonF([P(17, 24), P(22, 29), P(31, 18)]))
    elif kind == "star":
        pts = []
        for i in range(10):
            r = 17 if i % 2 == 0 else 7.5
            a = -math.pi / 2 + i * math.pi / 5
            pts.append(P(24 + r * math.cos(a), 25 + r * math.sin(a)))
        if fill:
            p.setBrush(c)
        p.drawPolygon(QPolygonF(pts))
    elif kind == "globe":
        p.drawEllipse(P(24, 24), 14, 14)
        p.drawEllipse(P(24, 24), 6, 14)
        p.drawLine(P(10, 24), P(38, 24))
    elif kind == "puzzle":
        # Chrome-style extension piece: knob on top and right, notch on left and bottom
        p.save()
        p.translate(2.1, 3.9)
        p.scale(1.75, 1.75)
        p.setPen(QPen(c, width / 1.75, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
        path = QPainterPath()
        path.moveTo(20.500, 11.000)
        path.lineTo(19.000, 11.000)
        path.lineTo(19.000, 7.000)
        path.cubicTo(19.000, 5.900, 18.100, 5.000, 17.000, 5.000)
        path.lineTo(13.000, 5.000)
        path.lineTo(13.000, 3.500)
        path.cubicTo(13.000, 2.120, 11.880, 1.000, 10.500, 1.000)
        path.cubicTo(9.120, 1.000, 8.000, 2.120, 8.000, 3.500)
        path.lineTo(8.000, 5.000)
        path.lineTo(4.000, 5.000)
        path.cubicTo(2.900, 5.000, 2.010, 5.900, 2.010, 7.000)
        path.lineTo(2.010, 10.800)
        path.lineTo(3.500, 10.800)
        path.cubicTo(4.990, 10.800, 6.200, 12.010, 6.200, 13.500)
        path.cubicTo(6.200, 14.990, 4.990, 16.200, 3.500, 16.200)
        path.lineTo(2.000, 16.200)
        path.lineTo(2.000, 20.000)
        path.cubicTo(2.000, 21.100, 2.900, 22.000, 4.000, 22.000)
        path.lineTo(7.800, 22.000)
        path.lineTo(7.800, 20.500)
        path.cubicTo(7.800, 19.010, 9.010, 17.800, 10.500, 17.800)
        path.cubicTo(11.990, 17.800, 13.200, 19.010, 13.200, 20.500)
        path.lineTo(13.200, 22.000)
        path.lineTo(17.000, 22.000)
        path.cubicTo(18.100, 22.000, 19.000, 21.100, 19.000, 20.000)
        path.lineTo(19.000, 16.000)
        path.lineTo(20.500, 16.000)
        path.cubicTo(21.880, 16.000, 23.000, 14.880, 23.000, 13.500)
        path.cubicTo(23.000, 12.120, 21.880, 11.000, 20.500, 11.000)
        path.closeSubpath()
        p.drawPath(path)
        p.restore()
    elif kind == "lock":
        p.drawRoundedRect(QRectF(14, 22, 20, 16), 4, 4)
        path = QPainterPath()
        path.moveTo(18, 22)
        path.lineTo(18, 17)
        path.cubicTo(18, 8, 30, 8, 30, 17)
        path.lineTo(30, 22)
        p.drawPath(path)
    elif kind == "unlock":
        p.drawRoundedRect(QRectF(14, 22, 20, 16), 4, 4)
        path = QPainterPath()
        path.moveTo(18, 22)
        path.lineTo(18, 17)
        path.cubicTo(18, 8, 30, 8, 30, 15)
        p.drawPath(path)
    elif kind == "search":
        p.drawEllipse(P(21, 21), 9, 9)
        p.drawLine(P(28, 28), P(36, 36))
    elif kind == "min":
        p.drawLine(P(14, 26), P(34, 26))
    elif kind == "max":
        p.drawRoundedRect(QRectF(14, 14, 20, 20), 3.5, 3.5)
    elif kind == "restore":
        p.drawRoundedRect(QRectF(12, 18, 18, 18), 3.5, 3.5)
        p.drawPolyline(QPolygonF([P(19, 17), P(19, 13), P(35, 13), P(35, 29), P(31, 29)]))
    elif kind == "up":
        p.drawPolyline(QPolygonF([P(14, 30), P(24, 19), P(34, 30)]))
    elif kind == "down":
        p.drawPolyline(QPolygonF([P(14, 19), P(24, 30), P(34, 19)]))
    elif kind == "speaker":
        p.setBrush(c)
        p.drawPolygon(QPolygonF([P(9, 19), P(16, 19), P(25, 11), P(25, 37), P(16, 29), P(9, 29)]))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawArc(QRectF(24, 17, 12, 14), -55 * 16, 110 * 16)
        p.drawArc(QRectF(27, 11, 16, 26), -50 * 16, 100 * 16)
    elif kind == "folder":
        path = QPainterPath()
        path.moveTo(9, 15)
        path.lineTo(20, 15)
        path.lineTo(24, 20)
        path.lineTo(39, 20)
        path.lineTo(39, 37)
        path.lineTo(9, 37)
        path.closeSubpath()
        fl = QColor(c)
        fl.setAlpha(45)
        p.setBrush(fl)
        p.drawPath(path)
    elif kind == "person":
        p.drawEllipse(P(24, 17), 7, 7)
        path = QPainterPath()
        path.moveTo(10, 40)
        path.cubicTo(10, 28, 38, 28, 38, 40)
        p.drawPath(path)
    elif kind == "trash":
        p.drawLine(P(11, 14), P(37, 14))
        p.drawPolyline(QPolygonF([P(19, 14), P(19, 9), P(29, 9), P(29, 14)]))
        p.drawPolyline(QPolygonF([P(15, 14), P(17, 39), P(31, 39), P(33, 14)]))
        p.drawLine(P(21, 21), P(21, 32))
        p.drawLine(P(27, 21), P(27, 32))
    elif kind == "pin":
        p.save()
        p.translate(24, 24)
        p.rotate(40)
        if fill:
            p.setBrush(c)
        p.drawRoundedRect(QRectF(-5, -17, 10, 15), 2.5, 2.5)
        p.drawLine(P(-9, -2), P(9, -2))
        p.drawLine(P(0, -2), P(0, 16))
        p.restore()
    elif kind == "dots_v":
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(c)
        for y in (12, 24, 36):
            p.drawEllipse(P(24, y), 3.2, 3.2)
    elif kind == "gear":
        p.drawEllipse(P(24, 24), 9, 9)
        for k in range(8):
            a = k * math.pi / 4
            p.drawLine(P(24 + 13 * math.cos(a), 24 + 13 * math.sin(a)),
                       P(24 + 18 * math.cos(a), 24 + 18 * math.sin(a)))
    p.end()
    return pm


def letter_icon(name, size=48):
    """Fallback extension icon: gradient circle with the first letter."""
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
    g = QLinearGradient(0, 0, size, size)
    g.setColorAt(0, QColor("#ff6b7a"))
    g.setColorAt(1, QColor("#a01030"))
    p.setBrush(QBrush(g))
    p.setPen(Qt.PenStyle.NoPen)
    p.drawEllipse(2, 2, size - 4, size - 4)
    f = QFont()
    f.setPixelSize(int(size * 0.5))
    f.setBold(True)
    p.setFont(f)
    p.setPen(QColor("#ffffff"))
    p.drawText(QRectF(0, 0, size, size), Qt.AlignmentFlag.AlignCenter, (name.strip()[:1] or "?").upper())
    p.end()
    return QIcon(pm)


# ---------------------------------------------------------------- start page
START_HTML = """<!doctype html><meta charset=utf-8><title>New Tab</title>
<style>
*{box-sizing:border-box}
html,body{height:100%;margin:0;color:#fff3f4;font-family:-apple-system,"SF Pro Display","Segoe UI Variable Display","Segoe UI",system-ui,sans-serif}
body{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:26px;
background:radial-gradient(900px 560px at 10% 0%,rgba(225,35,65,.30),transparent 62%),
radial-gradient(760px 600px at 100% 100%,rgba(150,15,50,.42),transparent 62%),
linear-gradient(165deg,#220710,#0c0206)}
#clk{text-align:center;animation:rise .8s cubic-bezier(.2,.8,.2,1) backwards}
#time{font-size:84px;font-weight:200;letter-spacing:-3px;line-height:1;color:#fff6f7;text-shadow:0 4px 40px rgba(255,60,85,.35)}
#date{font-size:14px;color:#d9a4ac;margin-top:10px;letter-spacing:.3px}
.brand{display:flex;align-items:center;gap:10px;margin-top:6px;opacity:.9;animation:rise .8s .06s cubic-bezier(.2,.8,.2,1) backwards}
.brand span{font-size:15px;font-weight:600;letter-spacing:.4px;color:#f0cfd4}
.brand svg{width:22px;height:22px}
form{width:min(600px,88vw);animation:rise .8s .12s cubic-bezier(.2,.8,.2,1) backwards}
input{width:100%;padding:15px 22px;font-size:16px;color:#fff3f4;border-radius:16px;outline:none;
border:1px solid rgba(255,255,255,.14);background:rgba(255,255,255,.07);
transition:border-color .25s,box-shadow .25s,background .25s}
input::placeholder{color:#c99aa2}
input:hover{background:rgba(255,255,255,.10)}
input:focus{border-color:rgba(255,110,125,.85);background:rgba(0,0,0,.30);box-shadow:0 0 0 4px rgba(255,77,94,.16)}
.cards{display:flex;gap:12px;flex-wrap:wrap;justify-content:center;padding:0 20px;margin-top:6px}
.card{width:214px;padding:16px 18px;border-radius:18px;background:rgba(255,255,255,.055);border:1px solid rgba(255,255,255,.09);
animation:rise .8s cubic-bezier(.2,.8,.2,1) backwards;transition:transform .3s cubic-bezier(.2,.8,.2,1),background .3s,border-color .3s}
.card:nth-child(1){animation-delay:.2s}.card:nth-child(2){animation-delay:.27s}.card:nth-child(3){animation-delay:.34s}
.card:hover{transform:translateY(-3px);background:rgba(255,255,255,.09);border-color:rgba(255,255,255,.18)}
.lab{font-size:10.5px;letter-spacing:1px;white-space:nowrap;text-transform:uppercase;color:#d9a4ac}
.val{font-size:26px;font-weight:600;margin:7px 0 2px;letter-spacing:-.4px}
.sub{font-size:11.5px;color:#b88a92}
.note{font-size:11px;color:#8f666e;margin-top:-6px;animation:rise .8s .45s ease backwards}
@keyframes rise{from{opacity:0;transform:translateY(14px)}to{opacity:1;transform:none}}
body::before,body::after{content:"";position:fixed;width:70vmax;height:70vmax;border-radius:50%;pointer-events:none;z-index:-1;will-change:transform}
body::before{left:-25vmax;top:-30vmax;background:radial-gradient(circle,rgba(225,29,72,.26),transparent 65%);animation:d1 24s ease-in-out infinite alternate}
body::after{right:-28vmax;bottom:-34vmax;background:radial-gradient(circle,rgba(150,15,45,.4),transparent 65%);animation:d2 30s ease-in-out infinite alternate}
@keyframes d1{to{transform:translate(14vmax,10vmax) scale(1.15)}}
@keyframes d2{to{transform:translate(-12vmax,-8vmax) scale(1.2)}}
body.still::before,body.still::after{animation-play-state:paused;will-change:auto}
@media(prefers-reduced-motion:reduce){*,::before,::after{animation:none!important;transition:none!important}}
</style>
<div id="clk"><div id="time"></div><div id="date"></div></div>
<form action="https://www.google.com/search" method="get"><input name="q" autofocus autocomplete="off" placeholder="Search Google or type a URL"></form>
<div class="brand"><svg viewBox="0 0 48 48" fill="none" stroke="#ff6b7d" stroke-width="3.6" stroke-linecap="round"><circle cx="24" cy="24" r="17"/><ellipse cx="24" cy="24" rx="7.6" ry="17"/><path d="M7 24h34"/></svg><span>LiteBrowser</span></div>
<div class="cards">
<div class="card"><div class="lab">Trackers &amp; ads blocked</div><div class="val" id="b">0</div><div class="sub">all time</div></div>
<div class="card"><div class="lab">Bandwidth saved</div><div class="val" id="d">0 B</div><div class="sub">all time</div></div>
<div class="card"><div class="lab">Time saved</div><div class="val" id="t">0 s</div><div class="sub">all time</div></div>
</div>
<div class="note">Bandwidth and time are estimates based on typical resource sizes.</div>
<script>
function fB(b){var u=['B','KB','MB','GB','TB'],i=0;while(b>=1024&&i<4){b/=1024;i++}return(i?b.toFixed(b<10?2:1):Math.round(b))+' '+u[i]}
function fT(ms){var s=ms/1000;if(s<60)return s.toFixed(1)+' s';var m=s/60;if(m<60)return m.toFixed(1)+' min';return(m/60).toFixed(1)+' h'}
window.setStats=function(s){document.getElementById('b').textContent=s.blocked.toLocaleString();document.getElementById('d').textContent=fB(s.bytes);document.getElementById('t').textContent=fT(s.ms)};
function tick(){var d=new Date(),t=d.toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'}),e=document.getElementById('time');if(e.textContent!==t){e.textContent=t;document.getElementById('date').textContent=d.toLocaleDateString([],{weekday:'long',day:'numeric',month:'long'});}}
tick();(function sched(){var d=new Date();setTimeout(function(){tick();sched()},(60-d.getSeconds())*1000-d.getMilliseconds()+50)})();
setTimeout(function(){document.body.classList.add('still')},5000);
window.setStats(__STATS__);
</script>"""

# ---------------------------------------------------------------- ad blocker
BUILTIN = set("""doubleclick.net googlesyndication.com googleadservices.com google-analytics.com
googletagservices.com adservice.google.com adnxs.com taboola.com outbrain.com criteo.com criteo.net
scorecardresearch.com quantserve.com amazon-adsystem.com moatads.com adsrvr.org rubiconproject.com
pubmatic.com openx.net casalemedia.com advertising.com smartadserver.com 33across.com sharethrough.com
teads.tv adform.net bidswitch.net media.net zedo.com popads.net propellerads.com exoclick.com
hotjar.com mixpanel.com segment.io adcolony.com applovin.com unityads.unity3d.com yieldmanager.com
serving-sys.com mathtag.com turn.com contextweb.com lijit.com sovrn.com indexww.com""".split())

COSMETIC_CSS = (
    "ins.adsbygoogle,.adsbygoogle,[id^='google_ads'],[id^='div-gpt-ad'],.ad-container,.advert,"
    ".ad-banner,[aria-label='Advertisement'],iframe[src*='doubleclick'],"
    "iframe[src*='googlesyndication'],.sponsored-ad,.ad-slot{display:none!important}"
)

R = QWebEngineUrlRequestInfo.ResourceType
# Rough (bytes, milliseconds) a blocked request would typically have cost. Estimates only.
COST = {getattr(R, n): v for n, v in {
    "ResourceTypeScript": (48_000, 140), "ResourceTypeImage": (32_000, 70),
    "ResourceTypeSubFrame": (70_000, 260), "ResourceTypeXhr": (6_000, 90),
    "ResourceTypePing": (500, 40), "ResourceTypeMedia": (600_000, 400),
    "ResourceTypeStylesheet": (18_000, 80), "ResourceTypeFontResource": (30_000, 70),
}.items() if hasattr(R, n)}
DEFAULT_COST = (15_000, 60)


class AdBlock(QWebEngineUrlRequestInterceptor):
    """Blocks sub-resource requests to ad/tracker domains (never the page itself)."""

    def __init__(self):
        super().__init__()
        self.enabled = True
        self.allow = set()                    # sites where the user switched the blocker off
        self.domains = set(BUILTIN)
        self.s_count = self.s_bytes = self.s_ms = 0          # this session
        self.b_count = self.b_bytes = self.b_ms = 0          # lifetime before this session
        self._saved = None
        self.load_file()
        self.load_stats()

    def load_file(self):
        self._cache = {}
        try:
            extra = {l.strip().lower() for l in LIST_FILE.read_text().splitlines() if l.strip()}
            self.domains = set(BUILTIN) | extra
        except OSError:
            pass

    def load_stats(self):
        try:
            d = json.loads(STATS_FILE.read_text())
            self.b_count, self.b_bytes, self.b_ms = int(d["blocked"]), int(d["bytes"]), int(d["ms"])
        except Exception:
            pass

    def snapshot(self):
        return dict(blocked=self.b_count + self.s_count, bytes=self.b_bytes + self.s_bytes,
                    ms=self.b_ms + self.s_ms, sblocked=self.s_count, sbytes=self.s_bytes, sms=self.s_ms)

    def save(self):
        s = self.snapshot()
        data = {"blocked": s["blocked"], "bytes": s["bytes"], "ms": s["ms"]}
        if data == self._saved:
            return
        try:
            DATA.mkdir(parents=True, exist_ok=True)
            STATS_FILE.write_text(json.dumps(data))
            self._saved = data
        except OSError:
            pass

    def reset(self):
        self.s_count = self.s_bytes = self.s_ms = 0
        self.b_count = self.b_bytes = self.b_ms = 0
        self.save()

    def _lookup(self, host):
        for d in NEVER_BLOCK:
            if host == d or host.endswith("." + d):
                return False
        domains = self.domains
        while host:
            if host in domains:
                return True
            host = host.partition(".")[2]
        return False

    def interceptRequest(self, info):
        host = info.requestUrl().host()
        if SIGNIN_COMPAT and host in SIGNIN_HOSTS:     # Google sign-in pages: send a Firefox identity (header only, no state change)
            try:
                info.setHttpHeader(b"User-Agent", FIREFOX_UA.encode())
            except Exception:
                pass
            return
        if not self.enabled:
            return
        rtype = info.resourceType()
        if rtype == R.ResourceTypeMainFrame:
            return
        if self.allow:                                  # blocker switched off for the site you are on
            h = info.firstPartyUrl().host()
            while h:
                if h in self.allow:
                    return
                h = h.partition(".")[2]
        hit = self._cache.get(host)
        if hit is None:
            hit = self._lookup(host.lower())
            if len(self._cache) > 6000:
                self._cache.clear()
            self._cache[host] = hit
        if hit:
            info.block(True)
            b, ms = COST.get(rtype, DEFAULT_COST)
            self.s_count += 1
            self.s_bytes += b
            self.s_ms += ms


def _dpapi(data, protect):
    """Windows DPAPI: encrypt/decrypt bytes so that only the current Windows user can read them."""
    import ctypes
    from ctypes import wintypes

    class BLOB(ctypes.Structure):
        _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]
    buf = ctypes.create_string_buffer(data, len(data))
    src = BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    out = BLOB()
    f = ctypes.windll.crypt32.CryptProtectData if protect else ctypes.windll.crypt32.CryptUnprotectData
    f.argtypes = [ctypes.POINTER(BLOB), ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                  wintypes.DWORD, ctypes.POINTER(BLOB)]
    f.restype = wintypes.BOOL
    if not f(ctypes.byref(src), None, None, None, None, 0, ctypes.byref(out)):
        raise OSError("DPAPI failed")
    try:
        return ctypes.string_at(out.pbData, out.cbData)
    finally:
        ctypes.windll.kernel32.LocalFree.argtypes = [ctypes.c_void_p]
        ctypes.windll.kernel32.LocalFree(ctypes.cast(out.pbData, ctypes.c_void_p))


class CookieJar(QObject):
    """Our own, independent copy of every cookie, so sign-ins survive closing the browser.

    Chromium keeps cookies in its own database and only writes it now and then (and drops cookies that have no expiry
    date when it closes). That is how people end up signed out. This jar records every cookie the moment it is set or
    removed, gives expiry-less 'session' cookies a 30-day life, saves to cookies.json (atomically, a couple of seconds
    after any change and again on exit) and puts everything back into the engine on the next start."""
    SESSION_DAYS = 30

    def __init__(self, store, parent=None):
        super().__init__(parent)
        self.store = store
        self.jar = {}                  # (domain, path, name) -> (value, raw "Set-Cookie" text)
        self._restoring = False
        self._dirty = False
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(2000)
        self._timer.timeout.connect(self.save)
        self._load_file()
        store.cookieAdded.connect(self.on_added)
        store.cookieRemoved.connect(self.on_removed)

    @staticmethod
    def _key(c):
        return (str(c.domain()).lower(), str(c.path()), bytes(c.name()).decode("utf-8", "ignore"))

    def _load_file(self):
        data = {}
        try:
            txt = COOKIE_FILE.read_text(encoding="utf-8")
            if txt.startswith("DPAPI1:"):                    # encrypted with your Windows account (like Chrome does)
                import base64
                txt = _dpapi(base64.b64decode(txt[7:]), False).decode("utf-8")
            data = json.loads(txt)
        except Exception:
            data = {}
        now = time.time()
        for rec in data.get("cookies", []) if isinstance(data, dict) else []:
            try:
                if rec["exp"] > now:
                    self.jar[(rec["d"], rec["p"], rec["n"])] = (rec["v"], rec["raw"], rec["exp"])
            except Exception:
                continue

    def restore(self):
        """Hand every saved cookie back to the engine (call before the first page loads)."""
        self._restoring = True
        n = 0
        try:
            for (d, p, name), (v, raw, exp) in list(self.jar.items()):
                try:
                    cs = QNetworkCookie.parseCookies(raw.encode("utf-8"))
                    if not cs:
                        continue
                    c = cs[0]
                    c.setExpirationDate(QDateTime.fromSecsSinceEpoch(int(exp)))
                    host = d.lstrip(".")
                    self.store.setCookie(c, QUrl(("https://" if c.isSecure() else "http://") + host + (p or "/")))
                    n += 1
                except Exception:
                    continue
        finally:
            self._restoring = False
        try:
            self.store.loadAllCookies()        # also report the cookies Chromium kept itself, so the jar holds everything
        except Exception:
            pass
        return n

    def on_added(self, cookie):
        try:
            c = QNetworkCookie(cookie)
            exp = time.time() + self.SESSION_DAYS * 86400
            if not c.isSessionCookie():
                exp = c.expirationDate().toSecsSinceEpoch()
                if exp <= time.time():                      # the site is deleting it
                    self.jar.pop(self._key(c), None)
                    self._touch()
                    return
            else:
                c.setExpirationDate(QDateTime.fromSecsSinceEpoch(int(exp)))
            raw = bytes(c.toRawForm()).decode("utf-8", "ignore")
            self.jar[self._key(c)] = (bytes(c.value()).decode("utf-8", "ignore"), raw, exp)
            if not self._restoring:
                self._touch()
        except Exception:
            pass

    def on_removed(self, cookie):
        try:
            k = self._key(cookie)
            cur = self.jar.get(k)
            if cur is not None and cur[0] == bytes(cookie.value()).decode("utf-8", "ignore"):   # (an overwrite reports the OLD value)
                del self.jar[k]
                self._touch()
        except Exception:
            pass

    def _touch(self):
        self._dirty = True
        if not self._timer.isActive():
            self._timer.start()

    def save(self):
        if not self._dirty:
            return
        self._dirty = False
        try:
            now = time.time()
            rows = [{"d": d, "p": p, "n": n, "v": v, "raw": raw, "exp": exp}
                    for (d, p, n), (v, raw, exp) in self.jar.items() if exp > now]
            DATA.mkdir(parents=True, exist_ok=True)
            tmp = COOKIE_FILE.with_suffix(".tmp")
            txt = json.dumps({"cookies": rows})
            if sys.platform == "win32":                      # only your Windows account can read the saved sign-ins
                try:
                    import base64
                    txt = "DPAPI1:" + base64.b64encode(_dpapi(txt.encode("utf-8"), True)).decode("ascii")
                except Exception:
                    pass
            tmp.write_text(txt, encoding="utf-8")
            os.replace(tmp, COOKIE_FILE)
        except Exception:
            pass

    def clear(self):
        self.jar.clear()
        self._dirty = True
        self.save()

    def count(self):
        return len(self.jar)


class SelfUpdater(QObject):
    """Checks UPDATE_URL for a newer litebrowser4.py and installs it (applied on next start)."""
    result = pyqtSignal(str, str)        # status: "new" | "same" | "error" | "off", detail

    @staticmethod
    def url():
        return (os.environ.get("LITEBROWSER_UPDATE_URL") or load_json(PREFS_FILE, {}).get("update_url")
                or UPDATE_URL or "").strip()

    def run(self):
        url = self.url()
        if not url:
            self.result.emit("off", "")
            return

        def work():
            from urllib.request import Request, urlopen
            try:
                data = urlopen(Request(url, headers={"User-Agent": "LiteBrowser"}), timeout=25).read()
                text = data.decode("utf-8")
                new = _ver(text)
                if not new:
                    raise ValueError("no APP_VERSION in the downloaded file")
                if new <= _ver('APP_VERSION = "%s"' % APP_VERSION):
                    self.result.emit("same", "")
                    return
                if len(data) < 50000 or "class Browser" not in text:
                    raise ValueError("downloaded file does not look like LiteBrowser")
                compile(text, "litebrowser_update", "exec")          # refuse anything that is not valid Python
                label = ".".join(map(str, new))
                if getattr(sys, "frozen", False):
                    DATA.mkdir(parents=True, exist_ok=True)
                    tmp = UPDATE_FILE.with_suffix(".tmp")
                    tmp.write_bytes(data)
                    os.replace(tmp, UPDATE_FILE)
                else:
                    me = Path(__file__).resolve()
                    tmp = me.with_suffix(".new")
                    tmp.write_bytes(data)
                    try:
                        shutil.copy2(me, me.with_suffix(".bak"))      # one-step rollback: rename .bak back
                    except Exception:
                        pass
                    os.replace(tmp, me)
                self.result.emit("new", label)
            except Exception as e:
                self.result.emit("error", str(e)[:80])
        threading.Thread(target=work, daemon=True).start()


class Updater(QObject):
    done = pyqtSignal(int, str)

    def run(self):
        def work():
            from urllib.request import Request, urlopen
            try:
                req = Request(LIST_URL, headers={"User-Agent": "LiteBrowser"})
                text = urlopen(req, timeout=20).read().decode("utf-8", "ignore")
                names = set()
                for line in text.splitlines():
                    line = line.split("#")[0].strip()
                    if line:
                        d = line.split()[-1].lower()
                        if "." in d and "/" not in d and d not in ("localhost", "local"):
                            names.add(d)
                DATA.mkdir(parents=True, exist_ok=True)
                LIST_FILE.write_text("\n".join(sorted(names)))
                self.done.emit(len(names), "")
            except Exception as e:
                self.done.emit(0, str(e))
        threading.Thread(target=work, daemon=True).start()


def crx_to_zip(data):
    if data[:4] != b"Cr24":
        raise ValueError("download was not a CRX file")
    ver = int.from_bytes(data[4:8], "little")
    if ver == 3:
        hl = int.from_bytes(data[8:12], "little")
        return data[12 + hl:]
    if ver == 2:
        pk = int.from_bytes(data[8:12], "little")
        sg = int.from_bytes(data[12:16], "little")
        return data[16 + pk + sg:]
    raise ValueError(f"unsupported CRX version {ver}")


def store_ext_id(url):
    if url.host().lower() not in ("chromewebstore.google.com", "chrome.google.com"):
        return None
    m = re.search(r"/detail/(?:[^/]+/)?([a-p]{32})(?:/|$)", url.path())
    return m.group(1) if m else None


class Installer(QObject):
    """Downloads a Chrome Web Store extension (CRX) and unpacks it into the extensions folder."""
    done = pyqtSignal(str, str, str)

    def run(self, eid):
        def work():
            import io
            import zipfile
            from urllib.request import Request, urlopen
            try:
                dest = EXT_DIR / eid
                if dest.exists():
                    self.done.emit(eid, "", "Already installed")
                    return
                url = ("https://clients2.google.com/service/update2/crx?response=redirect"
                       "&prodversion=130.0.6723.70&acceptformat=crx2,crx3&x=id%3D" + eid + "%26uc")
                data = urlopen(Request(url, headers={"User-Agent": UA}), timeout=45).read()
                tmp = EXT_DIR / (eid + ".tmp")
                shutil.rmtree(tmp, ignore_errors=True)
                with zipfile.ZipFile(io.BytesIO(crx_to_zip(data))) as z:
                    z.extractall(tmp)
                man = json.loads((tmp / "manifest.json").read_text(encoding="utf-8-sig"))
                if man.get("manifest_version") != 3:
                    shutil.rmtree(tmp, ignore_errors=True)
                    self.done.emit(eid, "", "this extension uses Manifest V2, which Qt can't load")
                    return
                tmp.rename(dest)
                self.done.emit(eid, str(dest), "")
            except Exception as e:
                self.done.emit(eid, "", str(e))
        threading.Thread(target=work, daemon=True).start()


def load_ext_ui():
    try:
        d = json.loads(EXT_UI_FILE.read_text(encoding="utf-8"))
        return {"pinned": [str(x) for x in d.get("pinned", [])]}
    except Exception:
        return {"pinned": []}


class ExtPage(QWebEnginePage):
    def __init__(self, profile, browser, parent):
        super().__init__(profile, parent)
        self.browser = browser

    def javaScriptConsoleMessage(self, level, message, line, source):
        pass

    def createWindow(self, _t):
        return self.browser.add_tab("").page()


class ExtPopup(QFrame):
    """Hosts an extension's action popup (like clicking its toolbar icon in Chrome)."""

    def __init__(self, browser, url):
        super().__init__(browser, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.NoDropShadowWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setObjectName("extpanel")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(10, 10, 10, 10)
        self.view = QWebEngineView(self)
        page = ExtPage(browser.profile, browser, self.view)
        page.windowCloseRequested.connect(self.close)
        self.view.setPage(page)
        lay.addWidget(self.view)
        self.resize(380, 520)
        self.view.setUrl(url)

    def paintEvent(self, e):
        paint_glass(self, 18, (48, 8, 18, 250))

    def showEvent(self, e):
        super().showEvent(e)
        fade_in_window(self)


class ExtPanel(QFrame):
    """Chrome-style 'Extensions' dropdown: list, pin toggle, per-extension menu, manage."""

    def __init__(self, browser):
        super().__init__(browser, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.NoDropShadowWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setObjectName("extpanel")
        self.b = browser
        self.setFixedWidth(360)
        self.lay = QVBoxLayout(self)
        self.lay.setContentsMargins(10, 10, 10, 10)
        self.lay.setSpacing(2)
        self.build()

    def paintEvent(self, e):
        paint_glass(self, 18, (48, 8, 18, 250))

    def showEvent(self, e):
        super().showEvent(e)
        fade_in_window(self)

    def build(self):
        b = self.b
        while self.lay.count():
            w = self.lay.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()

        head = QWidget()
        hl = QHBoxLayout(head)
        hl.setContentsMargins(8, 2, 0, 6)
        hl.addWidget(QLabel("Extensions", objectName="exttitle"))
        hl.addStretch(1)
        x = HoverButton(objectName="flat")
        x.setIcon(QIcon(pm_icon("close", width=4)))
        x.setIconSize(QSize(16, 16))
        x.setFixedSize(30, 30)
        x.clicked.connect(self.close)
        hl.addWidget(x)
        self.lay.addWidget(head)

        fm = QFontMetrics(QFont(self.font().family(), 10))
        exts = b.ext_list()
        if b.ext_mgr is None:
            self.lay.addWidget(QLabel("Extensions need Qt 6.10+.\npip install -U PyQt6 PyQt6-WebEngine",
                                      objectName="extmuted"))
        elif not exts:
            self.lay.addWidget(QLabel("No extensions yet. Add an unpacked\nManifest V3 extension folder below.",
                                      objectName="extmuted"))
        pinned = set(b.ext_ui["pinned"])
        for info in exts:
            eid = info.id()
            row = HoverRow(base=0, hi=24, radius=12, objectName="extrow")
            h = QHBoxLayout(row)
            h.setContentsMargins(10, 6, 6, 6)
            h.setSpacing(10)
            ic = QLabel()
            ic.setPixmap(b.ext_icon(info).pixmap(QSize(24, 24)))
            ic.setFixedSize(26, 26)
            h.addWidget(ic)
            name = info.name() or eid
            lab = QLabel(fm.elidedText(name, Qt.TextElideMode.ElideRight, 190), objectName="extname")
            lab.setToolTip(name)
            if not info.isEnabled():
                lab.setStyleSheet("color:#8a6a70;")
            h.addWidget(lab, 1)
            pin = HoverButton(objectName="flat")
            on = eid in pinned
            pin.setIcon(QIcon(pm_icon("pin", "#ff8f9c" if on else "#d9a4ac", fill=on, width=3.2)))
            pin.setIconSize(QSize(18, 18))
            pin.setFixedSize(30, 30)
            pin.setToolTip("Unpin from toolbar" if on else "Pin to toolbar")
            pin.clicked.connect(lambda _=False, e=eid: (b.toggle_pin(e), self.build()))
            h.addWidget(pin)
            d = HoverButton(objectName="flat")
            d.setIcon(QIcon(pm_icon("dots_v", "#d9a4ac")))
            d.setIconSize(QSize(18, 18))
            d.setFixedSize(30, 30)
            d.clicked.connect(lambda _=False, e=eid, bt=d: b.ext_menu(e, bt.mapToGlobal(bt.rect().bottomLeft())))
            h.addWidget(d)
            self.lay.addWidget(row)

        self.lay.addWidget(QFrame(objectName="extsep"))
        for kind, text, fn in [("plus", "Add extension…", lambda: (self.close(), b.add_tab(STORE_URL))),
                               ("gear", "Manage extensions", lambda: (self.close(), b.show_settings()))]:
            r = HoverRow(base=0, hi=30, radius=12)
            r.setCursor(Qt.CursorShape.PointingHandCursor)
            h = QHBoxLayout(r)
            h.setContentsMargins(12, 10, 12, 10)
            h.setSpacing(12)
            ic = QLabel()
            ic.setPixmap(QIcon(pm_icon(kind, "#fbe6e8", width=3.4)).pixmap(QSize(18, 18)))
            ic.setFixedSize(20, 20)
            h.addWidget(ic)
            h.addWidget(QLabel(text, objectName="extname"), 1)
            r.clicked.connect(fn)
            self.lay.addWidget(r)
        self.adjustSize()


class SettingsWindow(QFrame):
    """'Manage extensions' settings: every installed extension with an on/off switch."""

    def __init__(self, browser):
        super().__init__(browser, Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setObjectName("settings")
        self.b = browser
        self._drag = None
        self.resize(600, 660)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(24, 20, 24, 22)
        outer.setSpacing(10)

        head = QHBoxLayout()
        head.addWidget(QLabel("Extensions", objectName="settitle"))
        head.addStretch(1)
        x = HoverButton(objectName="flat")
        x.setIcon(QIcon(pm_icon("close", width=4)))
        x.setIconSize(QSize(16, 16))
        x.setFixedSize(32, 32)
        x.clicked.connect(self.close)
        head.addWidget(x)
        outer.addLayout(head)
        self.sub = QLabel("", objectName="extmuted")
        self.sub.setContentsMargins(0, 0, 0, 0)
        self.sub.setStyleSheet("padding:0;")
        outer.addWidget(self.sub)

        actions = QHBoxLayout()
        actions.setSpacing(8)
        for text, fn in [("Add from Web Store", lambda: (self.close(), browser.add_tab(STORE_URL))),
                         ("Load unpacked…", browser.add_extension),
                         ("Open folder", lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(str(EXT_DIR))))]:
            c = HoverButton(objectName="chip")
            c.setText(text)
            c.setFixedHeight(30)
            c.setCursor(Qt.CursorShape.PointingHandCursor)
            c.clicked.connect(lambda _=False, f=fn: f())
            actions.addWidget(c)
        actions.addStretch(1)
        outer.addLayout(actions)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.content = QWidget()
        self.cl = QVBoxLayout(self.content)
        self.cl.setContentsMargins(0, 4, 4, 0)
        self.cl.setSpacing(8)
        scroll.setWidget(self.content)
        outer.addWidget(scroll, 1)
        self.build(animate=True)

    def paintEvent(self, e):
        paint_glass(self, 22)

    def showEvent(self, e):
        super().showEvent(e)
        fade_in_window(self, 220, 14)
        self.activateWindow()
        self.setFocus()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and e.position().y() < 64:
            self._drag = e.globalPosition().toPoint() - self.frameGeometry().topLeft()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._drag is not None and e.buttons() & Qt.MouseButton.LeftButton:
            self.move(e.globalPosition().toPoint() - self._drag)
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._drag = None
        super().mouseReleaseEvent(e)

    def build(self, animate=False):
        b = self.b
        while self.cl.count():
            w = self.cl.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        exts = b.ext_list()
        if b.ext_mgr is None:
            self.sub.setText("Extensions need Qt 6.10+  (pip install -U PyQt6 PyQt6-WebEngine)")
        else:
            self.sub.setText(f"{len(exts)} installed")
        if not exts:
            self.cl.addWidget(QLabel("Nothing here yet.\nUse “Add from Web Store” or “Load unpacked…”.",
                                     objectName="extmuted"))
        fm = QFontMetrics(QFont(self.font().family(), 9))
        for i, info in enumerate(exts):
            eid = info.id()
            row = HoverRow(base=16, hi=28, radius=16)
            h = QHBoxLayout(row)
            h.setContentsMargins(14, 12, 12, 12)
            h.setSpacing(12)
            ic = QLabel()
            ic.setPixmap(b.ext_icon(info).pixmap(QSize(36, 36)))
            ic.setFixedSize(38, 38)
            h.addWidget(ic)
            colv = QVBoxLayout()
            colv.setSpacing(2)
            name = info.name() or eid
            nl = QLabel(name, objectName="extname")
            man = b.ext_manifest(info)
            desc = ""
            try:
                desc = info.description() or ""
            except Exception:
                pass
            if not desc or desc.startswith("__MSG"):
                desc = man.get("description", "")
            if desc.startswith("__MSG"):
                desc = ""
            meta = f"v{man.get('version', '?')}" + (f"  ·  {desc}" if desc else "")
            ml = QLabel(fm.elidedText(meta, Qt.TextElideMode.ElideRight, 320), objectName="extmeta")
            ml.setToolTip(f"{name}\n{desc}\nID: {eid}")
            colv.addWidget(nl)
            colv.addWidget(ml)
            h.addLayout(colv, 1)

            tg = Toggle(info.isEnabled())

            def dim(on, lab=nl):
                lab.setStyleSheet("" if on else "color:#8a6a70;")
            dim(info.isEnabled())
            tg.toggled.connect(lambda on, e=eid, d=dim: (d(on), b.set_ext_enabled(e, on, False)))
            h.addWidget(tg)
            rm = HoverButton(objectName="flat")
            rm.setIcon(QIcon(pm_icon("trash", "#ff9aa5", width=3.2)))
            rm.setIconSize(QSize(18, 18))
            rm.setFixedSize(34, 34)
            rm.setToolTip("Remove extension")
            rm.setCursor(Qt.CursorShape.PointingHandCursor)
            rm.clicked.connect(lambda _=False, e=eid: b.remove_ext(e))
            h.addWidget(rm)
            self.cl.addWidget(row)
            if animate:
                fade_widget(row, delay=70 + i * 50)
        self.cl.addStretch(1)


class Page(QWebEnginePage):
    def __init__(self, profile, browser):
        super().__init__(profile, browser)
        self.browser = browser

    def javaScriptConsoleMessage(self, level, message, line, source):
        pass                             # a site's own console output is not for the user (it used to flood the terminal)

    def createWindow(self, _type):
        bg = _type == QWebEnginePage.WebWindowType.WebBrowserBackgroundTab     # ctrl/middle-click on a link
        try:
            opener = self.view()
        except Exception:
            opener = None
        return self.browser.add_tab("", background=bg, after_current=True, opener=opener).page()


def paint_glass(w, radius=22, fill=(40, 7, 16, 250)):
    """Paint a window's rounded glass background ourselves (does not rely on the style sheet)."""
    p = QPainter(w)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setBrush(QColor(*fill))
    p.setPen(QPen(QColor(255, 255, 255, 70), 1))
    p.drawRoundedRect(QRectF(w.rect()).adjusted(0.5, 0.5, -0.5, -0.5), radius, radius)
    p.end()


def fade_widget(w, delay=0, dur=260):
    """Fade a small widget in (opacity effect is removed afterwards so it costs nothing)."""
    eff = QGraphicsOpacityEffect(w)
    eff.setOpacity(0.0)
    w.setGraphicsEffect(eff)
    a = QPropertyAnimation(eff, b"opacity", w)
    a.setDuration(dur)
    a.setStartValue(0.0)
    a.setEndValue(1.0)
    a.setEasingCurve(QEasingCurve.Type.OutCubic)
    a.finished.connect(lambda: w.setGraphicsEffect(None))

    def go():
        try:
            a.start()
        except RuntimeError:
            pass
    QTimer.singleShot(delay, go)


def fade_in_window(w, dur=180, slide=10):
    """Fade (and slightly slide down) a top-level popup/dialog when it appears."""
    if getattr(w, "_faded", False):
        return
    w._faded = True
    end = w.pos()
    w.setWindowOpacity(0.0)
    grp = QParallelAnimationGroup(w)
    a = QPropertyAnimation(w, b"windowOpacity", w)
    a.setDuration(dur)
    a.setStartValue(0.0)
    a.setEndValue(1.0)
    a.setEasingCurve(QEasingCurve.Type.OutCubic)
    grp.addAnimation(a)
    if slide:
        w.move(end - QPoint(0, slide))
        m = QPropertyAnimation(w, b"pos", w)
        m.setDuration(dur + 40)
        m.setStartValue(end - QPoint(0, slide))
        m.setEndValue(end)
        m.setEasingCurve(QEasingCurve.Type.OutCubic)
        grp.addAnimation(m)
    grp.start()
    w._anim = grp


# (idle bg alpha, hover bg alpha, idle border alpha, hover border alpha)
BTN_ALPHA = {"nav": (0, 30, 0, 0), "shield": (14, 40, 26, 60),
             "chip": (0, 30, 0, 0), "flat": (0, 30, 0, 0)}


class HoverButton(QToolButton):
    """Glass button whose background smoothly fades on hover/press."""

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self._h = 0.0
        self._anim = QPropertyAnimation(self, b"hover", self)
        self._anim.setDuration(150)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._pulse = QPropertyAnimation(self, b"hover", self)
        self._pulse.setDuration(650)
        self._pulse.setEasingCurve(QEasingCurve.Type.OutCubic)

    def _get_h(self):
        return self._h

    def _set_h(self, v):
        self._h = v
        self.update()

    hover = pyqtProperty(float, _get_h, _set_h)

    def _go(self, end):
        self._pulse.stop()
        self._anim.stop()
        self._anim.setStartValue(self._h)
        self._anim.setEndValue(end)
        self._anim.start()

    def pulse(self):
        self._anim.stop()
        self._pulse.stop()
        self._pulse.setStartValue(1.0)
        self._pulse.setEndValue(0.0)
        self._pulse.start()

    def enterEvent(self, e):
        self._go(1.0)
        super().enterEvent(e)

    def leaveEvent(self, e):
        self._go(0.0)
        super().leaveEvent(e)

    def paintEvent(self, e):
        a0, a1, b0, b1 = BTN_ALPHA.get(self.objectName(), (0, 0, 0, 0))
        h = self._h
        a = a0 + (a1 - a0) * h + (34 if self.isDown() else 0)
        bd = b0 + (b1 - b0) * h
        if a > 0 or bd > 0:
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
            p.setBrush(QColor(255, 255, 255, int(min(a, 255))))
            p.setPen(QPen(QColor(255, 255, 255, int(bd)), 1) if bd > 0 else Qt.PenStyle.NoPen)
            rad = 10 if self.objectName() in ("nav", "flat") else r.height() / 2
            p.drawRoundedRect(r, rad, rad)
            p.end()
        super().paintEvent(e)


class HoverRow(QFrame):
    """Row/card with a hover glow that fades in and out; emits clicked."""
    clicked = pyqtSignal()

    def __init__(self, *a, base=0, hi=26, radius=12, **kw):
        super().__init__(*a, **kw)
        self._h = 0.0
        self._base, self._hi, self._r = base, hi, radius
        self._anim = QPropertyAnimation(self, b"hover", self)
        self._anim.setDuration(160)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)

    def _get_h(self):
        return self._h

    def _set_h(self, v):
        self._h = v
        self.update()

    hover = pyqtProperty(float, _get_h, _set_h)

    def _go(self, end):
        self._anim.stop()
        self._anim.setStartValue(self._h)
        self._anim.setEndValue(end)
        self._anim.start()

    def enterEvent(self, e):
        self._go(1.0)
        super().enterEvent(e)

    def leaveEvent(self, e):
        self._go(0.0)
        super().leaveEvent(e)

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and self.rect().contains(e.position().toPoint()):
            self.clicked.emit()
        super().mouseReleaseEvent(e)

    def paintEvent(self, e):
        a = self._base + (self._hi - self._base) * self._h
        if a > 0:
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            p.setBrush(QColor(255, 255, 255, int(a)))
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRoundedRect(QRectF(self.rect()), self._r, self._r)
            p.end()
        super().paintEvent(e)


class Toggle(QAbstractButton):
    """iOS-style switch with a sliding knob."""

    def __init__(self, on=False, parent=None):
        super().__init__(parent)
        self.setCheckable(True)
        self.setChecked(on)
        self._t = 1.0 if on else 0.0
        self.setFixedSize(46, 26)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._anim = QPropertyAnimation(self, b"knob", self)
        self._anim.setDuration(200)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self.toggled.connect(self._go)

    def _get_t(self):
        return self._t

    def _set_t(self, v):
        self._t = v
        self.update()

    knob = pyqtProperty(float, _get_t, _set_t)

    def _go(self, on):
        self._anim.stop()
        self._anim.setStartValue(self._t)
        self._anim.setEndValue(1.0 if on else 0.0)
        self._anim.start()

    def paintEvent(self, e):
        t = self._t
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        track = QColor(int(255), int(255 + (77 - 255) * t), int(255 + (94 - 255) * t), int(55 + 200 * t))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(track)
        p.drawRoundedRect(QRectF(0, 1, 46, 24), 12, 12)
        p.setBrush(QColor(0, 0, 0, 50))
        x = 13 + 20 * t
        p.drawEllipse(QPointF(x, 13.8), 10, 10)
        p.setBrush(QColor("#ffffff"))
        p.drawEllipse(QPointF(x, 13), 10, 10)
        p.end()


class GlassMenu(QMenu):
    def __init__(self, *a):
        super().__init__(*a)
        self.setWindowFlags(self.windowFlags() | Qt.WindowType.FramelessWindowHint
                            | Qt.WindowType.NoDropShadowWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)

    def showEvent(self, e):
        super().showEvent(e)
        self._faded = False
        fade_in_window(self, 170, 8)


class Collapser(QObject):
    """Smoothly expands/collapses a bar by animating its maximum height."""

    def __init__(self, widget, full, shown=True, dur=240):
        super().__init__(widget)
        self.w, self.full, self.shown = widget, full, shown
        widget.setMinimumHeight(0)
        widget.setMaximumHeight(full if shown else 0)
        widget.setVisible(shown)
        self.anim = QPropertyAnimation(widget, b"maximumHeight", self)
        self.anim.setDuration(dur)
        self.anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self.anim.finished.connect(lambda: self.w.setVisible(self.shown))

    def set(self, show, animate=True):
        if show == self.shown:
            return
        self.shown = show
        target = self.full if show else 0
        if not animate:
            self.w.setMaximumHeight(target)
            self.w.setVisible(show)
            return
        self.w.setVisible(True)
        self.anim.stop()
        self.anim.setStartValue(self.w.maximumHeight())
        self.anim.setEndValue(target)
        self.anim.start()


def style_menu(m):
    m.setWindowFlags(m.windowFlags() | Qt.WindowType.FramelessWindowHint | Qt.WindowType.NoDropShadowWindowHint)
    m.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
    return m


def glass_menu(parent):
    return GlassMenu(parent)


class Chip(HoverButton):
    """Bookmark-bar button; middle-click opens in a new tab."""
    middle = pyqtSignal()

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.MiddleButton and self.rect().contains(e.position().toPoint()):
            self.middle.emit()
            e.accept()
            return
        super().mouseReleaseEvent(e)


def is_folder(b):
    return "children" in b


def bm_walk(items):
    for b in items:
        if is_folder(b):
            yield from bm_walk(b["children"])
        else:
            yield b


def clean_bm(items):
    out = []
    for b in items or []:
        if not isinstance(b, dict):
            continue
        if "children" in b or b.get("folder"):
            f = {"title": str(b.get("title") or "Folder"), "folder": True, "children": clean_bm(b.get("children"))}
            if b.get("src"):
                f["src"] = str(b["src"])
            out.append(f)
        elif "url" in b:
            out.append({"title": str(b.get("title") or b["url"]), "url": b["url"]})
    return out


def load_bookmarks():
    try:
        d = json.loads(BM_FILE.read_text(encoding="utf-8"))
        return {"show": bool(d.get("show", True)), "items": clean_bm(d.get("items", []))}
    except Exception:
        return {"show": True, "items": []}


PREFS_FILE = DATA / "prefs.json"
GSYNC_FILE = DATA / "google_sync.json"
DESKTOP_ID = "litebrowser.desktop"
SERVER_NAME = "LiteBrowserInstance"
APP_ICON_PATH = None


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception:
        return default


def save_json(path, obj):
    try:
        DATA.mkdir(parents=True, exist_ok=True)
        Path(path).write_text(json.dumps(obj, indent=1), encoding="utf-8")
    except OSError:
        pass


def load_gsync():
    d = load_json(GSYNC_FILE, {})
    return {"accounts": d.get("accounts", {}) if isinstance(d.get("accounts"), dict) else {}, "last": d.get("last")}


# ---- app icon -------------------------------------------------------------------
def make_app_icon(size=256):
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    g = QLinearGradient(0, 0, size, size)
    g.setColorAt(0, QColor("#ff5a6e"))
    g.setColorAt(1, QColor("#7a0f2a"))
    p.setBrush(QBrush(g))
    p.setPen(Qt.PenStyle.NoPen)
    p.drawRoundedRect(QRectF(8, 8, size - 16, size - 16), size * 0.24, size * 0.24)
    hl = QLinearGradient(0, 0, 0, size * 0.55)
    hl.setColorAt(0, QColor(255, 255, 255, 95))
    hl.setColorAt(1, QColor(255, 255, 255, 0))
    p.setBrush(QBrush(hl))
    p.drawRoundedRect(QRectF(8, 8, size - 16, size * 0.55), size * 0.24, size * 0.24)
    p.setPen(QPen(QColor(255, 255, 255, 235), size * 0.045, Qt.PenStyle.SolidLine,
                  Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
    p.setBrush(Qt.BrushStyle.NoBrush)
    c, r = size / 2, size * 0.27
    p.drawEllipse(QPointF(c, c), r, r)
    p.drawEllipse(QPointF(c, c), r * 0.45, r)
    p.drawLine(QPointF(c - r, c), QPointF(c + r, c))
    p.end()
    return pm


# ---- default browser ---------------------------------------------------------------
def launch_command():
    if getattr(sys, "frozen", False):      # running as LiteBrowser.exe
        return sys.executable, None
    exe = sys.executable
    if sys.platform == "win32":
        pyw = Path(exe).with_name("pythonw.exe")
        if pyw.exists():
            exe = str(pyw)
    return exe, os.path.abspath(__file__)


def is_default_browser():
    try:
        if sys.platform == "win32":
            import winreg
            for proto in ("https", "http"):
                key = rf"Software\Microsoft\Windows\Shell\Associations\UrlAssociations\{proto}\UserChoice"
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER, key) as k:
                    if not str(winreg.QueryValueEx(k, "ProgId")[0]).startswith("LiteBrowser"):
                        return False
            return True
        if sys.platform.startswith("linux"):
            r = subprocess.run(["xdg-settings", "get", "default-web-browser"],
                               capture_output=True, text=True, timeout=3)
            return r.stdout.strip() == DESKTOP_ID
    except Exception:
        pass
    return False


def set_default_browser(icon):
    """Registers LiteBrowser with the OS and takes the user to the place where they confirm it."""
    exe, script = launch_command()
    if sys.platform == "win32":
        try:
            import winreg
            import ctypes
            hk = winreg.HKEY_CURRENT_USER
            frozen = getattr(sys, "frozen", False)
            icon_val = f"{exe},0" if (frozen or not icon) else f"{icon},0"
            extra = f' "{script}"' if script else ""
            cmd = f'"{exe}"{extra} "%1"'

            def put(path, name, value):
                with winreg.CreateKeyEx(hk, path, 0, winreg.KEY_WRITE) as k:
                    winreg.SetValueEx(k, name, 0, winreg.REG_SZ, value)
            for progid, desc, is_url in (("LiteBrowserURL", "LiteBrowser URL", True),
                                         ("LiteBrowserHTML", "LiteBrowser Document", False)):
                base = rf"Software\Classes\{progid}"
                put(base, "", desc)
                if is_url:
                    put(base, "URL Protocol", "")
                put(base + r"\DefaultIcon", "", icon_val)
                put(base + r"\shell\open\command", "", cmd)
            smi = r"Software\Clients\StartMenuInternet\LiteBrowser"
            put(smi, "", "LiteBrowser")
            put(smi + r"\DefaultIcon", "", icon_val)
            put(smi + r"\shell\open\command", "", f'"{exe}"{extra}')
            cap = smi + r"\Capabilities"
            put(cap, "ApplicationName", "LiteBrowser")
            put(cap, "ApplicationDescription", "Light, fast Chromium-based browser")
            put(cap, "ApplicationIcon", icon_val)
            for proto in ("http", "https"):
                put(cap + r"\URLAssociations", proto, "LiteBrowserURL")
            for ext in (".htm", ".html", ".xhtml"):
                put(cap + r"\FileAssociations", ext, "LiteBrowserHTML")
            put(r"Software\RegisteredApplications", "LiteBrowser", cap)
            try:
                ctypes.windll.shell32.SHChangeNotify(0x08000000, 0, None, None)
            except Exception:
                pass
            for uri in ("ms-settings:defaultapps?registeredAppUser=LiteBrowser", "ms-settings:defaultapps"):
                try:
                    os.startfile(uri)
                    break
                except OSError:
                    continue
            return "Windows needs you to confirm: pick LiteBrowser under “Web browser” in the Settings window."
        except Exception as e:
            return "Couldn't register as a browser: " + str(e)[:80]
    if sys.platform.startswith("linux"):
        try:
            d = Path.home() / ".local" / "share" / "applications"
            d.mkdir(parents=True, exist_ok=True)
            (d / DESKTOP_ID).write_text(
                "[Desktop Entry]\nVersion=1.0\nType=Application\nName=LiteBrowser\n"
                f'Exec="{exe}"{" " + chr(34) + script + chr(34) if script else ""} %U\nIcon={icon or "web-browser"}\nTerminal=false\n'
                "Categories=Network;WebBrowser;\nMimeType=text/html;x-scheme-handler/http;x-scheme-handler/https;\n",
                encoding="utf-8")
            subprocess.run(["xdg-settings", "set", "default-web-browser", DESKTOP_ID], timeout=5)
            return "LiteBrowser is now your default browser."
        except Exception as e:
            return "Couldn't set default browser: " + str(e)[:80]
    return "Setting a default browser on this OS needs LiteBrowser packaged as an app."


def create_shortcuts(icon, desktop=True):
    """Windows: Start Menu (+ Desktop) shortcuts that start LiteBrowser through pythonw (no console window).
    Windows only lets the user pin an app to the taskbar, so these are what you right-click to pin."""
    if sys.platform != "win32":
        return []
    exe, script = launch_command()

    def q(t):
        return str(t).replace("'", "''")
    ps = ("$ws = New-Object -ComObject WScript.Shell; "
          "$paths = @(Join-Path ([Environment]::GetFolderPath('Programs')) 'LiteBrowser.lnk'); ")
    if desktop:
        ps += "$paths += Join-Path ([Environment]::GetFolderPath('Desktop')) 'LiteBrowser.lnk'; "
    ps += ("foreach ($p in $paths) { $s = $ws.CreateShortcut($p); "
           f"$s.TargetPath = '{q(exe)}'; $s.Arguments = '{(chr(34) + q(script) + chr(34)) if script else ''}'; "
           f"$s.WorkingDirectory = '{q(os.path.dirname(script or exe))}'; "
           f"$s.IconLocation = '{q(exe if (getattr(sys, 'frozen', False) or not icon) else icon)},0'; $s.Description = 'LiteBrowser'; "
           "$s.Save(); Write-Output $p }")
    try:
        r = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass", "-Command", ps],
                           capture_output=True, text=True, timeout=30, creationflags=0x08000000)
        return [l.strip() for l in r.stdout.splitlines() if l.strip().lower().endswith(".lnk")]
    except Exception:
        return []


_IPV4 = re.compile(r"^\d{1,3}(\.\d{1,3}){3}(:\d+)?([/?#].*)?$")
_HOSTPORT = re.compile(r"^[A-Za-z0-9-]+:\d{2,5}([/?#].*)?$")
_DOMAIN = re.compile(r"^([A-Za-z0-9-]+\.)+[A-Za-z]{2,}(:\d+)?([/?#].*)?$")


def guess_url(text):
    """What the user most likely meant: a file, a local server (http), a website (https) or a search."""
    t = (text or "").strip().strip('"')
    if not t:
        return ""
    if (os.path.isabs(t) or "\\" in t or "/" in t or t.startswith(".")) and os.path.exists(t):
        return QUrl.fromLocalFile(os.path.abspath(t)).toString()
    if "://" in t or t.startswith(("about:", "chrome:", "data:", "file:", "view-source:")):
        return t
    if " " not in t:
        bare = t.split("/")[0].split("?")[0].split("#")[0].split(":")[0].lower()
        if bare == "localhost" or bare.endswith(".local") or _IPV4.match(t) or _HOSTPORT.match(t):
            return "http://" + t
        if _DOMAIN.match(t):
            return "https://" + t
    return SEARCH + QUrl.toPercentEncoding(t).data().decode()


def normalize_arg(a):
    return guess_url(a)


def send_to_running(arg):
    """If LiteBrowser is already running, hand it the URL and tell the caller to exit."""
    sock = QLocalSocket()
    sock.connectToServer(SERVER_NAME)
    if sock.waitForConnected(400):
        sock.write((arg + "\n").encode("utf-8"))
        sock.flush()
        sock.waitForBytesWritten(400)
        answered = sock.waitForReadyRead(2500)            # a healthy window answers at once; a stuck leftover process never does
        sock.disconnectFromServer()
        return bool(answered)
    return False


def on_instance_connection(server, win):
    sock = server.nextPendingConnection()
    if sock is None:
        return

    def read():
        data = bytes(sock.readAll()).decode("utf-8", "ignore").strip()
        win.open_external(data)
        try:
            sock.write(b"ok\n")
            sock.flush()
        except Exception:
            pass
        sock.disconnectFromServer()
    if sock.bytesAvailable():
        read()
    else:
        sock.readyRead.connect(read)


# ---- Google accounts: read the Chrome profiles on this PC ----------------------------
def chrome_user_dir():
    if sys.platform == "win32":
        base = os.environ.get("LOCALAPPDATA")
        return Path(base) / "Google" / "Chrome" / "User Data" if base else None
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Application Support" / "Google" / "Chrome"
    return Path.home() / ".config" / "google-chrome"


def chrome_profiles():
    base = chrome_user_dir()
    if base is None:
        return []
    try:
        cache = json.loads((base / "Local State").read_text(encoding="utf-8")).get("profile", {}).get("info_cache", {})
    except Exception:
        return []
    out = []
    for d, info in cache.items():
        if not (base / d).is_dir():
            continue
        out.append({"dir": d, "path": str(base / d), "email": info.get("user_name") or "",
                    "name": info.get("gaia_name") or info.get("name") or d})
    return sorted(out, key=lambda x: (x["dir"] != "Default", x["dir"]))


def convert_chrome_node(n):
    t = n.get("type")
    if t == "url":
        u = n.get("url", "")
        if u.startswith(("http://", "https://", "file://")):
            return {"title": n.get("name") or u, "url": u}
        return None
    if t == "folder":
        kids = [x for x in (convert_chrome_node(c) for c in n.get("children", []) or []) if x]
        return {"title": n.get("name") or "Folder", "folder": True, "children": kids}
    return None


def chrome_extensions(profile_path):
    base = Path(profile_path) / "Extensions"
    out = []
    if not base.is_dir():
        return out
    for d in base.iterdir():
        if not re.fullmatch(r"[a-p]{32}", d.name):
            continue
        vers = sorted((v for v in d.iterdir() if v.is_dir()), key=lambda x: x.name)
        if not vers:
            continue
        v = vers[-1]
        try:
            man = json.loads((v / "manifest.json").read_text(encoding="utf-8-sig"))
        except Exception:
            continue
        if "theme" in man:
            continue
        name = str(man.get("name", ""))
        if name.startswith("__MSG_"):
            key = name[6:-2].lower()
            try:
                msgs = json.loads((v / "_locales" / man.get("default_locale", "en") / "messages.json")
                                  .read_text(encoding="utf-8-sig"))
                low = {k.lower(): val for k, val in msgs.items()}
                name = low.get(key, {}).get("message", d.name)
            except Exception:
                name = d.name
        out.append({"id": d.name, "name": name or d.name, "mv": man.get("manifest_version", 2)})
    return out


def build_account_folder(prof):
    """Read one Chrome profile's bookmarks file and turn it into one bookmark folder (or None)."""
    try:
        data = json.loads((Path(prof["path"]) / "Bookmarks").read_text(encoding="utf-8"))
    except Exception:
        return None
    roots = data.get("roots", {})
    kids = [c for c in (convert_chrome_node(n) for n in roots.get("bookmark_bar", {}).get("children", []) or []) if c]
    for key, title in (("other", "Other bookmarks"), ("synced", "Mobile bookmarks")):
        sub = [c for c in (convert_chrome_node(n) for n in roots.get(key, {}).get("children", []) or []) if c]
        if sub:
            kids.append({"title": title, "folder": True, "children": sub})
    return {"title": prof["email"] or prof["name"], "folder": True, "src": prof["dir"], "children": kids}


class GoogleWindow(QFrame):
    """Google accounts: web sign-in shortcuts + one-click import/sync from the Chrome profiles on this PC."""

    def __init__(self, browser):
        super().__init__(browser, Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setObjectName("settings")
        self.b = browser
        self._drag = None
        self.resize(620, 720)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(24, 20, 24, 22)
        outer.setSpacing(10)

        head = QHBoxLayout()
        head.addWidget(QLabel("Google accounts", objectName="settitle"))
        head.addStretch(1)
        x = HoverButton(objectName="flat")
        x.setIcon(QIcon(pm_icon("close", width=4)))
        x.setIconSize(QSize(16, 16))
        x.setFixedSize(32, 32)
        x.clicked.connect(self.close)
        head.addWidget(x)
        outer.addLayout(head)
        self.sub = QLabel("", objectName="extmuted")
        self.sub.setStyleSheet("padding:0;")
        outer.addWidget(self.sub)

        web = HoverRow(base=16, hi=22, radius=16)
        wl = QVBoxLayout(web)
        wl.setContentsMargins(16, 14, 16, 14)
        wl.setSpacing(8)
        wl.addWidget(QLabel("Sign in on the web", objectName="extname"))
        t = QLabel("Sign in to as many Google accounts as you like here and switch between them from Google’s "
                   "own account menu. Sign-ins stay saved in this browser.", objectName="extmeta")
        t.setWordWrap(True)
        wl.addWidget(t)
        crow = QHBoxLayout()
        crow.setSpacing(8)
        for text, url in [("Add Google account", "https://accounts.google.com/AddSession?continue=https://www.google.com/"),
                          ("Switch accounts", "https://accounts.google.com/AccountChooser"),
                          ("My Account", "https://myaccount.google.com/")]:
            c = HoverButton(objectName="chip")
            c.setText(text)
            c.setFixedHeight(30)
            c.setCursor(Qt.CursorShape.PointingHandCursor)
            c.clicked.connect(lambda _=False, u=url: (self.close(), browser.add_tab(u)))
            crow.addWidget(c)
        crow.addStretch(1)
        wl.addLayout(crow)
        outer.addWidget(web)

        sec = QHBoxLayout()
        sec.addWidget(QLabel("Accounts found in Chrome", objectName="extname"))
        sec.addStretch(1)
        self.all_btn = HoverButton(objectName="chip")
        self.all_btn.setText("Sync all now")
        self.all_btn.setFixedHeight(30)
        self.all_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.all_btn.clicked.connect(lambda: browser.sync_profiles(chrome_profiles()))
        sec.addWidget(self.all_btn)
        outer.addLayout(sec)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.content = QWidget()
        self.cl = QVBoxLayout(self.content)
        self.cl.setContentsMargins(0, 2, 4, 0)
        self.cl.setSpacing(8)
        scroll.setWidget(self.content)
        outer.addWidget(scroll, 1)

        note = QLabel("LiteBrowser can’t use Google’s own sync service (it only works inside Chrome). Instead it copies "
                      "bookmarks and extensions from the Chrome profiles on this PC, so keep Chrome’s sync on for each "
                      "account. Synced bookmarks show up as one folder per account. Passwords, history and open tabs "
                      "are not synced.", objectName="extmeta")
        note.setWordWrap(True)
        outer.addWidget(note)
        self.build(animate=True)

    def paintEvent(self, e):
        paint_glass(self, 22)

    def showEvent(self, e):
        super().showEvent(e)
        fade_in_window(self, 220, 14)
        self.activateWindow()
        self.setFocus()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and e.position().y() < 64:
            self._drag = e.globalPosition().toPoint() - self.frameGeometry().topLeft()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._drag is not None and e.buttons() & Qt.MouseButton.LeftButton:
            self.move(e.globalPosition().toPoint() - self._drag)
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._drag = None
        super().mouseReleaseEvent(e)

    def build(self, animate=False):
        b = self.b
        while self.cl.count():
            w = self.cl.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        last = b.gsync.get("last")
        self.sub.setText(("Last synced " + datetime.fromtimestamp(last).strftime("%d %b, %H:%M")) if last else "Not synced yet")
        profs = chrome_profiles()
        self.all_btn.setEnabled(bool(profs))
        if not profs:
            self.cl.addWidget(QLabel("No Chrome profiles found on this PC.\nInstall Chrome, sign in with sync turned on,\n"
                                     "and your accounts will appear here.", objectName="extmuted"))
        for i, pr in enumerate(profs):
            cfg = b.gsync["accounts"].get(pr["dir"], {})
            row = HoverRow(base=16, hi=26, radius=16)
            v = QVBoxLayout(row)
            v.setContentsMargins(14, 12, 12, 12)
            v.setSpacing(10)
            top = QHBoxLayout()
            top.setSpacing(12)
            av = QLabel()
            av.setPixmap(letter_icon(pr["name"] or pr["email"]).pixmap(QSize(40, 40)))
            av.setFixedSize(42, 42)
            top.addWidget(av)
            col = QVBoxLayout()
            col.setSpacing(2)
            col.addWidget(QLabel(pr["name"], objectName="extname"))
            col.addWidget(QLabel(pr["email"] or "Not signed in to Chrome", objectName="extmeta"))
            top.addLayout(col, 1)
            sync = HoverButton(objectName="chip")
            sync.setText("Sync now")
            sync.setFixedHeight(28)
            sync.setCursor(Qt.CursorShape.PointingHandCursor)
            sync.clicked.connect(lambda _=False, p=pr: b.sync_profiles([p]))
            top.addWidget(sync)
            v.addLayout(top)
            opts = QHBoxLayout()
            opts.setSpacing(8)
            for key, label in (("bookmarks", "Keep bookmarks in sync"), ("extensions", "Keep extensions in sync")):
                tg = Toggle(bool(cfg.get(key)))
                tg.toggled.connect(lambda on, p=pr, k=key: b.set_sync(p, k, on))
                opts.addWidget(tg)
                opts.addWidget(QLabel(label, objectName="extmeta"))
                opts.addSpacing(14)
            opts.addStretch(1)
            v.addLayout(opts)
            self.cl.addWidget(row)
            if animate:
                fade_widget(row, delay=70 + i * 50)
        self.cl.addStretch(1)


class History:
    """Browsing history in a small SQLite file (one row per address: title, visit count, last visit)."""

    def __init__(self):
        self.db = None
        self._dirty = False
        try:
            DATA.mkdir(parents=True, exist_ok=True)
            self.db = sqlite3.connect(str(HISTORY_DB))
            self.db.execute("PRAGMA journal_mode=WAL")
            self.db.execute("PRAGMA synchronous=NORMAL")
            self.db.execute("CREATE TABLE IF NOT EXISTS urls "
                            "(url TEXT PRIMARY KEY, title TEXT, visits INTEGER, last INTEGER)")
            self.db.execute("CREATE INDEX IF NOT EXISTS idx_last ON urls(last)")
            self.db.execute("CREATE TABLE IF NOT EXISTS typed (text TEXT PRIMARY KEY, count INTEGER, last INTEGER)")
            self.db.commit()
        except Exception:
            self.db = None

    def _run(self, sql, args=(), commit=False):
        if self.db is None:
            return []
        try:
            rows = self.db.execute(sql, args).fetchall()
            if commit:
                self._dirty = True          # written to disk in batches by flush()
            return rows
        except Exception:
            return []

    def flush(self):
        if self.db is not None and self._dirty:
            try:
                self.db.commit()
                self._dirty = False
            except Exception:
                pass

    def visit(self, url, title):
        self._run("INSERT INTO urls(url, title, visits, last) VALUES(?, ?, 1, ?) "
                  "ON CONFLICT(url) DO UPDATE SET "
                  "title = CASE WHEN excluded.title <> '' THEN excluded.title ELSE urls.title END, "
                  "visits = urls.visits + 1, last = excluded.last",
                  (url, title or "", int(time.time())), True)

    def set_title(self, url, title):
        self._run("UPDATE urls SET title = ? WHERE url = ?", (title, url), True)

    def search(self, q="", limit=400):
        if q:
            like = f"%{q}%"
            return self._run("SELECT url, title, visits, last FROM urls WHERE title LIKE ? OR url LIKE ? "
                             "ORDER BY last DESC LIMIT ?", (like, like, limit))
        return self._run("SELECT url, title, visits, last FROM urls ORDER BY last DESC LIMIT ?", (limit,))

    def suggest(self, q, limit=5):
        like = f"%{q}%"
        return self._run("SELECT url, title FROM urls WHERE title LIKE ? OR url LIKE ? "
                         "ORDER BY visits DESC, last DESC LIMIT ?", (like, like, limit))

    def add_typed(self, text):
        """Remember an address the user typed (and that really loaded)."""
        self._run("INSERT INTO typed(text, count, last) VALUES(?, 1, ?) "
                  "ON CONFLICT(text) DO UPDATE SET count = typed.count + 1, last = excluded.last",
                  (text, int(time.time())), True)

    @staticmethod
    def _esc(s):
        return s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")

    def complete(self, prefix):
        """Best address that starts with what is being typed: sites you typed before first, then sites you visited."""
        p = (prefix or "").strip().lower()
        if not p or " " in p:
            return None
        rows = self._run("SELECT text FROM typed WHERE text LIKE ? ESCAPE '\\' AND length(text) > ? "
                         "ORDER BY count DESC, last DESC LIMIT 1", (self._esc(p) + "%", len(p)))
        if rows:
            return rows[0][0]
        pats = tuple(f"{sch}{www}{self._esc(p)}%" for sch in ("https://", "http://") for www in ("", "www."))
        rows = self._run("SELECT url, visits FROM urls WHERE url LIKE ? ESCAPE '\\' OR url LIKE ? ESCAPE '\\' "
                         "OR url LIKE ? ESCAPE '\\' OR url LIKE ? ESCAPE '\\' ORDER BY visits DESC, last DESC LIMIT 60", pats)
        score = {}
        for url, visits in rows:
            rest = url.split("://", 1)[-1]
            if rest.startswith("www."):
                rest = rest[4:]
            cand = (rest if "/" in p else rest.split("/", 1)[0]).rstrip("/")
            if len(cand) > len(p) and cand.lower().startswith(p):
                score[cand] = score.get(cand, 0) + visits
        return max(score, key=score.get) if score else None

    def delete(self, url):
        self._run("DELETE FROM urls WHERE url = ?", (url,), True)

    def clear(self, since=0):
        self._run("DELETE FROM urls WHERE last >= ?", (since,), True)
        self._run("DELETE FROM typed WHERE last >= ?", (since,), True)


class Suggest(QFrame):
    """Drop-down under the address bar: matching history/bookmarks plus 'Search Google'."""
    picked = pyqtSignal(str)

    def showEvent(self, e):
        super().showEvent(e)
        self._faded = False
        fade_in_window(self, 130, 0)

    def __init__(self, browser):
        super().__init__(browser, Qt.WindowType.ToolTip | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowDoesNotAcceptFocus | Qt.WindowType.NoDropShadowWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)
        self.rows, self.values, self.sel = [], [], -1
        self.lay = QVBoxLayout(self)
        self.lay.setContentsMargins(8, 8, 8, 8)
        self.lay.setSpacing(2)

    def paintEvent(self, e):
        paint_glass(self, 14, (48, 8, 18, 250))

    def set_items(self, items, width):
        self.setFixedWidth(width)
        while self.lay.count():
            w = self.lay.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        self.rows, self.values, self.sel = [], [], -1
        fm = QFontMetrics(QFont(self.font().family(), 10))
        for icon, title, sub, value in items:
            row = HoverRow(base=0, hi=30, radius=10)
            h = QHBoxLayout(row)
            h.setContentsMargins(10, 7, 10, 7)
            h.setSpacing(10)
            ic = QLabel()
            ic.setPixmap(icon.pixmap(QSize(16, 16)))
            ic.setFixedSize(18, 18)
            h.addWidget(ic)
            h.addWidget(QLabel(fm.elidedText(title, Qt.TextElideMode.ElideRight, int(width * 0.56)), objectName="extname"), 1)
            if sub:
                h.addWidget(QLabel(fm.elidedText(sub, Qt.TextElideMode.ElideRight, int(width * 0.30)), objectName="extmeta"))
            row.clicked.connect(lambda v=value: self.picked.emit(v))
            self.lay.addWidget(row)
            self.rows.append(row)
            self.values.append(value)
        self.adjustSize()

    def move_sel(self, d):
        if not self.rows:
            return
        self.sel = (self.sel + d) % len(self.rows)
        for i, r in enumerate(self.rows):
            r._base, r._hi = (36, 40) if i == self.sel else (0, 30)
            r.update()

    def current_value(self):
        return self.values[self.sel] if 0 <= self.sel < len(self.values) else None


class HistoryWindow(QFrame):
    """History: searchable list grouped by day, with delete and 'clear' options."""

    def __init__(self, browser):
        super().__init__(browser, Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setObjectName("settings")
        self.b = browser
        self._drag = None
        self.limit = 80
        self.resize(660, 740)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(24, 20, 24, 22)
        outer.setSpacing(10)

        head = QHBoxLayout()
        head.addWidget(QLabel("History", objectName="settitle"))
        head.addStretch(1)
        x = HoverButton(objectName="flat")
        x.setIcon(QIcon(pm_icon("close", width=4)))
        x.setIconSize(QSize(16, 16))
        x.setFixedSize(32, 32)
        x.clicked.connect(self.close)
        head.addWidget(x)
        outer.addLayout(head)

        self.search = QLineEdit(placeholderText="Search history")
        self.search.setFixedHeight(38)
        outer.addWidget(self.search)
        self._debounce = QTimer(self)
        self._debounce.setSingleShot(True)
        self._debounce.setInterval(150)
        self._debounce.timeout.connect(self._search_changed)
        self.search.textChanged.connect(lambda _t: self._debounce.start())

        actions = QHBoxLayout()
        actions.setSpacing(8)
        for text, since in [("Clear last hour", lambda: time.time() - 3600),
                            ("Clear today", lambda: datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp()),
                            ("Clear all history", lambda: 0)]:
            c = HoverButton(objectName="chip")
            c.setText(text)
            c.setFixedHeight(30)
            c.setCursor(Qt.CursorShape.PointingHandCursor)
            c.clicked.connect(lambda _=False, f=since, t=text: self._clear(f(), t))
            actions.addWidget(c)
        actions.addStretch(1)
        outer.addLayout(actions)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.content = QWidget()
        self.cl = QVBoxLayout(self.content)
        self.cl.setContentsMargins(0, 2, 4, 0)
        self.cl.setSpacing(2)
        scroll.setWidget(self.content)
        outer.addWidget(scroll, 1)
        self.build(animate=True)

    def paintEvent(self, e):
        paint_glass(self, 22)

    def showEvent(self, e):
        super().showEvent(e)
        fade_in_window(self, 220, 14)
        self.activateWindow()
        self.search.setFocus()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and e.position().y() < 64:
            self._drag = e.globalPosition().toPoint() - self.frameGeometry().topLeft()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._drag is not None and e.buttons() & Qt.MouseButton.LeftButton:
            self.move(e.globalPosition().toPoint() - self._drag)
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._drag = None
        super().mouseReleaseEvent(e)

    def _search_changed(self):
        self.limit = 80
        self.build()

    def _clear(self, since, label):
        self.b.history.clear(since)
        self.build()
        self.b.toast(label.replace("Clear", "Cleared").replace("all history", "all history"))

    def _delete(self, url, row):
        self.b.history.delete(url)
        row.setParent(None)
        row.deleteLater()

    @staticmethod
    def _day_label(d):
        today = datetime.now().date()
        if d == today:
            return "Today"
        if (today - d).days == 1:
            return "Yesterday"
        return d.strftime("%A, %d %B %Y")

    def build(self, animate=False):
        b = self.b
        while self.cl.count():
            w = self.cl.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        q = self.search.text().strip()
        rows = b.history.search(q, self.limit)
        if not rows:
            self.cl.addWidget(QLabel("No matches." if q else "Nothing here yet. Pages you visit will show up here.",
                                     objectName="extmuted"))
        fm = QFontMetrics(QFont(self.font().family(), 10))
        last_day = None
        for i, (url, title, visits, ts) in enumerate(rows):
            day = datetime.fromtimestamp(ts).date()
            if day != last_day:
                last_day = day
                lab = QLabel(self._day_label(day), objectName="extname")
                lab.setContentsMargins(6, 12, 0, 4)
                self.cl.addWidget(lab)
            row = HoverRow(base=0, hi=26, radius=12)
            row.setCursor(Qt.CursorShape.PointingHandCursor)
            h = QHBoxLayout(row)
            h.setContentsMargins(10, 8, 6, 8)
            h.setSpacing(12)
            ic = QLabel()
            ic.setPixmap(b.fav_icon(url).pixmap(QSize(18, 18)))
            ic.setFixedSize(20, 20)
            h.addWidget(ic)
            col = QVBoxLayout()
            col.setSpacing(1)
            col.addWidget(QLabel(fm.elidedText(title or url, Qt.TextElideMode.ElideRight, 360), objectName="extname"))
            col.addWidget(QLabel(fm.elidedText(url, Qt.TextElideMode.ElideRight, 360), objectName="extmeta"))
            h.addLayout(col, 1)
            h.addWidget(QLabel(datetime.fromtimestamp(ts).strftime("%H:%M"), objectName="extmeta"))
            rm = HoverButton(objectName="flat")
            rm.setIcon(QIcon(pm_icon("close", "#d9a4ac", width=4)))
            rm.setIconSize(QSize(12, 12))
            rm.setFixedSize(28, 28)
            rm.setToolTip("Remove from history")
            rm.clicked.connect(lambda _=False, u=url, r=row: self._delete(u, r))
            h.addWidget(rm)
            row.clicked.connect(lambda u=url: (self.close(), b.cur().setUrl(QUrl(u))))
            self.cl.addWidget(row)
            if animate and i < 14:
                fade_widget(row, delay=60 + i * 30)
        if len(rows) >= self.limit:           # long histories load in pages so the window opens instantly
            more = HoverButton(objectName="chip")
            more.setText("Show older entries")
            more.setFixedHeight(32)
            more.setCursor(Qt.CursorShape.PointingHandCursor)
            more.clicked.connect(lambda: (setattr(self, "limit", self.limit + 160), self.build()))
            self.cl.addWidget(more)
        self.cl.addStretch(1)


class TitleBar(QWidget):
    """The strip above the toolbar: drag to move the window, double-click to maximize."""

    def __init__(self, win, **kw):
        super().__init__(**kw)
        self.win = win
        self._press = False

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._press = True
            e.accept()
        else:
            super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._press and e.buttons() & Qt.MouseButton.LeftButton:
            self._press = False
            self.win.start_move()
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._press = False
        super().mouseReleaseEvent(e)

    def mouseDoubleClickEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._press = False
            self.win.toggle_max()
            e.accept()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        tb = getattr(self.win, "tabbar", None)
        if tb is not None:
            tb.refit(False)


def tint_from_icon(ic):
    """Dominant, slightly boosted colour of a favicon (used to tint its tab)."""
    try:
        img = ic.pixmap(QSize(16, 16)).toImage()
        r = g = bl = n = 0
        for y in range(img.height()):
            for x in range(img.width()):
                c = img.pixelColor(x, y)
                if c.alpha() > 128:
                    r += c.red()
                    g += c.green()
                    bl += c.blue()
                    n += 1
        if n < 8:
            return None
        h, sat, v, _ = QColor(r // n, g // n, bl // n).getHsv()
        if h < 0 or sat < 25:
            return QColor(205, 205, 220)
        return QColor.fromHsv(h, min(255, int(sat * 1.25) + 25), max(v, 190))
    except Exception:
        return None


class Backdrop(QWidget):
    """Window background: soft red 'liquid' colour blobs. Painted once at a small fixed size, then just scaled."""

    def __init__(self, **kw):
        super().__init__(**kw)
        self._base = None
        self._scaled = None

    @staticmethod
    def _render():
        w, h = 640, 360
        pm = QPixmap(w, h)
        pm.fill(QColor("#0c0206"))
        p = QPainter(pm)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        for fx, fy, fr, (r, g, b, a) in [(0.06, 0.04, 0.60, (225, 29, 72, 120)),
                                          (0.90, 0.10, 0.42, (255, 92, 58, 56)),
                                          (0.26, 0.96, 0.52, (150, 15, 62, 105)),
                                          (0.98, 0.92, 0.50, (205, 22, 92, 90))]:
            rad = fr * max(w, h)
            c = QPointF(fx * w, fy * h)
            gr = QRadialGradient(c, rad)
            gr.setColorAt(0.0, QColor(r, g, b, a))
            gr.setColorAt(0.55, QColor(r, g, b, a // 3))
            gr.setColorAt(1.0, QColor(r, g, b, 0))
            p.setBrush(QBrush(gr))
            p.drawEllipse(c, rad, rad)
        p.end()
        return pm

    def paintEvent(self, e):
        if self._base is None:
            self._base = self._render()
        if self._scaled is None or self._scaled.size() != self.size():
            self._scaled = self._base.scaled(self.size(), Qt.AspectRatioMode.IgnoreAspectRatio,
                                             Qt.TransformationMode.SmoothTransformation)
        p = QPainter(self)
        p.drawPixmap(e.rect(), self._scaled, e.rect())      # only the dirty part
        p.end()


class UrlBar(QLineEdit):
    """Shows just the site name when idle (like the reference), the full address while editing."""

    chosen = pyqtSignal(str)
    escaped = pyqtSignal()

    def __init__(self, **kw):
        super().__init__(**kw)
        self._full = ""
        self.sug = None
        self.no_complete = False

    def keyPressEvent(self, e):
        # Backspace/Delete, paste and cut must not be 'fixed' by the auto-complete
        self.no_complete = (e.key() in (Qt.Key.Key_Backspace, Qt.Key.Key_Delete)
                            or e.matches(QKeySequence.StandardKey.Paste) or e.matches(QKeySequence.StandardKey.Cut))
        s = self.sug
        if s is not None and s.isVisible():
            k = e.key()
            if k == Qt.Key.Key_Down:
                s.move_sel(1)
                return
            if k == Qt.Key.Key_Up:
                s.move_sel(-1)
                return
            if k == Qt.Key.Key_Escape:
                s.hide()
                return
            if k in (Qt.Key.Key_Return, Qt.Key.Key_Enter) and s.sel >= 0:
                v = s.current_value()
                s.hide()
                if v:
                    self.chosen.emit(v)
                return
        if e.key() == Qt.Key.Key_Escape:        # Esc: forget what was typed and go back to the page
            self.setText(self._full)
            self.escaped.emit()
            return
        super().keyPressEvent(e)

    @staticmethod
    def nice(u):
        h = QUrl(u).host()
        return h or u

    def set_url(self, full):
        self._full = full
        if self.hasFocus():
            if not self.isModified():            # don't overwrite what the user is typing
                self.setText(full)
        else:
            self.setText(self.nice(full) if full else "")
            self.setCursorPosition(0)

    def focusInEvent(self, e):
        super().focusInEvent(e)
        if self.text() != self._full:
            self.setText(self._full)
        QTimer.singleShot(0, self.selectAll)

    def focusOutEvent(self, e):
        super().focusOutEvent(e)
        if self.sug is not None:
            self.sug.hide()
        self.setText(self.nice(self._full) if self._full else "")
        self.setCursorPosition(0)


class GlassBar(QWidget):
    """Soft rounded container behind the toolbar row (redesign v4)."""

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        p.setBrush(QColor(255, 255, 255, 11))
        p.setPen(QPen(QColor(255, 255, 255, 22), 1))
        p.drawRoundedRect(r, 16, 16)
        p.end()


class CardFrame(QWidget):
    """Thin glass outline around the page area."""

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QColor(255, 255, 255, 34), 1))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5), 16, 16)
        p.end()


class Card(QStackedWidget):
    """Holds the pages; clips them to rounded corners (re-applied once resizing has settled)."""

    def __init__(self):
        super().__init__()
        self._masked = False
        self._mask_timer = QTimer(self)
        self._mask_timer.setSingleShot(True)
        self._mask_timer.setInterval(70)
        self._mask_timer.timeout.connect(self._apply_mask)

    def resizeEvent(self, e):
        super().resizeEvent(e)
        if not ROUND_CONTENT:
            return
        if self._masked:                 # no clipping while the size is changing, so the page never lags behind
            self.clearMask()
            self._masked = False
        self._mask_timer.start()

    def _apply_mask(self):
        w, h = self.width(), self.height()
        if w < 4 or h < 4:
            return
        bm = QBitmap(w, h)
        bm.fill(Qt.GlobalColor.color0)
        p = QPainter(bm)
        p.setBrush(Qt.GlobalColor.color1)
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRoundedRect(0, 0, w, h, 15, 15)
        p.end()
        self.setMask(bm)
        self._masked = True


class FindEdit(QLineEdit):
    """Find box: Enter = next, Shift+Enter = previous, Esc = close."""
    prev = pyqtSignal()
    closed = pyqtSignal()

    def keyPressEvent(self, e):
        k = e.key()
        if k == Qt.Key.Key_Escape:
            self.closed.emit()
            return
        if k in (Qt.Key.Key_Return, Qt.Key.Key_Enter) and e.modifiers() & Qt.KeyboardModifier.ShiftModifier:
            self.prev.emit()
            return
        super().keyPressEvent(e)


class DevTools(QWidget):
    """Chromium's developer tools for the current page (F12)."""

    def __init__(self, browser, view):
        super().__init__(None)
        self.setWindowTitle("Developer tools - " + (view.title() or "page"))
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.resize(1000, 650)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        self.view = QWebEngineView(self)
        self.dpage = QWebEnginePage(browser.profile, self.view)
        self.view.setPage(self.dpage)
        lay.addWidget(self.view)
        self.inspected = view.page()
        self.inspected.setDevToolsPage(self.dpage)

    def closeEvent(self, e):
        try:
            self.inspected.setDevToolsPage(None)
        except Exception:
            pass
        super().closeEvent(e)


class CloseSlot(QWidget):
    """Invisible stand-in for Qt's close button: keeps the tab text clear of the X we paint ourselves."""

    def __init__(self):
        super().__init__()
        self.setFixedSize(20, 20)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)


class TabStub:
    """A restored tab whose web view has not been created yet: it remembers URL, title, icon colour."""

    def __init__(self, url, title):
        self.pending_url = url
        self.title_text = title or QUrl(url).host() or url
        self.tint = None
        self.is_start = False

    def url(self):
        return QUrl(self.pending_url)


class TabBar(QTabBar):
    """Horizontal glass tabs, tinted with each site's colour.

    Like Chrome, tabs shrink as you open more so that all of them stay visible: wide tabs show title and
    close button, narrower ones drop the title, and the tiniest show only the icon. The active tab never
    gets smaller than ACTIVE_MIN so it always keeps a close button. Empty space drags the window."""
    MAX_W, MIN_W, ACTIVE_MIN, RESERVED = 230, 40, 64, 236

    def __init__(self, win, **kw):
        super().__init__(**kw)
        self.win = win
        self._empty = False
        self._hover = -1
        self._on_tab = False
        self._dragging = False
        self._grab = 0
        self._mx = 0
        self._w_cur = self._w_other = 160.0
        self._tgt = (160, 160, 600)
        self._inited = False
        self._spk = None
        self._th = None
        self._pending = False
        self._sig = None
        self.setMouseTracking(True)
        self.setUsesScrollButtons(True)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.customContextMenuRequested.connect(lambda pos: self.win.tab_menu(self.tabAt(pos), self.mapToGlobal(pos)))
        self.currentChanged.connect(lambda _i: (self.refit(True), self._ease_start()))
        self._lv = {}                                  # per-tab highlight level 0..1, eased towards its target
        self._cv = {}                                  # per-tab close-button hover level 0..1
        self._ch = -1                                  # tab whose close button the mouse is over
        self._pc = None                                # tab whose close button is being pressed
        self._hold = False                             # after a mouse close keep widths so the next X lands under the cursor
        self._closing = None                           # tab currently shrinking away
        self._close_t = 0.0
        self._canim = QVariantAnimation(self)
        self._canim.setDuration(150)
        self._canim.setEasingCurve(QEasingCurve.Type.InOutCubic)
        self._canim.setStartValue(0.0)
        self._canim.setEndValue(1.0)
        self._canim.valueChanged.connect(self._close_step)
        self._canim.finished.connect(self._finish_close)
        self._lv_timer = QTimer(self)
        self._lv_timer.setInterval(16)
        self._lv_timer.timeout.connect(self._ease_step)
        self._anim = QVariantAnimation(self)
        self._anim.setDuration(160)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._anim.setStartValue(0.0)
        self._anim.setEndValue(1.0)
        self._anim.valueChanged.connect(self._step)

    # ---- sizing ---------------------------------------------------------------------
    def tabSizeHint(self, index):
        if self._th is None:
            h = super().tabSizeHint(index).height()
            if self.isVisible():
                self._th = h                 # style metrics are final once shown: cache them
        else:
            h = self._th
        w = self._w_cur if index == self.currentIndex() else self._w_other
        if self._closing is not None and self.tabData(index) is self._closing:
            w = max(1.0, w * (1.0 - self._close_t))
        return QSize(int(round(w)), h)

    def minimumTabSizeHint(self, index):
        return QSize(self.MIN_W, self.tabSizeHint(index).height())

    def tabInserted(self, index):
        super().tabInserted(index)
        self._queue_refit()

    def tabRemoved(self, index):
        super().tabRemoved(index)
        self._queue_refit()

    def _queue_refit(self):                  # many inserts/removals in a row -> a single re-fit
        if not self._pending:
            self._pending = True
            QTimer.singleShot(0, self._do_refit)

    def _do_refit(self):
        self._pending = False
        for i in range(self.count()):                    # swap Qt's close buttons for invisible spacers (we paint the X)
            b = self.tabButton(i, QTabBar.ButtonPosition.RightSide)
            if b is not None and not isinstance(b, CloseSlot):
                self.setTabButton(i, QTabBar.ButtonPosition.RightSide, CloseSlot())
                b.deleteLater()
        self._apply_close()
        self.refit(True)

    def refit(self, animate=True):
        n = self.count()
        tw = getattr(self.win, "tabwrap", None)
        if n == 0 or tw is None:
            return
        avail = max(120, tw.width() - self.RESERVED)
        even = avail // n
        if even >= self.ACTIVE_MIN:
            cur = other = float(min(self.MAX_W, even))
        else:
            cur = float(self.ACTIVE_MIN)
            other = float(max(self.MIN_W, (avail - self.ACTIVE_MIN) // max(1, n - 1)))
        if self._hold and self._inited:                  # Brave-style: don't re-grow tabs while you keep closing them
            cur, other = min(cur, self._tgt[0]), min(other, self._tgt[1])
        new = (cur, other, avail)
        cur_dep = other < 92 or cur != other     # the active tab only matters when widths/close buttons differ
        sig = (n, self.currentIndex() if cur_dep else -1, cur >= 56, other >= 56, cur >= 92, other >= 92)
        if new == self._tgt and sig == self._sig and self._inited:
            return                           # nothing changed: do no work at all
        self._tgt = new
        if sig != self._sig:                 # titles / close buttons only change when a width class changes
            self._sig = sig
            self._apply_text()
            self._apply_close()
        self._anim.stop()
        if animate and self._inited:
            self._from = (self._w_cur, self._w_other)
            self._anim.start()
        else:
            self._w_cur, self._w_other = cur, other
            self._relayout()
        self._inited = True

    def _step(self, t):
        t = float(t)
        self._w_cur = self._from[0] + (self._tgt[0] - self._from[0]) * t
        self._w_other = self._from[1] + (self._tgt[1] - self._from[1]) * t
        self._relayout()

    def _relayout(self):
        n = self.count()
        if n == 0:
            return
        total = self._w_cur + self._w_other * (n - 1)
        self.setFixedWidth(int(min(total, self._tgt[2]) + 2))
        self.setTabText(0, self.tabText(0))  # cheapest way to make Qt re-run its tab layout
        self.update()

    def _title(self, i):
        return getattr(self.tabData(i), "title_text", None) or "New Tab"

    def _apply_text(self):
        cur = self.currentIndex()
        for i in range(self.count()):
            w = self._tgt[0] if i == cur else self._tgt[1]
            t = self._title(i)
            self.setTabText(i, t if w >= 56 else "")
            self.setTabToolTip(i, t)

    def set_title(self, i):
        w = self._tgt[0] if i == self.currentIndex() else self._tgt[1]
        t = self._title(i)
        self.setTabText(i, t if w >= 56 else "")
        self.setTabToolTip(i, t)

    def _apply_close(self):
        cur = self.currentIndex()
        for i in range(self.count()):
            btn = self.tabButton(i, QTabBar.ButtonPosition.RightSide)
            if btn is None:
                continue
            w = self._tgt[0] if i == cur else self._tgt[1]
            btn.setVisible(w >= 92 or (w >= 56 and (i == cur or i == self._hover)))

    # ---- close button (painted by us) ------------------------------------------------------
    def _close_vis(self, i):
        if i < 0 or i >= self.count():
            return False
        w = self._tgt[0] if i == self.currentIndex() else self._tgt[1]
        return w >= 92 or (w >= 56 and (i == self.currentIndex() or i == self._hover))

    def _cr(self, i):
        r = QRectF(self.tabRect(i)).adjusted(2, 3, -2, -3)
        return QRectF(r.right() - 27, r.center().y() - 11, 22, 22)

    def _poke(self):
        if self.count():
            self.setTabText(0, self.tabText(0))          # make Qt re-run its tab layout
        self.update()

    def _index_of(self, d):
        for i in range(self.count()):
            if self.tabData(i) is d:
                return i
        return -1

    def close_animated(self, i):
        d = self.tabData(i)
        if d is None:
            return
        if self._closing is not None:
            if self._closing is d:
                return
            self._canim.stop()
            self._finish_close()                         # a previous close is still running: finish it now
        i = self._index_of(d)
        if i < 0:
            return
        if self.count() <= 1 or not self.isVisible():
            self.win.close_tab(i)
            return
        self._closing = d
        self._close_t = 0.0
        self._canim.start()

    def _close_step(self, t):
        self._close_t = float(t)
        self._poke()

    def _finish_close(self):
        d, self._closing = self._closing, None
        self._close_t = 0.0
        if d is None:
            return
        i = self._index_of(d)
        if i >= 0:
            self.win.close_tab(i)

    # ---- eased highlight ----------------------------------------------------------------
    def _target(self, i):
        return 1.0 if i == self.currentIndex() else (0.4 if i == self._hover else 0.0)

    def _ease_start(self):
        if not self._lv_timer.isActive():
            self._lv_timer.start()

    def _ease_step(self):
        busy = False
        keep = set()
        for i in range(self.count()):
            k = id(self.tabData(i))
            keep.add(k)
            t = self._target(i)
            v = self._lv.get(k, t)
            if abs(t - v) > 0.01:
                v += (t - v) * 0.28
                busy = True
            else:
                v = t
            self._lv[k] = v
            ct = 1.0 if i == self._ch else 0.0
            cv = self._cv.get(k, 0.0)
            if abs(ct - cv) > 0.01:
                cv += (ct - cv) * 0.35
                busy = True
            else:
                cv = ct
            self._cv[k] = cv
        for k in [k for k in self._lv if k not in keep]:
            del self._lv[k]
            self._cv.pop(k, None)
        self.update()
        if not busy:
            self._lv_timer.stop()

    # ---- painting ---------------------------------------------------------------------
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        cur = self.currentIndex()
        for i in range(self.count()):
            r = QRectF(self.tabRect(i)).adjusted(2, 3, -2, -3)
            if self._dragging and i == cur:      # follow the mouse while the tab is being dragged
                r.moveLeft(max(2.0, min(self._mx - self._grab + 2, self.width() - r.width() - 2.0)))
            tint = getattr(self.tabData(i), "tint", None) or QColor(255, 96, 118)
            sel = i == cur
            closing = self._closing is not None and self.tabData(i) is self._closing
            p.setOpacity(max(0.0, 1.0 - self._close_t * 1.15) if closing else 1.0)
            lv = self._lv.get(id(self.tabData(i)), 1.0 if sel else 0.0)
            if lv > 0.02:
                g = QLinearGradient(r.left(), r.top(), r.right(), r.bottom())
                c1, c2 = QColor(tint), QColor(tint)
                c1.setAlpha(int(100 * lv))
                c2.setAlpha(int(34 * lv))
                g.setColorAt(0, c1)
                g.setColorAt(1, c2)
                p.setBrush(QBrush(g))
                p.setPen(Qt.PenStyle.NoPen)
                p.drawRoundedRect(r, 12, 12)
                ba = int(52 * max(0.0, (lv - 0.4) / 0.6))
                p.setBrush(QColor(255, 255, 255, int(26 * lv)))
                p.setPen(QPen(QColor(255, 255, 255, ba), 1) if ba else Qt.PenStyle.NoPen)
                p.drawRoundedRect(r, 12, 12)
            da = int(70 * (1 - min(1.0, lv * 2.5)))
            if da > 2:                                  # idle tab: just a small tinted dash
                c = QColor(tint)
                c.setAlpha(da)
                p.setBrush(c)
                p.setPen(Qt.PenStyle.NoPen)
                p.drawRoundedRect(QRectF(r.center().x() - 7, r.bottom() - 1.5, 14, 2), 1, 1)
            if self._close_vis(i) and not closing:
                cr = QRectF(r.right() - 27, r.center().y() - 11, 22, 22)
                cv = self._cv.get(id(self.tabData(i)), 0.0)
                if cv > 0.02:
                    p.setBrush(QColor(255, 255, 255, int((60 if self._pc == i else 42) * cv)))
                    p.setPen(Qt.PenStyle.NoPen)
                    p.drawEllipse(cr)
                pen = QPen(QColor(255, 235, 238, int(150 + 100 * cv)), 1.6)
                pen.setCapStyle(Qt.PenCapStyle.RoundCap)
                p.setPen(pen)
                c = cr.center()
                k = 3.6
                p.drawLine(QPointF(c.x() - k, c.y() - k), QPointF(c.x() + k, c.y() + k))
                p.drawLine(QPointF(c.x() - k, c.y() + k), QPointF(c.x() + k, c.y() - k))
            if getattr(self.tabData(i), "audible", False):          # speaker badge on a tab that is playing sound
                btn = self.tabButton(i, QTabBar.ButtonPosition.RightSide)
                x = r.right() - (38 if (btn is not None and btn.isVisible()) else 22)
                if self._spk is None:
                    self._spk = pm_icon("speaker", "#ffd3d8", size=32)
                p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
                p.drawPixmap(QRectF(x, r.center().y() - 7, 14, 14).toRect(), self._spk)
            p.setOpacity(1.0)
        p.end()
        super().paintEvent(e)

    # ---- mouse ------------------------------------------------------------------------
    def leaveEvent(self, e):
        self._hover = -1
        self._ch = -1
        self._pc = None
        if self._hold:
            self._hold = False
            self.refit(True)                             # tabs spread back out once the mouse has left
        self._apply_close()
        self._ease_start()
        self.update()
        super().leaveEvent(e)

    def mousePressEvent(self, e):
        pos = e.position().toPoint()
        i = self.tabAt(pos)
        if e.button() == Qt.MouseButton.LeftButton and i < 0:
            self._empty = True
            e.accept()
            return
        self._empty = False
        if e.button() == Qt.MouseButton.LeftButton and i >= 0 and self._close_vis(i) and self._cr(i).contains(QPointF(pos)):
            self._pc = i                                 # pressing an X must not select or drag the tab
            self.update()
            e.accept()
            return
        if e.button() == Qt.MouseButton.LeftButton:
            self._on_tab = True
            self._dragging = False
            self._grab = pos.x() - self.tabRect(i).left()
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        pos = e.position().toPoint()
        h = self.tabAt(pos)
        ch = h if (h >= 0 and self._close_vis(h) and self._cr(h).contains(QPointF(pos))) else -1
        if h != self._hover or ch != self._ch:
            self._hover = h
            self._ch = ch
            self.setCursor(Qt.CursorShape.PointingHandCursor if ch >= 0 else Qt.CursorShape.ArrowCursor)
            self._apply_close()
            self._ease_start()
            self.update()
        if self._empty:
            if e.buttons() & Qt.MouseButton.LeftButton:
                self._empty = False
                self.win.start_move()
            return
        if self._on_tab and e.buttons() & Qt.MouseButton.LeftButton:
            self._mx = pos.x()
            if not self._dragging and abs(pos.x() - (self.tabRect(self.currentIndex()).left() + self._grab)) > 6:
                self._dragging = True
            self.update()
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        if self._empty:
            self._empty = False
            return
        if self._pc is not None:
            i, self._pc = self._pc, None
            self.update()
            if e.button() == Qt.MouseButton.LeftButton and i < self.count() and self._cr(i).contains(QPointF(e.position())):
                self._hold = True
                self.tabCloseRequested.emit(i)
            e.accept()
            return
        if e.button() == Qt.MouseButton.MiddleButton:          # middle-click closes a tab
            i = self.tabAt(e.position().toPoint())
            if i >= 0:
                self._hold = True
                self.tabCloseRequested.emit(i)
                e.accept()
                return
        self._on_tab = False
        self._dragging = False
        super().mouseReleaseEvent(e)
        self.update()

    def mouseDoubleClickEvent(self, e):
        if self.tabAt(e.position().toPoint()) < 0:
            self._empty = False
            self.win.toggle_max()
            e.accept()
            return
        super().mouseDoubleClickEvent(e)


class CaptionButton(HoverButton):
    """Minimize / maximize / close button in the title bar."""

    def __init__(self, kind, tip, fn, danger=False):
        super().__init__()
        self.setObjectName("wc")
        self.danger = danger
        self.setToolTip(tip)
        self.setIcon(QIcon(pm_icon(kind, width=3.2)))
        self.setIconSize(QSize(18, 18))
        self.setFixedSize(46, 30)
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.clicked.connect(lambda _=False: fn())

    def paintEvent(self, e):
        h = self._h
        if h > 0.01 or self.isDown():
            p = QPainter(self)
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            if self.danger:
                col = QColor(255, 77, 94, int(215 * max(h, 0.6 if self.isDown() else 0)))
            else:
                col = QColor(255, 255, 255, int(46 * h) + (30 if self.isDown() else 0))
            p.setBrush(col)
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRoundedRect(QRectF(self.rect()).adjusted(3, 1, -3, -1), 9, 9)
            p.end()
        QToolButton.paintEvent(self, e)


class Browser(QMainWindow):
    shortcuts_done = pyqtSignal(list, bool)
    sync_ready = pyqtSignal(list)

    def __init__(self, start_url):
        super().__init__()
        self.setWindowTitle("LiteBrowser")
        self.setWindowFlag(Qt.WindowType.FramelessWindowHint, True)
        self.resize(1200, 800)
        self._maxed = False
        self._fs = False
        self._normal_geo = QRect()
        self._busy = False
        self.closed_tabs = []
        self.last_active = {}
        self.toast_label = None
        self.bm = load_bookmarks()
        self.history = History()
        self._sess_last = None
        self._shield_txt = None
        self._loading = False
        self._pending_typed = None
        self._perm_q = []
        self._active = None
        self._bm_urls = None
        self.downloads = []
        self._bm_sig = None
        self._fav_ver = 0
        self._fav_cache = {}
        self._no_save = False
        self.ext_ui = load_ext_ui()
        self._ext_icons = {}
        self._panel = None
        self._settings = None
        self._gwin = None
        self._hwin = None
        self._devtools = None
        self.gsync = load_gsync()
        self._queue, self._batch_ids, self._batch_ok, self._batch_fail, self._installing = [], set(), 0, 0, False
        self._store_id = None
        self._store_dismissed = set()
        self._last_n = None
        self.installer = Installer()
        self.installer.done.connect(self.on_installed)
        self.shortcuts_done.connect(self.on_shortcuts)
        self.sync_ready.connect(self._apply_auto_sync)
        self._clock = ""
        self.bm_timer = QTimer(self)
        self.bm_timer.setSingleShot(True)
        self.bm_timer.setInterval(80)
        self.bm_timer.timeout.connect(self.refresh_bookmarks)

        # --- profile, ad blocker, extensions ------------------------------
        self.profile = QWebEngineProfile("lite", self)
        # Always keep cookies/logins in our own fixed folder: Qt's default folder depends on how the app was started
        # (python vs pythonw vs the .exe), which made every launch method look like a fresh, logged-out browser.
        self.profile.setPersistentStoragePath(str(DATA / "web"))
        self.profile.setCachePath(str(DATA / "web-cache"))
        try:                                             # keep "session" cookies too, so closing the browser doesn't sign you out
            self.profile.setPersistentCookiesPolicy(QWebEngineProfile.PersistentCookiesPolicy.ForcePersistentCookies)
        except Exception:
            pass
        self.profile.setHttpCacheType(QWebEngineProfile.HttpCacheType.DiskHttpCache)
        self.profile.setHttpCacheMaximumSize(64 * 1024 * 1024)
        try:  # Google refuses sign-in from browsers that announce 'QtWebEngine'
            self.profile.setHttpUserAgent(re.sub(r"\s*QtWebEngine/\S+", "", self.profile.httpUserAgent()))
        except Exception:
            pass
        self.profile.downloadRequested.connect(self.on_download)
        self.cookies = CookieJar(self.profile.cookieStore(), self)      # our own copy of all cookies (keeps you signed in)
        self.cookies.restore()
        s = self.profile.settings()
        s.setAttribute(QWebEngineSettings.WebAttribute.PluginsEnabled, False)
        s.setAttribute(QWebEngineSettings.WebAttribute.ScrollAnimatorEnabled, False)
        s.setAttribute(QWebEngineSettings.WebAttribute.WebGLEnabled, True)       # bot checks treat 'no WebGL' as a fake browser
        s.setAttribute(QWebEngineSettings.WebAttribute.FullScreenSupportEnabled, True)

        self.adblock = AdBlock()
        self.adblock.allow = set(load_json(PREFS_FILE, {}).get("adblock_allow", []))
        self.profile.setUrlRequestInterceptor(self.adblock)
        self.cosmetic = QWebEngineScript()
        self.cosmetic.setName("cosmetic-adblock")
        self.cosmetic.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
        self.cosmetic.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        self.cosmetic.setRunsOnSubFrames(True)
        self.cosmetic.setSourceCode(
            "(function(){var css=%r;function add(){var s=document.createElement('style');s.textContent=css;"
            "(document.head||document.documentElement).appendChild(s)}"
            "if(document.documentElement){add()}else{new MutationObserver(function(m,o){if(document.documentElement){o.disconnect();add()}})"
            ".observe(document,{childList:true})}})();" % COSMETIC_CSS)
        self.profile.scripts().insert(self.cosmetic)
        self.compat_js = QWebEngineScript()               # a real Chrome has window.chrome; checks look for it
        self.compat_js.setName("chrome-object")
        self.compat_js.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
        self.compat_js.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        self.compat_js.setRunsOnSubFrames(True)
        self.compat_js.setSourceCode(
            "(function(){try{if(!window.chrome){Object.defineProperty(window,'chrome',{value:{app:{isInstalled:false},"
            "csi:function(){return {}},loadTimes:function(){return {}}},writable:true,configurable:true,enumerable:true})}}catch(e){}})();")
        self.profile.scripts().insert(self.compat_js)
        self.webauthn_js = QWebEngineScript()             # no automatic passkey pop-up on login pages
        self.webauthn_js.setName("passkey-quiet")
        self.webauthn_js.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
        self.webauthn_js.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        self.webauthn_js.setRunsOnSubFrames(True)
        self.passkeys_on = load_json(PREFS_FILE, {}).get("passkeys", True)
        self.webauthn_js.setSourceCode(
            "(function(){try{var ON=%s;"
            "function deny(m){return Promise.reject(new DOMException(m,'NotAllowedError'))}"
            "function act(){try{return !navigator.userActivation||navigator.userActivation.isActive}catch(e){return true}}"
            "if(window.PublicKeyCredential){"
            "['isConditionalMediationAvailable','isUserVerifyingPlatformAuthenticatorAvailable'].forEach(function(k){"
            "try{Object.defineProperty(PublicKeyCredential,k,{value:function(){return Promise.resolve(false)},writable:true,configurable:true})}catch(e){}})}"
            "if(navigator.credentials){['get','create'].forEach(function(k){var orig=navigator.credentials[k];if(!orig)return;"
            "Object.defineProperty(navigator.credentials,k,{value:function(o){"
            "if(o&&o.publicKey){"
            "if(o.mediation==='conditional')return deny('Passkey autofill is not available in this browser');"
            "if(!ON)return deny('Passkeys are turned off in LiteBrowser');"
            "if(!act())return deny('A passkey prompt needs a click first')}"
            "return orig.apply(this,arguments)},writable:true,configurable:true})})}"
            "}catch(e){}})();" % ("true" if self.passkeys_on else "false"))
        if BLOCK_CONDITIONAL_PASSKEYS:
            self.profile.scripts().insert(self.webauthn_js)
        self.signin_js = QWebEngineScript()               # makes the page's own view of the browser match the header
        self.signin_js.setName("signin-compat")
        self.signin_js.setInjectionPoint(QWebEngineScript.InjectionPoint.DocumentCreation)
        self.signin_js.setWorldId(QWebEngineScript.ScriptWorldId.MainWorld)
        self.signin_js.setRunsOnSubFrames(True)
        self.signin_js.setSourceCode(
            "(function(){var h=location.hostname;if(h!=='accounts.google.com'&&h!=='accounts.youtube.com')return;"
            "function d(k,v){try{Object.defineProperty(Navigator.prototype,k,{get:function(){return v},configurable:true})}catch(e){}}"
            "d('userAgent',%r);d('appVersion','5.0 (Windows)');d('vendor','');d('productSub','20100101');d('userAgentData',undefined);"
            "try{Object.defineProperty(window,'chrome',{value:undefined,configurable:true})}catch(e){}})();" % FIREFOX_UA)
        if SIGNIN_COMPAT:
            self.profile.scripts().insert(self.signin_js)
        _mark("init_profile")

        self.selfup = SelfUpdater()
        self.selfup.result.connect(self.on_selfupdate)
        self._manual_check = False
        self.updater = Updater()
        self.updater.done.connect(self.on_list_updated)

        self.ext_mgr = None
        EXT_DIR.mkdir(parents=True, exist_ok=True)
        try:
            self.ext_mgr = self.profile.extensionManager()
            self.ext_mgr.loadFinished.connect(self.on_ext_loaded)
            for d in sorted(EXT_DIR.iterdir()):
                if (d / "manifest.json").exists() and not d.name.endswith(".tmp"):
                    self.ext_mgr.loadExtension(str(d))
        except Exception:
            self.ext_mgr = None  # Qt < 6.10

        _mark("init_ext")
        # --- UI ------------------------------------------------------------
        root = Backdrop(objectName="root")
        self.root = root
        root.setMouseTracking(True)
        root.installEventFilter(self)
        col = QVBoxLayout(root)
        self.root_layout = col
        col.setContentsMargins(6, 6, 6, 6)
        col.setSpacing(0)

        tabwrap = TitleBar(self, objectName="tabwrap")
        tl = QHBoxLayout(tabwrap)
        tl.setContentsMargins(8, 4, 2, 2)
        tl.setSpacing(0)
        logo = HoverButton(objectName="nav", toolTip="LiteBrowser menu")
        logo.setIcon(QIcon(make_app_icon(96)))
        logo.setIconSize(QSize(22, 22))
        logo.setFixedSize(32, 32)
        logo.setCursor(Qt.CursorShape.PointingHandCursor)
        logo.clicked.connect(lambda: self.show_menu(logo))
        tl.addWidget(logo)
        tl.addSpacing(8)
        self.tabbar = TabBar(self, documentMode=True, tabsClosable=True, movable=True,
                             expanding=False, drawBase=False)
        self.tabbar.setElideMode(Qt.TextElideMode.ElideRight)
        self.tabbar.tabCloseRequested.connect(self.close_tab_animated)
        self.tabbar.currentChanged.connect(self.show_tab)
        tl.addWidget(self.tabbar)
        newtab = HoverButton(objectName="nav", toolTip="New tab (Ctrl+T)")
        newtab.setIcon(QIcon(pm_icon("plus", width=3.6)))
        newtab.setIconSize(QSize(18, 18))
        newtab.setFixedSize(32, 32)
        newtab.setCursor(Qt.CursorShape.PointingHandCursor)
        newtab.clicked.connect(lambda: self.add_tab("start"))
        tl.addSpacing(4)
        tl.addWidget(newtab)
        tl.addStretch(1)
        self.min_btn = CaptionButton("min", "Minimize", self.showMinimized)
        self.max_btn = CaptionButton("max", "Maximize", self.toggle_max)
        self.close_btn = CaptionButton("close", "Close", self.close, danger=True)
        for b in (self.min_btn, self.max_btn, self.close_btn):
            tl.addWidget(b)
        col.addWidget(tabwrap)
        self.tabwrap = tabwrap

        barwrap = GlassBar(objectName="barwrap")
        bl = QHBoxLayout(barwrap)
        bl.setContentsMargins(8, 4, 8, 4)
        self.bar = QWidget(objectName="bar")
        row = QHBoxLayout(self.bar)
        row.setContentsMargins(0, 0, 0, 0)
        row.setSpacing(4)
        def nav_btn(kind, tip, fn):
            b = HoverButton(objectName="nav", toolTip=tip)
            b.setIcon(QIcon(pm_icon(kind)))
            b.setIconSize(QSize(20, 20))
            b.setFixedSize(32, 32)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.clicked.connect(fn)
            return b

        row.addWidget(nav_btn("back", "Back", lambda: self.cur().back()))
        row.addWidget(nav_btn("forward", "Forward", lambda: self.cur().forward()))
        self.ic_reload = QIcon(pm_icon("reload"))
        self.ic_stop = QIcon(pm_icon("close", width=3.6))
        self.reload_btn = nav_btn("reload", "Reload", self.reload_or_stop)
        row.addWidget(self.reload_btn)
        self.urlbar = UrlBar(placeholderText="Search with Google or enter address")
        self.urlbar.setFixedHeight(36)
        self.urlbar.returnPressed.connect(self.navigate)
        self.sug = Suggest(self)
        self.urlbar.sug = self.sug
        self.urlbar.textEdited.connect(self.on_url_typed)
        self.urlbar.chosen.connect(self.open_input)
        self.urlbar.escaped.connect(lambda: self.cur().setFocus())
        self.sug.picked.connect(self.open_input)
        self.ic_star = QIcon(pm_icon("star", "#d9a4ac", width=3.2))
        self.ic_star_on = QIcon(pm_icon("star", "#ff8f9c", width=3.2, fill=True))
        self.ic_globe = QIcon(pm_icon("globe", "#d9a4ac", width=3))
        self.ic_folder = QIcon(pm_icon("folder", "#ffb3bb", width=3.0))
        self.star_act = QAction(self.ic_star, "Bookmark this page (Ctrl+D)", self)
        self.star_act.triggered.connect(self.toggle_bookmark)
        self.urlbar.addAction(self.star_act, QLineEdit.ActionPosition.TrailingPosition)
        self.star_act.setVisible(False)
        self.ic_lock = QIcon(pm_icon("lock", "#d9a4ac", width=3.2))
        self.ic_unlock = QIcon(pm_icon("unlock", "#ff8f9c", width=3.2))
        self.ic_search = QIcon(pm_icon("search", "#d9a4ac", width=3.2))
        self.lock_act = QAction(self.ic_search, "", self)
        self.urlbar.addAction(self.lock_act, QLineEdit.ActionPosition.LeadingPosition)
        row.addWidget(self.urlbar, 1)
        self.pin_lay = QHBoxLayout()
        self.pin_lay.setSpacing(8)
        self.pin_lay.setContentsMargins(0, 0, 0, 0)
        row.addLayout(self.pin_lay)
        self.ext_btn = nav_btn("puzzle", "Extensions", self.show_extensions)
        row.addWidget(self.ext_btn)
        self.ic_shield_on = QIcon(pm_icon("shield", "#ff9aa5"))
        self.ic_shield_off = QIcon(pm_icon("shield", "#a77880", off=True))
        self._shield_state = None
        self.shield = HoverButton(objectName="shield", toolTip="Trackers & ads blocked (click to toggle blocker)")
        self.shield.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.shield.setIconSize(QSize(18, 18))
        self.shield.setFixedHeight(32)
        self.shield.setCursor(Qt.CursorShape.PointingHandCursor)
        self.shield.clicked.connect(self.toggle_adblock)
        row.addWidget(self.shield)
        row.addWidget(nav_btn("person", "Google accounts & sync", self.show_google))
        more = nav_btn("dots", "Menu", lambda: None)
        more.clicked.disconnect()
        more.clicked.connect(lambda: self.show_menu(more))
        row.addWidget(more)
        bl.addWidget(self.bar)
        col.addSpacing(2)
        col.addWidget(barwrap)
        col.addSpacing(6)
        self.barwrap = barwrap

        self.bmbar = QWidget(objectName="bmbar")
        self.bm_layout = QHBoxLayout(self.bmbar)
        self.bm_layout.setContentsMargins(16, 0, 16, 7)
        self.bm_layout.setSpacing(6)
        col.addWidget(self.bmbar)
        self.bm_col = Collapser(self.bmbar, 37, shown=self.bm["show"])

        self.storewrap = QWidget(objectName="storewrap")
        sw = QHBoxLayout(self.storewrap)
        sw.setContentsMargins(16, 0, 16, 8)
        pill = QFrame(objectName="storepill")
        pl = QHBoxLayout(pill)
        pl.setContentsMargins(14, 6, 8, 6)
        pl.setSpacing(10)
        sic = QLabel()
        sic.setPixmap(QIcon(pm_icon("puzzle", "#ff9aa5", width=3.2)).pixmap(QSize(20, 20)))
        pl.addWidget(sic)
        self.store_label = QLabel("", objectName="extname")
        pl.addWidget(self.store_label, 1)
        self.store_btn = HoverButton(objectName="chip")
        self.store_btn.setText("Add to LiteBrowser")
        self.store_btn.setFixedHeight(28)
        self.store_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.store_btn.clicked.connect(self.install_current)
        pl.addWidget(self.store_btn)
        sx = HoverButton(objectName="flat")
        sx.setIcon(QIcon(pm_icon("close", width=4)))
        sx.setIconSize(QSize(14, 14))
        sx.setFixedSize(28, 28)
        sx.clicked.connect(self.dismiss_store)
        pl.addWidget(sx)
        sw.addWidget(pill)
        col.addWidget(self.storewrap)
        self.store_col = Collapser(self.storewrap, 46, shown=False)
        self.defwrap, self.def_label, self.def_btn = self._make_infobar(
            "globe", "Set as default", self.make_default_from_bar, self.dismiss_default)
        self.def_label.setText("Make LiteBrowser your default browser?")
        col.addWidget(self.defwrap)
        self.def_col = Collapser(self.defwrap, 46, shown=False)

        self.permwrap, self.perm_label, self.perm_btn = self._make_infobar(
            "lock", "Allow", self._perm_allow, self._perm_deny)       # site asks for camera / microphone / location
        col.addWidget(self.permwrap)
        self.perm_col = Collapser(self.permwrap, 46, shown=False)

        self.findwrap = QWidget(objectName="storewrap")                # find in page (Ctrl+F)
        fw = QHBoxLayout(self.findwrap)
        fw.setContentsMargins(16, 0, 16, 8)
        fpill = QFrame(objectName="storepill")
        fl = QHBoxLayout(fpill)
        fl.setContentsMargins(12, 5, 6, 5)
        fl.setSpacing(6)
        self.find_edit = FindEdit(placeholderText="Find in page")
        self.find_edit.setFixedSize(260, 30)
        fl.addWidget(self.find_edit)
        self.find_label = QLabel("", objectName="extmeta")
        self.find_label.setMinimumWidth(70)
        fl.addWidget(self.find_label)
        for kind, tip, fn in (("up", "Previous (Shift+Enter)", lambda: self.do_find(False)),
                              ("down", "Next (Enter)", lambda: self.do_find(True)),
                              ("close", "Close (Esc)", lambda: self.hide_find())):
            fb = HoverButton(objectName="flat")
            fb.setIcon(QIcon(pm_icon(kind, width=4 if kind == "close" else 3.6)))
            fb.setIconSize(QSize(16, 16))
            fb.setFixedSize(28, 28)
            fb.setToolTip(tip)
            fb.clicked.connect(lambda _=False, f=fn: f())
            fl.addWidget(fb)
        fw.addWidget(fpill)
        fw.addStretch(1)
        col.addWidget(self.findwrap)
        self.find_col = Collapser(self.findwrap, 46, shown=False)
        self.find_edit.textChanged.connect(lambda _t: self.do_find(True))
        self.find_edit.returnPressed.connect(lambda: self.do_find(True))
        self.find_edit.prev.connect(lambda: self.do_find(False))
        self.find_edit.closed.connect(lambda: self.hide_find())

        self.progress = QProgressBar(textVisible=False, maximum=100)
        col.addWidget(self.progress)
        self.prog_anim = QPropertyAnimation(self.progress, b"value", self)
        self.prog_anim.setDuration(240)
        self.prog_anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        content = QWidget(objectName="content")
        cl = QVBoxLayout(content)
        cl.setContentsMargins(4, 2, 4, 4)
        frame = CardFrame()
        fl = QVBoxLayout(frame)
        fl.setContentsMargins(1, 1, 1, 1)
        self.stack = Card()
        fl.addWidget(self.stack)
        cl.addWidget(frame)
        col.addWidget(content, 1)
        self.setCentralWidget(root)
        self._apply_chrome()
        _mark("init_ui")

        for key, fn in [("Ctrl+T", lambda: self.add_tab("start")),
                        ("Ctrl+W", lambda: self.close_tab_animated(self.tabbar.currentIndex())),
                        ("Ctrl+L", self.focus_bar), ("Ctrl+D", self.toggle_bookmark), ("Ctrl+Shift+T", self.reopen_tab), ("Ctrl+H", self.show_history),
                        ("Ctrl+Shift+B", self.toggle_bm_bar), ("F5", lambda: self.cur().reload()),
                        ("Alt+Left", lambda: self.cur().back()),
                        ("Alt+Right", lambda: self.cur().forward()),
                        ("Ctrl+Tab", lambda: self.cycle(1)),
                        ("Ctrl+Shift+Tab", lambda: self.cycle(-1)),
                        ("Ctrl+=", lambda: self.zoom(0.1)), ("Ctrl+-", lambda: self.zoom(-0.1)),
                        ("Ctrl+0", self.zoom_reset), ("Ctrl++", lambda: self.zoom(0.1)),
                        ("Ctrl+F", self.show_find), ("F3", lambda: self.find_next(True)),
                        ("Shift+F3", lambda: self.find_next(False)),
                        ("F11", lambda: self.set_fullscreen(not self._fs)),
                        ("F12", self.show_devtools), ("Ctrl+Shift+I", self.show_devtools)]:
            QShortcut(QKeySequence(key), self, activated=fn)
        for n in range(1, 10):                        # Ctrl+1..8 = that tab, Ctrl+9 = last tab
            QShortcut(QKeySequence(f"Ctrl+{n}"), self, activated=lambda n=n: self.goto_tab(n - 1 if n < 9 else -1))

        self.tick_timer = QTimer(self)
        self.tick_timer.setTimerType(Qt.TimerType.VeryCoarseTimer)
        self.tick_timer.timeout.connect(self.tick)
        self.tick_timer.start(1000)
        self._house_n = 0
        self.house_timer = QTimer(self)             # one low-frequency timer replaces four separate ones
        self.house_timer.setTimerType(Qt.TimerType.VeryCoarseTimer)
        self.house_timer.timeout.connect(self.housekeeping)
        self.house_timer.start(5000)

        restored = self.restore_session(activate=not start_url)
        if start_url:
            self.add_tab(start_url)
        elif not restored:
            self.add_tab("start")
        self.tick()
        _mark("init_first_tab")
        self.refresh_bookmarks(stagger=True)
        self.refresh_ext_pins()
        QTimer.singleShot(2000, self.maybe_ask_default)
        QTimer.singleShot(2500, self.auto_sync)
        QTimer.singleShot(3500, self.ensure_shortcut)
        QTimer.singleShot(9000, self.auto_check_updates)
        gt = QTimer(self)
        gt.timeout.connect(self.auto_sync)
        gt.start(30 * 60 * 1000)

    # --- custom window chrome: title bar merged into the tab strip --------------------
    def _apply_chrome(self):
        m = 0 if (self._maxed or self._fs) else 6
        self.root_layout.setContentsMargins(m, m, m, m)
        self.max_btn.setIcon(QIcon(pm_icon("restore" if self._maxed else "max", width=3.2)))
        self.max_btn.setToolTip("Restore" if self._maxed else "Maximize")
        if self.isVisible():
            self._win_corners(not (self._maxed or self._fs))

    def _set_max(self, on, restore_geo=None):
        if on == self._maxed:
            return
        if on:
            self._normal_geo = self.geometry()
            self._maxed = True
            self.setGeometry(self.screen().availableGeometry())
        else:
            self._maxed = False
            g = restore_geo if restore_geo is not None else self._normal_geo
            if g.isValid() and not g.isEmpty():
                self.setGeometry(g)
        self._apply_chrome()

    def toggle_max(self):
        if self._fs:
            return
        self._set_max(not self._maxed)

    def start_move(self):
        if self._fs:
            return
        if self._maxed:
            cur = QCursor.pos()
            g = self._normal_geo if self._normal_geo.isValid() else QRect(0, 0, 1200, 800)
            ratio = (cur.x() - self.x()) / max(1, self.width())
            self._set_max(False, QRect(cur.x() - int(g.width() * ratio), cur.y() - 18, g.width(), g.height()))
        wh = self.windowHandle()
        if wh is not None:
            wh.startSystemMove()

    def changeEvent(self, e):
        super().changeEvent(e)
        # Windows snap-to-top (or Win+Up) maximizes natively; swap it for our taskbar-safe maximize
        if e.type() == QEvent.Type.WindowStateChange and self.isMaximized() and not self._fs and not self._busy:
            QTimer.singleShot(0, self._fix_native_max)
        if e.type() == QEvent.Type.ActivationChange and not self.isActiveWindow():
            sg = getattr(self, "sug", None)
            if sg is not None:
                sg.hide()
        if e.type() == QEvent.Type.WindowStateChange:      # no UI ticking while minimized
            tt = getattr(self, "tick_timer", None)
            if tt is not None:
                if self.isMinimized():
                    tt.stop()
                elif not tt.isActive():
                    tt.start()
                    self.tick()

    def closeEvent(self, e):
        self.save_session()
        self.history.flush()
        for w in (self._settings, self._gwin, self._hwin, self._panel, self._devtools, getattr(self, "sug", None)):
            try:
                if w is not None:
                    w.close()
            except RuntimeError:
                pass
        super().closeEvent(e)

    def _fix_native_max(self):
        if not self.isMaximized() or self._busy:
            return
        self._busy = True
        self.showNormal()
        self._maxed = False
        self._set_max(True)
        self._busy = False

    def _edges(self, pos):
        m, c = 6, 14
        x, y, w, h = pos.x(), pos.y(), self.width(), self.height()
        l, r, t, b = x <= m, x >= w - m, y <= m, y >= h - m
        if t or b:
            l, r = l or x <= c, r or x >= w - c
        if l or r:
            t, b = t or y <= c, b or y >= h - c
        e = Qt.Edge(0)
        if l:
            e |= Qt.Edge.LeftEdge
        if r:
            e |= Qt.Edge.RightEdge
        if t:
            e |= Qt.Edge.TopEdge
        if b:
            e |= Qt.Edge.BottomEdge
        return e, (l, r, t, b)

    def eventFilter(self, obj, ev):
        if obj is self.root and not (self._maxed or self._fs):
            et = ev.type()
            if et in (QEvent.Type.MouseMove, QEvent.Type.MouseButtonPress):
                edges, (l, r, t, b) = self._edges(ev.position().toPoint())
                if et == QEvent.Type.MouseMove:
                    if edges:
                        if (l and t) or (r and b):
                            shape = Qt.CursorShape.SizeFDiagCursor
                        elif (r and t) or (l and b):
                            shape = Qt.CursorShape.SizeBDiagCursor
                        elif l or r:
                            shape = Qt.CursorShape.SizeHorCursor
                        else:
                            shape = Qt.CursorShape.SizeVerCursor
                        self.root.setCursor(shape)
                    else:
                        self.root.unsetCursor()
                elif edges and ev.button() == Qt.MouseButton.LeftButton:
                    wh = self.windowHandle()
                    if wh is not None:
                        wh.startSystemResize(edges)
                        return True
            elif et == QEvent.Type.Leave:
                self.root.unsetCursor()
        return super().eventFilter(obj, ev)

    # --- helpers -------------------------------------------------------------
    def showEvent(self, e):
        super().showEvent(e)
        self._win_corners(not (self._maxed or self._fs))

    def _win_corners(self, rounded):
        """Windows 11: let the system round the window corners and draw a thin dark-red outline."""
        if sys.platform != "win32":
            return
        try:
            import ctypes
            hwnd = int(self.winId())
            dwm = ctypes.windll.dwmapi
            dwm.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(ctypes.c_int(1)), 4)
            dwm.DwmSetWindowAttribute(hwnd, 33, ctypes.byref(ctypes.c_int(2 if rounded else 1)), 4)
            dwm.DwmSetWindowAttribute(hwnd, 34, ctypes.byref(ctypes.c_uint(0x2A1A5B if rounded else 0xFFFFFFFE)), 4)
        except Exception:
            pass

    def cur(self):
        return self.stack.currentWidget()

    def tab_of(self, view):
        for n in range(self.tabbar.count()):
            if self.tabbar.tabData(n) is view:
                return n
        return -1

    def focus_bar(self):
        self.urlbar.setFocus()
        self.urlbar.selectAll()

    def cycle(self, step):
        n = self.tabbar.count()
        self.tabbar.setCurrentIndex((self.tabbar.currentIndex() + step) % n)

    def zoom(self, d):
        v = self.cur()
        f = max(0.25, min(5.0, v.zoomFactor() + d))
        v.setZoomFactor(f)
        self.toast(f"Zoom {round(f * 100)}%")

    def zoom_reset(self):
        self.cur().setZoomFactor(1.0)
        self.toast("Zoom 100%")

    def goto_tab(self, n):
        c = self.tabbar.count()
        if c:
            self.tabbar.setCurrentIndex(c - 1 if n < 0 else min(n, c - 1))

    def show_find(self):
        if self.cur() is None:
            return
        self.find_col.set(True)
        self.find_edit.setFocus()
        self.find_edit.selectAll()
        if self.find_edit.text():
            self.do_find(True)

    def hide_find(self, refocus=True, page=None):
        self.find_col.set(False)
        try:
            (page or self.cur().page()).findText("")           # clears the highlights
        except Exception:
            pass
        self.find_label.setText("")
        if refocus and self.cur() is not None:
            self.cur().setFocus()

    def do_find(self, forward=True):
        v = self.cur()
        if v is None:
            return
        text = self.find_edit.text()
        if not text:
            v.page().findText("")
            self.find_label.setText("")
            return
        flags = QWebEnginePage.FindFlag(0) if forward else QWebEnginePage.FindFlag.FindBackward
        v.page().findText(text, flags)

    def on_find_result(self, v, r):
        if v is not self.cur():
            return
        n = r.numberOfMatches()
        self.find_label.setText(f"{r.activeMatchOrdinal()}/{n}" if n else ("No results" if self.find_edit.text() else ""))

    def find_next(self, forward):
        if not self.find_col.shown:
            self.show_find()
        else:
            self.do_find(forward)

    def toast(self, text):
        if self.toast_label:
            try:
                self.toast_label.deleteLater()
            except RuntimeError:
                pass
        lab = QLabel(text, self, objectName="toast")
        lab.setWordWrap(True)
        lab.setMaximumWidth(560)
        lab.adjustSize()
        x = (self.width() - lab.width()) // 2
        y = self.height() - lab.height() - 28
        eff = QGraphicsOpacityEffect(lab)
        eff.setOpacity(0.0)
        lab.setGraphicsEffect(eff)
        lab.move(x, y + 16)
        lab.show()
        lab.raise_()
        grp = QParallelAnimationGroup(lab)
        a1 = QPropertyAnimation(eff, b"opacity", lab)
        a1.setDuration(220)
        a1.setStartValue(0.0)
        a1.setEndValue(1.0)
        a2 = QPropertyAnimation(lab, b"pos", lab)
        a2.setDuration(300)
        a2.setStartValue(QPoint(x, y + 16))
        a2.setEndValue(QPoint(x, y))
        a2.setEasingCurve(QEasingCurve.Type.OutBack)
        grp.addAnimation(a1)
        grp.addAnimation(a2)
        grp.start()
        self.toast_label = lab

        def out():
            try:
                fo = QPropertyAnimation(eff, b"opacity", lab)
                fo.setDuration(300)
                fo.setStartValue(1.0)
                fo.setEndValue(0.0)
                fo.finished.connect(lab.deleteLater)
                fo.start()
            except RuntimeError:
                pass
        QTimer.singleShot(3200, out)

    def _set_loading(self, loading):
        if loading == self._loading:
            return
        self._loading = loading
        self.reload_btn.setIcon(self.ic_stop if loading else self.ic_reload)
        self.reload_btn.setToolTip("Stop loading" if loading else "Reload")

    def reload_or_stop(self):
        if self._loading:
            self.cur().stop()
        else:
            self.cur().reload()

    def _set_title(self, t):
        self.setWindowTitle(f"{t} - LiteBrowser" if t and t != "New Tab" else "LiteBrowser")

    def set_progress(self, p):
        self._set_loading(p < 100)
        self.prog_anim.stop()
        self.prog_anim.setStartValue(self.progress.value())
        self.prog_anim.setEndValue(p)
        self.prog_anim.start()
        if p >= 100:
            QTimer.singleShot(420, lambda: self.progress.setValue(0) if self.progress.value() >= 100 else None)

    def on_title(self, v, t):
        v.title_text = t or "New Tab"
        u = v.url().toString()
        if t and u.startswith("http"):
            self.history.set_title(u, t)
        i = self.tab_of(v)
        if i >= 0:
            self.tabbar.set_title(i)
        if v is self.cur():
            self._set_title(v.title_text)
            self.update_store_bar()

    def tick(self):
        on = self.adblock.enabled
        if on != self._shield_state:
            self.shield.setIcon(self.ic_shield_on if on else self.ic_shield_off)
            self._shield_state = on
        n = self.adblock.snapshot()["blocked"]
        if on and self._last_n is not None and n > self._last_n:
            self.shield.pulse()
        self._last_n = n
        txt = f" {n:,}" if on else " off"
        if txt != self._shield_txt:
            self._shield_txt = txt
            self.shield.setText(txt)
        v = self.cur()
        if v is not None and getattr(v, "is_start", False):
            snap = self.adblock.snapshot()
            key = (snap["blocked"], snap["bytes"], snap["ms"])
            if key != getattr(v, "_pushed", None):
                v._pushed = key
                v.page().runJavaScript("window.setStats&&window.setStats(%s)" % json.dumps(snap))

    # --- tabs --------------------------------------------------------------
    def _make_view(self):
        v = QWebEngineView()
        v.is_start = False
        v.tint = None
        v.title_text = "New Tab"
        page = Page(self.profile, self)
        page.fullScreenRequested.connect(self.on_fullscreen)
        page.recentlyAudibleChanged.connect(lambda a, v=v: self.on_audible(v, a))
        page.findTextFinished.connect(lambda r, v=v: self.on_find_result(v, r))
        page.windowCloseRequested.connect(lambda v=v: self.close_by_page(v))
        if QWebEnginePermission is not None and hasattr(page, "permissionRequested"):
            page.permissionRequested.connect(self.on_permission)
        v.setPage(page)
        page.setBackgroundColor(QColor("#12030a"))
        self.stack.addWidget(v)
        v.titleChanged.connect(lambda t, v=v: self.on_title(v, t))
        v.iconChanged.connect(lambda ic, v=v: self.on_icon(v, ic))
        v.urlChanged.connect(lambda u, v=v: self.on_url(v, u))
        v.loadProgress.connect(lambda p, v=v: v is self.cur() and self.set_progress(p))
        v.loadFinished.connect(lambda _ok, v=v: v is self.cur() and self.set_progress(100))
        v.loadFinished.connect(lambda ok, v=v: self.on_loaded(v, ok))
        return v

    def add_tab(self, url="start", lazy=False, title="", background=False, after_current=False, opener=None):
        if lazy and url:
            return self._add_stub(url, title)        # restored tab: no web view until it is opened
        v = self._make_view()
        v._opener_view = opener                      # a sign-in popup talks to the page that opened it
        tb = self.tabbar
        tb.blockSignals(True)                        # show_tab runs once, explicitly (not twice via the signal)
        if after_current and tb.count():
            i = tb.insertTab(tb.currentIndex() + 1, "New Tab")
        else:
            i = tb.addTab("New Tab")
        tb.setTabData(i, v)
        tb.setTabIcon(i, self.ic_globe)
        if not background:
            tb.setCurrentIndex(i)
        tb.blockSignals(False)
        if background:
            v._bg_new = True                         # freeze it once it has finished loading
        else:
            self.show_tab(i)
        if url == "start":
            v.setHtml(START_HTML.replace("__STATS__", json.dumps(self.adblock.snapshot())))
            v.setFocus()
        elif url:
            v.setUrl(QUrl(url))
        return v

    def _add_stub(self, url, title):
        stub = TabStub(url, title)
        tb = self.tabbar
        i = tb.addTab(stub.title_text)
        tb.setTabData(i, stub)
        ic = self.fav_icon(url)
        tb.setTabIcon(i, ic)
        if self.fav_path(url).exists():
            stub.tint = tint_from_icon(ic)
        tb.set_title(i)
        return i

    def materialize(self, i):
        """Create the real web view for a placeholder tab (first time it is opened) and start loading."""
        d = self.tabbar.tabData(i)
        if not isinstance(d, TabStub):
            return d
        v = self._make_view()
        v.tint, v.title_text = d.tint, d.title_text
        self.tabbar.setTabData(i, v)
        if d.pending_url:
            v.setUrl(QUrl(d.pending_url))
        return v

    def show_tab(self, i):
        d = self.tabbar.tabData(i) if i >= 0 else None
        if d is None:
            return
        v = self.materialize(i) if isinstance(d, TabStub) else d
        prev = self._active
        if prev is not None and prev is not v:
            if self._fs:                             # never leave the window stuck in full screen
                self.set_fullscreen(False)
                try:
                    prev.page().triggerAction(QWebEnginePage.WebAction.ExitFullScreen)
                except Exception:
                    pass
            if self.find_col.shown:
                self.hide_find(refocus=False, page=prev.page())
        self.stack.setCurrentWidget(v)
        pg = v.page()
        if pg.lifecycleState() != Life.Active:
            pg.setLifecycleState(Life.Active)
        self.last_active[v] = time.time()
        self._active = v
        if prev is not None and prev is not v and getattr(v, "_opener_view", None) is not prev:   # (never freeze the opener of a popup)
            QTimer.singleShot(0, lambda p=prev: self._freeze_if_idle(p))
        self._set_loading(False)
        self._set_title(v.title_text)
        self.on_url(v, v.url())
        self.prog_anim.stop()
        self.progress.setValue(0)

    def _freeze_if_idle(self, v):
        try:
            if v is self.cur():
                return
            pg = v.page()
            if pg.recentlyAudible():                  # keep media playing in background tabs
                return
            if pg.lifecycleState() == Life.Active:
                pg.setLifecycleState(Life.Frozen)
        except RuntimeError:                          # the tab was closed meanwhile
            pass

    def close_by_page(self, v):
        """window.close() from a page (e.g. a finished sign-in popup): close that tab and go back to its opener."""
        i = self.tab_of(v)
        if i < 0 or self.tabbar.count() <= 1:
            return
        op = getattr(v, "_opener_view", None)
        if op is not None and self.tabbar.currentIndex() == i:
            j = self.tab_of(op)
            if j >= 0:
                self.tabbar.setCurrentIndex(j)
        self.close_tab(self.tab_of(v))

    def on_audible(self, v, audible):
        v.audible = audible
        self.tabbar.update()
        if not audible:                               # sound stopped: the background tab can be frozen now
            self._freeze_if_idle(v)

    def close_tab_animated(self, i):
        if i < 0:
            return
        self.tabbar.close_animated(i)

    def close_tab(self, i):
        d = self.tabbar.tabData(i)
        if self.tabbar.count() <= 1:
            self.save_session(empty=True)
            self._no_save = True
            self.close()
            return
        u = d.url().toString()
        if u and not getattr(d, "is_start", False):
            self.closed_tabs.append(u)
            del self.closed_tabs[:-20]
        self.tabbar.removeTab(i)
        if isinstance(d, TabStub):
            return
        if self._active is d:
            self._active = None
        self.stack.removeWidget(d)
        self.last_active.pop(d, None)
        try:                                   # the page is owned by the window, so without this a closed tab's
            pg = d.page()                      # renderer process and memory would stay alive until the browser quits
            d.setPage(None)
            if pg is not None:
                pg.deleteLater()
        except Exception:
            pass
        d.deleteLater()

    # --- history / address-bar suggestions ---------------------------------------------
    def on_loaded(self, v, ok):
        pt = self._pending_typed
        if pt is not None and pt[0] == id(v):
            self._pending_typed = None
            if ok:                                         # typos that never loaded are not remembered
                self.history.add_typed(pt[1])
        if getattr(v, "_bg_new", False) and v is not self.cur():
            v._bg_new = False
            QTimer.singleShot(600, lambda: self._freeze_if_idle(v))
        if not ok or getattr(v, "is_start", False):
            return
        u = v.url()
        if u.scheme() in ("http", "https") and u.host() not in SIGNIN_HOSTS and not re.search(
                r"[?&#](access_token|id_token|token|code|password|auth|session)=", u.toString(), re.I):
            self.history.visit(u.toString(), v.title())

    def show_history(self):
        try:
            if self._hwin is not None:
                self._hwin.close()
                return
        except RuntimeError:
            self._hwin = None
        w = HistoryWindow(self)
        w.destroyed.connect(lambda *_, x=w: self._hwin_gone(x))
        g = self.geometry()
        w.move(g.center().x() - w.width() // 2, g.center().y() - w.height() // 2)
        self._hwin = w
        w.show()

    def _hwin_gone(self, w):
        if self._hwin is w:
            self._hwin = None

    def on_url_typed(self, text):
        t = text.strip()
        if not t:
            self.sug.hide()
            return
        items, seen = [], set()
        for url, title in self.history.suggest(t, 5):
            seen.add(url)
            items.append((self.fav_icon(url), title or url, QUrl(url).host(), url))
        low = t.lower()
        for b in bm_walk(self.bm["items"]):
            if len(items) >= 7:
                break
            if b["url"] not in seen and (low in b["title"].lower() or low in b["url"].lower()):
                seen.add(b["url"])
                items.append((self.fav_icon(b["url"]), b["title"], "Bookmark", b["url"]))
        items.append((self.ic_search, f"Search Google for “{t[:48]}”", "", t))
        self.sug.set_items(items, max(320, self.urlbar.width()))
        self.sug.move(self.urlbar.mapToGlobal(QPoint(0, self.urlbar.height() + 4)))
        self.sug.show()
        ub = self.urlbar                                    # inline auto-complete: fill in the rest, selected
        if text == t and not ub.no_complete and ub.cursorPosition() == len(text) and not ub.hasSelectedText():
            full = self.history.complete(t) or self._complete_bookmark(t)
            if full and len(full) > len(t) and full.lower().startswith(t.lower()):
                ub.setText(t + full[len(t):])               # what you typed stays exactly as typed
                ub.setSelection(len(t), len(full) - len(t))
                ub.setModified(True)

    @staticmethod
    def _typed_key(text, url):
        """What to remember about an address the user typed (nothing for searches or non-web pages)."""
        if not url or not url.startswith(("http://", "https://")) or url.startswith(SEARCH):
            return None
        raw = (text or "").strip()
        if "://" in raw:                                    # a pasted / picked full address: remember just the site
            from urllib.parse import urlsplit
            key = urlsplit(raw).netloc.lower()
        else:
            key = re.split(r"[?#]", raw.lower())[0].rstrip("/")
        if key.startswith("www."):
            key = key[4:]
        return key or None

    def _complete_bookmark(self, text):
        low = text.lower()
        for b in bm_walk(self.bm["items"]):
            host = QUrl(b["url"]).host().lower()
            host = host[4:] if host.startswith("www.") else host
            if len(host) > len(low) and host.startswith(low):
                return host
        return None

    def open_input(self, value):
        self.sug.hide()
        self.urlbar.setText(value)
        self.navigate()

    # --- session: continue where you left off --------------------------------------------
    def save_session(self, empty=False):
        if self._no_save:
            return
        tabs, cur = [], 0
        if not empty:
            for n in range(self.tabbar.count()):
                v = self.tabbar.tabData(n)
                if v is None:
                    continue
                url = getattr(v, "pending_url", None) or ("" if getattr(v, "is_start", False) else v.url().toString())
                if not url.startswith(("http", "file")):
                    continue
                if n == self.tabbar.currentIndex():
                    cur = len(tabs)
                tabs.append({"url": url, "title": getattr(v, "title_text", "") or ""})
        txt = json.dumps({"tabs": tabs, "current": cur, "closed": self.closed_tabs[-20:]})
        if txt != self._sess_last:
            self._sess_last = txt
            try:
                DATA.mkdir(parents=True, exist_ok=True)
                SESSION_FILE.write_text(txt, encoding="utf-8")
            except OSError:
                pass

    def restore_session(self, activate=True):
        if not load_json(PREFS_FILE, {}).get("restore_tabs", True):
            return False
        d = load_json(SESSION_FILE, {})
        tabs = [t for t in d.get("tabs", []) if isinstance(t, dict) and isinstance(t.get("url"), str) and t["url"]]
        if not tabs:
            return False
        self.closed_tabs = [u for u in d.get("closed", []) if isinstance(u, str)][-20:]
        tb = self.tabbar
        tb.blockSignals(True)
        for t in tabs[:80]:                            # placeholders only: cheap, no web views yet
            self._add_stub(t["url"], str(t.get("title", "")))
        cur = d.get("current", 0)
        if not isinstance(cur, int) or not (0 <= cur < tb.count()):
            cur = 0
        tb.setCurrentIndex(cur)
        tb.blockSignals(False)
        if activate:
            self.show_tab(cur)                         # creates the web view of the active tab only
        return True

    def toggle_restore(self, on):
        prefs = load_json(PREFS_FILE, {})
        prefs["restore_tabs"] = bool(on)
        save_json(PREFS_FILE, prefs)

    # --- downloads ---------------------------------------------------------------------------
    def download_dir(self):
        p = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.DownloadLocation)
        d = Path(p) if p else Path.home() / "Downloads"
        try:
            d.mkdir(parents=True, exist_ok=True)
        except OSError:
            d = Path.home()
        return d

    def on_download(self, req):
        d = self.download_dir()
        target = d / (req.downloadFileName() or "download")
        stem, suf, n = target.stem, target.suffix, 1
        while target.exists():
            target = d / f"{stem} ({n}){suf}"
            n += 1
        req.setDownloadDirectory(str(d))
        req.setDownloadFileName(target.name)
        rec = {"name": target.name, "path": str(target), "state": "Downloading…", "pct": 0}
        self.downloads.append(rec)
        del self.downloads[:-30]
        req.receivedBytesChanged.connect(lambda r=req, rec=rec: self._dl_progress(r, rec))
        req.stateChanged.connect(lambda st, rec=rec: self._dl_state(st, rec))
        req.accept()
        self.toast(f"Downloading {target.name}…")

    def _dl_progress(self, r, rec):
        try:
            tot = r.totalBytes()
            if tot > 0:
                rec["pct"] = int(100 * r.receivedBytes() / tot)
        except RuntimeError:
            pass

    def _dl_state(self, st, rec):
        S = QWebEngineDownloadRequest.DownloadState
        if st == S.DownloadCompleted:
            rec["state"], rec["pct"] = "Done", 100
            self.toast(f"Downloaded {rec['name']}")
        elif st == S.DownloadCancelled:
            rec["state"] = "Cancelled"
        elif st == S.DownloadInterrupted:
            rec["state"] = "Failed"
            self.toast(f"Download failed: {rec['name']}")

    def open_download(self, rec):
        if rec["state"] == "Done":
            QDesktopServices.openUrl(QUrl.fromLocalFile(rec["path"]))

    # --- site permissions (camera, microphone, location, ...) ---------------------------------
    def on_permission(self, perm):
        try:
            T = QWebEnginePermission.PermissionType
            if perm.permissionType() in (getattr(T, "Notifications", None), getattr(T, "Unsupported", None)):
                perm.deny()                           # we have no notification UI: don't let sites wait forever
                return
            self._perm_q.append(perm)
            if len(self._perm_q) == 1:
                self._show_perm()
        except Exception:
            try:
                perm.deny()
            except Exception:
                pass

    def _perm_what(self, t):
        T = QWebEnginePermission.PermissionType
        names = {"MediaAudioCapture": "use your microphone", "MediaVideoCapture": "use your camera",
                 "MediaAudioVideoCapture": "use your camera and microphone", "Geolocation": "know your location",
                 "DesktopVideoCapture": "share your screen", "DesktopAudioVideoCapture": "share your screen and sound",
                 "ClipboardReadWrite": "read your clipboard", "MouseLock": "lock your mouse pointer"}
        for n, text in names.items():
            if t == getattr(T, n, object()):
                return text
        return "use a browser feature"

    def _show_perm(self):
        if not self._perm_q:
            self.perm_col.set(False)
            return
        perm = self._perm_q[0]
        try:
            host = perm.origin().host() or "This page"
            self.perm_label.setText(f"{host} wants to {self._perm_what(perm.permissionType())}")
            self.perm_col.set(True)
        except Exception:
            self._perm_q.pop(0)
            self._show_perm()

    def _answer_perm(self, allow):
        if not self._perm_q:
            return
        perm = self._perm_q.pop(0)
        try:
            perm.grant() if allow else perm.deny()
        except Exception:
            pass
        self._show_perm()

    def _perm_allow(self):
        self._answer_perm(True)

    def _perm_deny(self):
        self._answer_perm(False)

    def reset_permissions(self):
        n = 0
        try:
            for pm in self.profile.listAllPermissions():
                pm.reset()
                n += 1
        except Exception:
            pass
        self.toast(f"Reset {n} saved site permission(s)" if n else "No saved site permissions")

    def reopen_tab(self):
        if self.closed_tabs:
            self.add_tab(self.closed_tabs.pop())

    def close_others(self, keep):
        for n in range(self.tabbar.count() - 1, -1, -1):
            v = self.tabbar.tabData(n)
            if v is not keep:
                self.close_tab(n)

    def close_right(self, v):
        i = self.tab_of(v)
        for n in range(self.tabbar.count() - 1, i, -1):
            self.close_tab(n)

    def reload_tab(self, v):
        if isinstance(v, TabStub):
            self.tabbar.setCurrentIndex(self.tab_of(v))     # opening a placeholder tab loads it
        else:
            v.reload()

    def tab_menu(self, i, pos):
        if i < 0:
            return
        v = self.tabbar.tabData(i)
        m = glass_menu(self)
        m.addAction("Reload", lambda: self.reload_tab(v))
        m.addAction("Duplicate", lambda: self.add_tab("start" if getattr(v, "is_start", False) else v.url().toString()))
        m.addSeparator()
        m.addAction("Close", lambda: self.close_tab_animated(self.tab_of(v)))
        m.addAction("Close other tabs", lambda: self.close_others(v))
        m.addAction("Close tabs to the right", lambda: self.close_right(v))
        if self.closed_tabs:
            m.addSeparator()
            m.addAction("Reopen closed tab", self.reopen_tab)
        m.exec(pos)

    # --- per-site ad blocker switch / developer tools -----------------------------------------
    @staticmethod
    def _site_key(host):
        host = (host or "").lower()
        return host[4:] if host.startswith("www.") else host

    def toggle_site_adblock(self):
        v = self.cur()
        h = self._site_key(v.url().host()) if v is not None else ""
        if not h:
            return
        allow = set(self.adblock.allow)
        if h in allow:
            allow.discard(h)
        else:
            allow.add(h)
        self.adblock.allow = allow
        prefs = load_json(PREFS_FILE, {})
        prefs["adblock_allow"] = sorted(allow)
        save_json(PREFS_FILE, prefs)
        self.toast(f"Ad blocker {'off' if h in allow else 'on'} for {h}. Reload the page.")

    def show_devtools(self):
        v = self.cur()
        if v is None:
            return
        try:
            if self._devtools is not None:
                self._devtools.close()
                self._devtools = None
                return
        except RuntimeError:
            self._devtools = None
        try:
            w = DevTools(self, v)
            w.destroyed.connect(lambda *_: setattr(self, "_devtools", None))
            self._devtools = w
            w.show()
        except Exception as ex:
            self.toast("Couldn't open developer tools: " + str(ex)[:60])

    def housekeeping(self):
        self._house_n += 1
        self.save_session()                      # only touches the disk when something changed
        self.history.flush()
        if self._house_n % 3 == 0:
            self.adblock.save()
        if self._house_n % 12 == 0:
            self.sweep()

    def sweep(self):
        """Discard tabs idle in the background for 5+ minutes to free RAM."""
        now = time.time()
        for v, t in list(self.last_active.items()):
            if v is not self.cur() and now - t > 300:
                try:
                    p = v.page()
                    if not p.recentlyAudible() and p.lifecycleState() == Life.Frozen:   # never drop a tab that is playing sound
                        p.setLifecycleState(Life.Discarded)
                except RuntimeError:
                    self.last_active.pop(v, None)

    def on_url(self, view, url):
        view.is_start = url.scheme() == "data"
        if view is self.cur():
            self.urlbar.set_url("" if url.scheme() in ("data", "about", "") else url.toString())
            self.update_lock(url)
            self.update_star()
            self.update_store_bar()

    def on_fullscreen(self, req):
        req.accept()
        self.set_fullscreen(req.toggleOn())

    def set_fullscreen(self, on):
        if on == self._fs:
            return
        self._fs = on
        self._apply_chrome()
        self.tabwrap.setVisible(not on)
        self.barwrap.setVisible(not on)
        self.bmbar.setVisible(not on and self.bm["show"])
        self.showFullScreen() if on else self.showNormal()

    def navigate(self):
        self.sug.hide()
        text = self.urlbar.text()
        url = guess_url(text)
        if not url:
            return
        key = self._typed_key(text, url)
        self._pending_typed = (id(self.cur()), key) if key else None       # remembered once the page has loaded
        self.cur().setUrl(QUrl(url))
        self.cur().setFocus()

    # --- ad blocker ----------------------------------------------------------
    def toggle_adblock(self):
        self.adblock.enabled = not self.adblock.enabled
        scripts = self.profile.scripts()
        if self.adblock.enabled:
            scripts.insert(self.cosmetic)
        else:
            scripts.remove(self.cosmetic)
        self.tick()
        self.toast("Ad blocker " + ("on" if self.adblock.enabled else "off") + " (reload the page)")

    def toggle_passkeys(self):
        prefs = load_json(PREFS_FILE, {})
        prefs["passkeys"] = not self.passkeys_on
        save_json(PREFS_FILE, prefs)
        self.toast("Passkeys " + ("allowed" if not self.passkeys_on else "turned off") + " - restart to apply")

    def shutdown_web(self):
        """Tear the web engine down in the right order so Chromium writes cookies/logins to disk before we exit."""
        try:
            self.cookies.save()
        except Exception:
            pass
        try:
            for n in range(self.tabbar.count()):
                d = self.tabbar.tabData(n)
                if isinstance(d, TabStub):
                    continue
                pg = d.page()
                d.setPage(None)
                if pg is not None:
                    pg.deleteLater()
                d.deleteLater()
            QApplication.sendPostedEvents(None, QEvent.Type.DeferredDelete)
            QApplication.processEvents()
            from PyQt6 import sip
            sip.delete(self.profile)
        except Exception:
            pass

    def check_updates(self, manual=False):
        self._manual_check = manual
        if manual and not self.selfup.url():
            self.set_update_source()
            return
        self.selfup.run()

    def auto_check_updates(self):
        if "--bench-out" in sys.argv or not self.selfup.url():
            return
        prefs = load_json(PREFS_FILE, {})
        if time.time() - prefs.get("last_update_check", 0) < 6 * 3600:
            return
        prefs["last_update_check"] = time.time()
        save_json(PREFS_FILE, prefs)
        self.selfup.run()

    def set_update_source(self):
        cur = self.selfup.url()
        url, ok = QInputDialog.getText(self, "Auto-update source",
                                       "Link to the raw litebrowser4.py file (leave empty to turn updates off):", text=cur)
        if not ok:
            return
        prefs = load_json(PREFS_FILE, {})
        prefs["update_url"] = url.strip()
        prefs["last_update_check"] = 0
        save_json(PREFS_FILE, prefs)
        if url.strip():
            self.toast("Update source saved - checking now")
            self.check_updates(manual=True)
        else:
            self.toast("Auto-update turned off")

    def on_selfupdate(self, status, detail):
        if status == "new":
            self._update_ready = detail
            self.toast(f"Updated to {detail} - restart to use it (menu > Restart now)")
        elif self._manual_check:
            self.toast({"same": f"You're up to date (v{APP_VERSION})",
                        "error": "Update check failed: " + detail,
                        "off": "No update source set"}.get(status, status))

    def restart_now(self):
        frozen = getattr(sys, "frozen", False)
        args = [sys.executable] + ([] if frozen else [str(Path(__file__).resolve())])
        code = ("import time,subprocess,sys;time.sleep(2);"
                "subprocess.Popen(sys.argv[1:],creationflags=0x08000000 if sys.platform=='win32' else 0)")
        try:
            subprocess.Popen([sys.executable, "-c", code] + args if not frozen else
                             ["cmd", "/c", "ping -n 3 127.0.0.1 >nul & start \"\" \"%s\"" % sys.executable],
                             creationflags=0x08000000 if sys.platform == "win32" else 0)
        except Exception as e:
            self.toast("Could not restart: " + str(e)[:50])
            return
        self.close()
        QApplication.quit()

    def on_list_updated(self, n, err):
        if err:
            self.toast("Blocklist update failed: " + err[:60])
        else:
            self.adblock.load_file()
            self.toast(f"Blocklist updated: {len(self.adblock.domains):,} domains")

    # --- extensions ----------------------------------------------------------
    def on_ext_loaded(self, info):
        try:
            if info.error():
                self.toast(f"Extension error: {info.error()[:70]}")
        except Exception:
            pass
        QTimer.singleShot(0, self.after_ext_change)

    def add_extension(self):
        d = QFileDialog.getExistingDirectory(self, "Select an unpacked Manifest V3 extension folder")
        if not d:
            return
        src = Path(d)
        if not (src / "manifest.json").exists():
            self.toast("No manifest.json in that folder")
            return
        dst = EXT_DIR / src.name
        shutil.copytree(src, dst, dirs_exist_ok=True)
        self.ext_mgr.loadExtension(str(dst))
        self.toast(f"Loading extension: {src.name}")

    def build_menu(self):
        m = glass_menu(self)
        cv = self.cur()
        is_bm = cv is not None and not getattr(cv, "is_start", False) and self.bm_index(cv.url().toString()) >= 0
        m.addAction("Remove bookmark" if is_bm else "Bookmark this page", self.toggle_bookmark)
        bar = QAction("Show bookmarks bar", m, checkable=True, checked=self.bm["show"])
        bar.triggered.connect(self.toggle_bm_bar)
        m.addAction(bar)
        rt = QAction("Continue where you left off", m, checkable=True,
                     checked=load_json(PREFS_FILE, {}).get("restore_tabs", True))
        rt.triggered.connect(self.toggle_restore)
        m.addAction(rt)
        m.addAction("History", self.show_history)
        m.addAction(f"Saved sign-ins: {self.cookies.count():,} cookies kept").setEnabled(False)
        dm = GlassMenu("Downloads", m)
        m.addMenu(dm)
        if not self.downloads:
            dm.addAction("No downloads yet").setEnabled(False)
        for rec in reversed(self.downloads[-10:]):
            st = f"{rec['pct']}%" if rec["state"] == "Downloading…" else rec["state"]
            act = dm.addAction(f"{rec['name'][:42]}   ({st})")
            act.triggered.connect(lambda _=False, r=rec: self.open_download(r))
        dm.addSeparator()
        dm.addAction("Open downloads folder", lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(str(self.download_dir()))))
        sub = GlassMenu("Bookmarks", m)
        m.addMenu(sub)
        if not self.bm["items"]:
            sub.addAction("No bookmarks yet").setEnabled(False)
        self.fill_menu(sub, self.bm["items"])
        m.addSeparator()
        a = QAction(f"Ad blocker  ({self.adblock.s_count:,} blocked this session)", m,
                    checkable=True, checked=self.adblock.enabled)
        a.triggered.connect(self.toggle_adblock)
        m.addAction(a)
        m.addAction("Update blocklist", self.updater.run)
        a = QAction("Allow passkeys / security keys (only after you click)", m, checkable=True, checked=self.passkeys_on)
        a.triggered.connect(self.toggle_passkeys)
        m.addAction(a)
        if getattr(self, "_update_ready", None):
            m.addAction(f"Restart now  (v{self._update_ready} is ready)", self.restart_now)
        m.addAction(f"Check for browser updates  (v{APP_VERSION})", lambda: self.check_updates(True))
        m.addAction("Auto-update source...", self.set_update_source)
        m.addAction("Reset blocking stats", self.reset_stats)
        cv0 = self.cur()
        h0 = self._site_key(cv0.url().host()) if cv0 is not None else ""
        if h0:
            m.addAction(f"Ad blocker: turn {'back on' if h0 in self.adblock.allow else 'off'} for {h0}", self.toggle_site_adblock)
        m.addSeparator()

        m.addAction("Extensions", self.show_extensions)
        m.addAction("Manage extensions", self.show_settings)
        m.addAction("Google accounts & sync…", self.show_google)

        m.addSeparator()
        if sys.platform == "win32":
            m.addAction("Pin to taskbar…", self.pin_to_taskbar)
        if is_default_browser():
            m.addAction("✓ LiteBrowser is your default browser").setEnabled(False)
        else:
            m.addAction("Make default browser", self.make_default)
        m.addAction("Developer tools (F12)", self.show_devtools)
        m.addAction("Reset site permissions", self.reset_permissions)
        m.addAction("Clear cache and cookies", self.clear_data)
        return m

    # --- extensions UI -------------------------------------------------------
    def ext_list(self):
        if self.ext_mgr is None:
            return []
        try:
            exts = list(self.ext_mgr.extensions())
        except Exception:
            return []
        base = os.path.normcase(os.path.abspath(str(EXT_DIR)))
        out = []
        for e in exts:
            try:
                name = (e.name() or "").lower()
                if "hangouts" in name or "pdf viewer" in name:
                    continue
                path = e.path()
                if path and not os.path.normcase(os.path.abspath(path)).startswith(base):
                    continue
            except Exception:
                pass
            out.append(e)
        return sorted(out, key=lambda e: (e.name() or "").lower())

    def find_ext(self, eid):
        for e in self.ext_list():
            if e.id() == eid:
                return e
        return None

    def ext_manifest(self, info):
        try:
            return json.loads((Path(info.path()) / "manifest.json").read_text(encoding="utf-8"))
        except Exception:
            return {}

    def ext_icon(self, info):
        key = info.id()
        if key in self._ext_icons:
            return self._ext_icons[key]
        icon = None
        try:
            base = Path(info.path())
            m = self.ext_manifest(info)
            cands = []
            act = m.get("action") or m.get("browser_action") or {}
            di = act.get("default_icon")
            if isinstance(di, str):
                cands.append((1000, di))
            elif isinstance(di, dict):
                cands += [(int(k) if str(k).isdigit() else 0, v) for k, v in di.items()]
            cands += [(int(k) if str(k).isdigit() else 0, v) for k, v in (m.get("icons") or {}).items()]
            for _, rel in sorted(cands, key=lambda t: -t[0]):
                f = base / rel
                if f.suffix.lower() in (".png", ".jpg", ".jpeg", ".webp", ".gif", ".ico") and f.exists():
                    ic = QIcon(str(f))
                    if not ic.isNull():
                        icon = ic
                        break
        except Exception:
            pass
        if icon is None:
            icon = letter_icon(info.name() or "?")
        self._ext_icons[key] = icon
        return icon

    def save_ext_ui(self):
        try:
            DATA.mkdir(parents=True, exist_ok=True)
            EXT_UI_FILE.write_text(json.dumps(self.ext_ui), encoding="utf-8")
        except OSError:
            pass

    def toggle_pin(self, eid):
        pins = self.ext_ui["pinned"]
        if eid in pins:
            pins.remove(eid)
        else:
            pins.append(eid)
        self.save_ext_ui()
        self.refresh_ext_pins()

    def refresh_ext_pins(self):
        lay = self.pin_lay
        while lay.count():
            w = lay.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        pinned = set(self.ext_ui["pinned"])
        for info in self.ext_list():
            eid = info.id()
            if eid not in pinned:
                continue
            btn = HoverButton(objectName="nav")
            btn.setIcon(self.ext_icon(info))
            btn.setIconSize(QSize(20, 20))
            btn.setFixedSize(32, 32)
            btn.setToolTip(info.name() or eid)
            btn.setEnabled(info.isEnabled())
            btn.setCursor(Qt.CursorShape.PointingHandCursor)
            btn.clicked.connect(lambda _=False, e=eid, bt=btn: self.open_ext_popup(e, bt))
            btn.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
            btn.customContextMenuRequested.connect(
                lambda pos, e=eid, bt=btn: self.ext_menu(e, bt.mapToGlobal(pos)))
            lay.addWidget(btn)

    def after_ext_change(self, settings=True):
        self.refresh_ext_pins()
        for attr in ("_panel", "_settings"):
            w = getattr(self, attr)
            if w is not None and (settings or attr == "_panel"):
                try:
                    w.build()
                except RuntimeError:
                    setattr(self, attr, None)

    def show_settings(self):
        try:
            if self._settings is not None:
                self._settings.raise_()
                self._settings.activateWindow()
                return
        except RuntimeError:
            self._settings = None
        w = SettingsWindow(self)
        w.destroyed.connect(lambda *_, x=w: self._settings_gone(x))
        g = self.geometry()
        w.move(g.center().x() - w.width() // 2, g.center().y() - w.height() // 2)
        self._settings = w
        w.show()

    def _settings_gone(self, w):
        if self._settings is w:
            self._settings = None

    # --- Chrome Web Store install bar ------------------------------------------
    def update_store_bar(self):
        v = self.cur()
        eid = store_ext_id(v.url()) if v is not None else None
        if eid and not (EXT_DIR / eid).exists() and eid not in self._store_dismissed:
            title = (v.title() or "").replace(" - Chrome Web Store", "").strip() or "this extension"
            self.store_label.setText(f"Add “{title[:46]}” to LiteBrowser?")
            self._store_id = eid
            self.store_col.set(True)
        else:
            self._store_id = None
            self.store_col.set(False)

    def dismiss_store(self):
        if self._store_id:
            self._store_dismissed.add(self._store_id)
        self.store_col.set(False)

    def install_current(self):
        if self.ext_mgr is None:
            self.toast("Extensions need Qt 6.10+  (pip install -U PyQt6 PyQt6-WebEngine)")
            return
        if not self._store_id:
            return
        self.store_btn.setEnabled(False)
        self.store_btn.setText("Installing…")
        self.installer.run(self._store_id)

    def on_installed(self, eid, folder, err):
        batch = eid in self._batch_ids
        if not batch:
            self.store_btn.setEnabled(True)
            self.store_btn.setText("Add to LiteBrowser")
        ok = False
        msg = ""
        if err and err != "Already installed":
            msg = "Install failed: " + err[:90]
        elif folder:
            try:
                self.ext_mgr.loadExtension(folder)
                ok = True
            except Exception as ex:
                msg = "Couldn't load extension: " + str(ex)[:70]
        elif err:
            msg = err
        if batch:
            self._batch_ids.discard(eid)
            if ok:
                self._batch_ok += 1
            elif msg != "Already installed":
                self._batch_fail += 1
            self._install_next()
            return
        if msg:
            self.toast(msg)
            return
        self.toast("Extension installed. Pin it from the puzzle menu.")
        self.update_store_bar()

    def install_many(self, items):
        have = set(self._queue) | self._batch_ids
        for e in items:
            if e["id"] not in have:
                self._queue.append(e["id"])
                have.add(e["id"])
        if not self._installing and self._queue:
            self._installing = True
            self._install_next()

    def _install_next(self):
        if self._queue:
            eid = self._queue.pop(0)
            self._batch_ids.add(eid)
            self.installer.run(eid)
            return
        if self._batch_ok or self._batch_fail:
            self.toast(f"Installed {self._batch_ok} extension(s)" +
                       (f", {self._batch_fail} failed" if self._batch_fail else ""))
        self._batch_ok = self._batch_fail = 0
        self._installing = False

    # --- Google accounts / sync ----------------------------------------------------
    def show_google(self):
        try:
            if self._gwin is not None:
                self._gwin.close()
                return
        except RuntimeError:
            self._gwin = None
        w = GoogleWindow(self)
        w.destroyed.connect(lambda *_, x=w: self._gwin_gone(x))
        g = self.geometry()
        w.move(g.center().x() - w.width() // 2, g.center().y() - w.height() // 2)
        self._gwin = w
        w.show()

    def _gwin_gone(self, w):
        if self._gwin is w:
            self._gwin = None

    def set_sync(self, prof, key, on):
        cfg = self.gsync["accounts"].setdefault(prof["dir"], {"bookmarks": False, "extensions": False})
        cfg[key] = on
        save_json(GSYNC_FILE, self.gsync)
        if on:
            self.sync_profiles([prof], kinds=(key,), rebuild=False)

    def apply_account_folder(self, folder, prof):
        for i, b in enumerate(self.bm["items"]):
            if b.get("src") == prof["dir"]:
                if b != folder:
                    self.bm["items"][i] = folder
                    self.save_bm()
                break
        else:
            self.bm["items"].append(folder)
            self.save_bm()
        return sum(1 for _ in bm_walk(folder["children"]))

    def sync_bookmarks_from(self, prof):
        folder = build_account_folder(prof)
        return None if folder is None else self.apply_account_folder(folder, prof)

    def sync_profiles(self, profs, kinds=("bookmarks", "extensions"), quiet=False, rebuild=True):
        nb = accounts = skipped = 0
        todo = []
        for pr in profs:
            if "bookmarks" in kinds:
                n = self.sync_bookmarks_from(pr)
                if n is not None:
                    nb += n
                    accounts += 1
            if "extensions" in kinds and self.ext_mgr is not None:
                found = chrome_extensions(pr["path"])
                todo += [e for e in found if e["mv"] == 3 and not (EXT_DIR / e["id"]).exists()]
                skipped += sum(1 for e in found if e["mv"] != 3)
        if "bookmarks" in kinds:
            self.refresh_bookmarks()
            self.update_star()
        if todo:
            self.install_many(todo)
        self.gsync["last"] = time.time()
        save_json(GSYNC_FILE, self.gsync)
        if not quiet:
            parts = []
            if "bookmarks" in kinds:
                parts.append(f"{nb} bookmarks from {accounts} account(s)")
            if "extensions" in kinds:
                if self.ext_mgr is None:
                    parts.append("extensions need Qt 6.10+")
                else:
                    parts.append(f"{len({e['id'] for e in todo})} extension(s) to install" +
                                 (f", {skipped} skipped (Manifest V2)" if skipped else ""))
            self.toast("Synced: " + "  ·  ".join(parts))
        if rebuild and self._gwin is not None:
            try:
                self._gwin.build()
            except RuntimeError:
                self._gwin = None

    def auto_sync(self):
        cfgs = {d: c for d, c in self.gsync["accounts"].items() if c.get("bookmarks") or c.get("extensions")}
        if not cfgs:
            return                           # nothing is switched on: do no work
        threading.Thread(target=self._auto_sync_worker, args=(cfgs,), daemon=True).start()

    def _auto_sync_worker(self, cfgs):       # reads Chrome's files off the UI thread
        results = []
        try:
            for pr in chrome_profiles():
                c = cfgs.get(pr["dir"])
                if not c:
                    continue
                item = {"prof": pr, "folder": None, "todo": []}
                if c.get("bookmarks"):
                    item["folder"] = build_account_folder(pr)
                if c.get("extensions"):
                    item["todo"] = [e for e in chrome_extensions(pr["path"])
                                    if e["mv"] == 3 and not (EXT_DIR / e["id"]).exists()]
                results.append(item)
        except Exception:
            pass
        self.sync_ready.emit(results)

    def _apply_auto_sync(self, results):
        before = json.dumps(self.bm["items"])
        for r in results:
            if r["folder"] is not None:
                self.apply_account_folder(r["folder"], r["prof"])
            if r["todo"] and self.ext_mgr is not None:
                self.install_many(r["todo"])
        if json.dumps(self.bm["items"]) != before:
            self.refresh_bookmarks()
            self.update_star()
        self.gsync["last"] = time.time()
        save_json(GSYNC_FILE, self.gsync)

    # --- default browser -------------------------------------------------------------
    def _make_infobar(self, icon_kind, btn_text, on_btn, on_close):
        wrap = QWidget(objectName="storewrap")
        sw = QHBoxLayout(wrap)
        sw.setContentsMargins(16, 0, 16, 8)
        pill = QFrame(objectName="storepill")
        pl = QHBoxLayout(pill)
        pl.setContentsMargins(14, 6, 8, 6)
        pl.setSpacing(10)
        ic = QLabel()
        ic.setPixmap(QIcon(pm_icon(icon_kind, "#ff9aa5", width=3.2)).pixmap(QSize(20, 20)))
        pl.addWidget(ic)
        label = QLabel("", objectName="extname")
        pl.addWidget(label, 1)
        btn = HoverButton(objectName="chip")
        btn.setText(btn_text)
        btn.setFixedHeight(28)
        btn.setCursor(Qt.CursorShape.PointingHandCursor)
        btn.clicked.connect(lambda _=False: on_btn())
        pl.addWidget(btn)
        x = HoverButton(objectName="flat")
        x.setIcon(QIcon(pm_icon("close", width=4)))
        x.setIconSize(QSize(14, 14))
        x.setFixedSize(28, 28)
        x.clicked.connect(lambda _=False: on_close())
        pl.addWidget(x)
        sw.addWidget(pill)
        return wrap, label, btn

    def _make_shortcuts(self, reveal):
        self.shortcuts_done.emit(create_shortcuts(APP_ICON_PATH, desktop=reveal), reveal)

    def ensure_shortcut(self):
        """Quietly keep a Start Menu shortcut (no console window) pointing at this copy of the script."""
        if sys.platform != "win32":
            return
        prefs = load_json(PREFS_FILE, {})
        script = launch_command()[1] or launch_command()[0]
        if prefs.get("shortcut_for") == script:
            return
        prefs["shortcut_for"] = script
        save_json(PREFS_FILE, prefs)
        threading.Thread(target=self._make_shortcuts, args=(False,), daemon=True).start()

    def pin_to_taskbar(self):
        if sys.platform != "win32":
            self.toast("Taskbar pinning is only available on Windows.")
            return
        self.toast("Creating shortcut…")
        threading.Thread(target=self._make_shortcuts, args=(True,), daemon=True).start()

    def on_shortcuts(self, paths, reveal):
        if not reveal:
            return
        if not paths:
            self.toast("Couldn't create the shortcut.")
            return
        self.toast("Shortcut created. Right-click it → Show more options → Pin to taskbar. "
                   "(You can also search “LiteBrowser” in Start and right-click it there.)")
        try:
            subprocess.Popen(f'explorer /select,"{paths[-1]}"')
        except Exception:
            pass

    def maybe_ask_default(self):
        prefs = load_json(PREFS_FILE, {})
        if prefs.get("asked_default"):
            return
        if not (sys.platform == "win32" or sys.platform.startswith("linux")):
            return
        if is_default_browser():
            return
        self.def_col.set(True)
        prefs["asked_default"] = True
        save_json(PREFS_FILE, prefs)

    def dismiss_default(self):
        self.def_col.set(False)

    def make_default(self):
        self.toast(set_default_browser(APP_ICON_PATH))

    def make_default_from_bar(self):
        self.make_default()
        self.dismiss_default()

    def open_external(self, arg):
        """Called when another process (e.g. a link clicked elsewhere) hands us a URL."""
        if self.isMinimized():
            self.showNormal()
        self.raise_()
        self.activateWindow()
        if arg:
            self.add_tab(normalize_arg(arg))

    def show_extensions(self):
        try:
            if self._panel is not None:
                self._panel.close()
        except RuntimeError:
            pass
        panel = ExtPanel(self)
        panel.destroyed.connect(lambda *_, p=panel: self._panel_gone(p))
        self._panel = panel
        g = self.ext_btn.mapToGlobal(self.ext_btn.rect().bottomRight())
        panel.move(max(0, g.x() - panel.width()), g.y() + 8)
        panel.show()

    def _panel_gone(self, p):
        if self._panel is p:
            self._panel = None

    def open_ext_popup(self, eid, btn):
        info = self.find_ext(eid)
        if info is None:
            return
        try:
            url = info.actionPopupUrl()
        except Exception:
            url = QUrl()
        if not url.isValid() or url.isEmpty():
            self.toast(f"{info.name() or 'This extension'} has no popup")
            return
        pop = ExtPopup(self, url)
        g = btn.mapToGlobal(btn.rect().bottomRight())
        pop.move(max(0, g.x() - pop.width()), g.y() + 8)
        pop.show()

    def ext_menu(self, eid, pos):
        info = self.find_ext(eid)
        if info is None:
            return
        m = glass_menu(self)
        pinned = eid in self.ext_ui["pinned"]
        m.addAction("Unpin from toolbar" if pinned else "Pin to toolbar",
                    lambda: (self.toggle_pin(eid), self.after_ext_change()))
        enabled = info.isEnabled()
        m.addAction("Disable" if enabled else "Enable", lambda: self.set_ext_enabled(eid, not enabled))
        man = self.ext_manifest(info)
        page = (man.get("options_ui") or {}).get("page") or man.get("options_page")
        if page:
            m.addAction("Options", lambda: self.add_tab(f"chrome-extension://{eid}/{page}"))
        m.addSeparator()
        m.addAction("Remove extension", lambda: self.remove_ext(eid))
        m.exec(pos)

    def set_ext_enabled(self, eid, on, rebuild_settings=True):
        info = self.find_ext(eid)
        if info is not None:
            self.ext_mgr.setExtensionEnabled(info, on)
            QTimer.singleShot(200, lambda: self.after_ext_change(settings=rebuild_settings))

    def remove_ext(self, eid):
        info = self.find_ext(eid)
        if info is None:
            return
        name, path = info.name(), info.path()
        try:
            self.ext_mgr.unloadExtension(info)
        except Exception:
            pass
        base = os.path.normcase(os.path.abspath(str(EXT_DIR))) + os.sep
        try:
            if path and os.path.normcase(os.path.abspath(path)).startswith(base):
                shutil.rmtree(path, ignore_errors=True)
        except Exception:
            pass
        if eid in self.ext_ui["pinned"]:
            self.ext_ui["pinned"].remove(eid)
            self.save_ext_ui()
        self._ext_icons.pop(eid, None)
        self.toast(f"Removed {name}")
        QTimer.singleShot(400, self.after_ext_change)

    # --- bookmarks -----------------------------------------------------------
    def resizeEvent(self, e):
        super().resizeEvent(e)
        if hasattr(self, "bm_timer"):
            self.bm_timer.start()

    @staticmethod
    def norm(url):
        return url.rstrip("/")

    def bm_find(self, url):
        u = self.norm(url)

        def rec(lst):
            for i, b in enumerate(lst):
                if is_folder(b):
                    r = rec(b["children"])
                    if r:
                        return r
                elif self.norm(b["url"]) == u:
                    return lst, i
            return None
        return rec(self.bm["items"])

    def bm_index(self, url):
        if self._bm_urls is None:
            self._bm_urls = {self.norm(b["url"]) for b in bm_walk(self.bm["items"])}
        return 0 if self.norm(url) in self._bm_urls else -1

    def save_bm(self):
        self._bm_urls = None
        try:
            DATA.mkdir(parents=True, exist_ok=True)
            BM_FILE.write_text(json.dumps(self.bm, indent=1), encoding="utf-8")
        except OSError:
            pass

    def fav_path(self, url):
        host = QUrl(url).host().lower()
        return FAV_DIR / (hashlib.md5(host.encode()).hexdigest() + ".png")

    def fav_icon(self, url):
        host = QUrl(url).host().lower()
        ic = self._fav_cache.get(host, 0)
        if isinstance(ic, int):              # not looked up yet
            p = self.fav_path(url)
            ic = QIcon(str(p)) if p.exists() else None
            self._fav_cache[host] = ic
        return ic if ic is not None else self.ic_globe

    def save_fav(self, url, icon, force=False):
        if icon.isNull():
            return False
        path = self.fav_path(url)
        if path.exists() and not force:
            return False
        try:
            FAV_DIR.mkdir(parents=True, exist_ok=True)
            ok = icon.pixmap(QSize(32, 32)).save(str(path), "PNG")
            if ok:
                self._fav_cache.pop(QUrl(url).host().lower(), None)
                self._fav_ver += 1
            return ok
        except Exception:
            return False

    def on_icon(self, v, ic):
        i = self.tab_of(v)
        if i >= 0:
            self.tabbar.setTabIcon(i, ic if not ic.isNull() else self.ic_globe)
        v.tint = tint_from_icon(ic) if not ic.isNull() else None
        self.tabbar.update()
        host = v.url().host()
        if host and not ic.isNull():
            fresh = self.save_fav(v.url().toString(), ic)      # keep a small favicon for every site we visit
            if fresh and any(QUrl(b["url"]).host() == host for b in bm_walk(self.bm["items"])):
                self.bm_timer.start()

    def update_lock(self, url):
        s = url.scheme()
        if s == "https":
            self.lock_act.setIcon(self.ic_lock)
            self.lock_act.setToolTip("Connection is secure")
        elif s == "http":
            self.lock_act.setIcon(self.ic_unlock)
            self.lock_act.setToolTip("Connection is not secure")
        else:
            self.lock_act.setIcon(self.ic_search)
            self.lock_act.setToolTip("")

    def update_star(self):
        v = self.cur()
        if v is None or getattr(v, "is_start", False) or not v.url().toString():
            self.star_act.setVisible(False)
            return
        self.star_act.setVisible(True)
        self.star_act.setIcon(self.ic_star_on if self.bm_index(v.url().toString()) >= 0 else self.ic_star)

    def toggle_bookmark(self):
        v = self.cur()
        if v is None or getattr(v, "is_start", False) or not v.url().toString():
            self.toast("Open a page first to bookmark it")
            return
        url = v.url().toString()
        found = self.bm_find(url)
        i = 0 if found else -1
        if found:
            del found[0][found[1]]
            self.toast("Bookmark removed")
        else:
            title = v.title() or v.url().host() or url
            self.bm["items"].append({"title": title, "url": url})
            self.save_fav(url, v.icon(), force=True)
            self.toast("Bookmarked: " + title[:40])
        self.save_bm()
        self.update_star()
        self.refresh_bookmarks(animate_last=(i < 0))

    def toggle_bm_bar(self):
        self.bm["show"] = not self.bm["show"]
        self.save_bm()
        self.refresh_bookmarks()

    def make_chip(self, b, text):
        c = Chip()
        c.setObjectName("chip")
        c.setText(text.replace("&", "&&"))
        c.setIconSize(QSize(16, 16))
        c.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        c.setFixedHeight(28)
        c.setCursor(Qt.CursorShape.PointingHandCursor)
        if is_folder(b):
            c.setIcon(self.ic_folder)
            c.setToolTip(b["title"])
            c.clicked.connect(lambda _=False, b=b, c=c: self.folder_menu(b, c))
        else:
            c.setToolTip(b["title"] + "\n" + b["url"])
            c.setIcon(self.fav_icon(b["url"]))
            c.clicked.connect(lambda _=False, u=b["url"]: self.cur().setUrl(QUrl(u)))
            c.middle.connect(lambda u=b["url"]: self.add_tab(u))
        c.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        c.customContextMenuRequested.connect(lambda pos, b=b, c=c: self.chip_menu(b, c.mapToGlobal(pos)))
        return c

    def fill_menu(self, menu, items):
        for b in items[:80]:
            if is_folder(b):
                sub = GlassMenu(b["title"][:40], menu)
                sub.setIcon(self.ic_folder)
                menu.addMenu(sub)
                if b["children"]:
                    self.fill_menu(sub, b["children"])
                else:
                    sub.addAction("Empty").setEnabled(False)
            else:
                act = menu.addAction(self.fav_icon(b["url"]), b["title"][:50])
                act.triggered.connect(lambda _=False, u=b["url"]: self.cur().setUrl(QUrl(u)))

    def folder_menu(self, b, chip):
        m = glass_menu(self)
        if b["children"]:
            self.fill_menu(m, b["children"])
        else:
            m.addAction("Empty").setEnabled(False)
        m.exec(chip.mapToGlobal(chip.rect().bottomLeft()))

    def refresh_bookmarks(self, stagger=False, animate_last=False):
        self.bm_col.set(self.bm["show"])
        items = self.bm["items"]
        f = QFont(self.font())
        f.setPixelSize(12)
        fm = QFontMetrics(f)
        avail = self.width() - 32 - 46
        used, vis, over = 0, [], []
        for b in items:
            if over:
                over.append(b)
                continue
            text = fm.elidedText(b["title"], Qt.TextElideMode.ElideRight, 150)
            w = fm.horizontalAdvance(text) + 48
            if used + w > avail:
                over.append(b)
                continue
            used += w + 6
            vis.append((b, text))
        sig = (tuple(id(b) for b in items), tuple(t for _, t in vis), len(over), self._fav_ver)
        if sig == self._bm_sig and not (stagger or animate_last):
            return                           # same chips as before: skip the rebuild
        self._bm_sig = sig
        lay = self.bm_layout
        while lay.count():
            w = lay.takeAt(0).widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()
        if not items:
            lay.addWidget(QLabel("Bookmarks appear here. Press Ctrl+D to bookmark a page.", objectName="hint"))
            lay.addStretch(1)
            return
        made = []
        for b, text in vis:
            chip = self.make_chip(b, text)
            made.append(chip)
            lay.addWidget(chip)
        if over:
            btn = Chip()
            btn.setObjectName("chip")
            btn.setText("»")
            btn.setFixedHeight(28)
            btn.setCursor(Qt.CursorShape.PointingHandCursor)
            btn.clicked.connect(lambda _=False, o=over, bt=btn: self.show_overflow(o, bt))
            lay.addWidget(btn)
        lay.addStretch(1)
        if stagger:
            for i, c in enumerate(made):
                fade_widget(c, delay=120 + i * 45)
        elif animate_last and made:
            fade_widget(made[-1])

    def show_overflow(self, items, btn):
        m = glass_menu(self)
        self.fill_menu(m, items)
        m.exec(btn.mapToGlobal(btn.rect().bottomLeft()))

    def chip_menu(self, b, pos):
        m = glass_menu(self)
        if is_folder(b):
            m.addAction("Open all in new tabs", lambda: [self.add_tab(x["url"]) for x in bm_walk(b["children"])])
            m.addSeparator()
            if not b.get("src"):
                m.addAction("Rename…", lambda: self.rename_bm(b))
            m.addAction("Remove folder", lambda: self.remove_bm(b))
        else:
            m.addAction("Open", lambda: self.cur().setUrl(QUrl(b["url"])))
            m.addAction("Open in new tab", lambda: self.add_tab(b["url"]))
            m.addSeparator()
            m.addAction("Rename…", lambda: self.rename_bm(b))
            m.addAction("Remove", lambda: self.remove_bm(b))
        m.exec(pos)

    def rename_bm(self, b):
        t, ok = QInputDialog.getText(self, "Rename bookmark", "Name:", text=b["title"])
        if ok and t.strip():
            b["title"] = t.strip()
            self.save_bm()
            self.refresh_bookmarks()

    def remove_bm(self, b):
        def rec(lst):
            for i, x in enumerate(lst):
                if x is b:
                    del lst[i]
                    return True
                if is_folder(x) and rec(x["children"]):
                    return True
            return False
        rec(self.bm["items"])
        self.save_bm()
        self.update_star()
        self.refresh_bookmarks()

    def show_menu(self, anchor):
        m = self.build_menu()
        g = anchor.mapToGlobal(anchor.rect().bottomRight())
        m.exec(QPoint(g.x() - m.sizeHint().width(), g.y() + 8))

    def reset_stats(self):
        self.adblock.reset()
        self.tick()
        self.toast("Blocking stats reset")

    def clear_data(self):
        self.profile.clearHttpCache()
        self.profile.cookieStore().deleteAllCookies()
        self.cookies.clear()
        self.toast("Cache and cookies cleared")


class Splash(QWidget):
    """Shown while the browser engine starts, so the app appears to open at once."""

    def __init__(self, icon):
        super().__init__(None, Qt.WindowType.SplashScreen | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowStaysOnTopHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setFixedSize(420, 250)
        self._pm = icon.pixmap(QSize(88, 88))
        geo = QApplication.primaryScreen().availableGeometry()
        self.move(geo.center().x() - self.width() // 2, geo.center().y() - self.height() // 2)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        g = QLinearGradient(0, 0, self.width(), self.height())
        g.setColorAt(0, QColor("#3d0a15"))
        g.setColorAt(1, QColor("#12030a"))
        p.setBrush(QBrush(g))
        p.setPen(QPen(QColor(255, 255, 255, 70), 1))
        p.drawRoundedRect(QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5), 22, 22)
        p.drawPixmap((self.width() - 88) // 2, 50, self._pm)
        f = QFont()
        f.setPixelSize(26)
        f.setBold(True)
        p.setFont(f)
        p.setPen(QColor("#f6e3e6"))
        p.drawText(QRectF(0, 156, self.width(), 40), Qt.AlignmentFlag.AlignCenter, "LiteBrowser")
        p.end()


def start_bench(win, app, out_path):
    """Automated benchmark (driven by benchmark.py): startup time, memory, idle CPU and tab-switch latency."""
    import statistics
    try:
        import psutil
    except Exception:
        psutil = None
    me = psutil.Process() if psutil else None
    created = me.create_time() if me else None
    res = {"label": os.environ.get("LB_LABEL", ""), "tabs": win.tabbar.count(), "psutil": bool(psutil)}

    def ms_since_start():
        return (time.time() - created) * 1000 if created else (time.perf_counter() - _T0) * 1000

    def tree():
        """(memory in MB, process count, cpu seconds) of this process and all its Chromium children."""
        if me is None:
            return 0.0, 1, time.process_time()
        procs = [me]
        try:
            procs += me.children(recursive=True)
        except Exception:
            pass
        rss = cpu = 0.0
        for pr in procs:
            try:
                rss += pr.memory_info().rss
                t = pr.cpu_times()
                cpu += t.user + t.system
            except Exception:
                pass
        return rss / 1048576.0, len(procs), cpu

    def breakdown():
        """RAM per kind of process: our Python process, and each kind of Chromium helper (renderer, gpu, ...)."""
        out = {}
        if me is None:
            return out
        procs = [me]
        try:
            procs += me.children(recursive=True)
        except Exception:
            pass
        for pr in procs:
            try:
                kind = "browser (python)" if pr.pid == me.pid else "chromium-other"
                for a in pr.cmdline():
                    if a.startswith("--type="):
                        kind = "chromium-" + a.split("=", 1)[1]
                        break
                d = out.setdefault(kind, {"mb": 0.0, "n": 0})
                d["mb"] += pr.memory_info().rss / 1048576.0
                d["n"] += 1
            except Exception:
                pass
        return {k: {"mb": round(v["mb"], 1), "n": v["n"]} for k, v in out.items()}

    def stats(x):
        if not x:
            return None
        x = sorted(x)
        return {"median": round(statistics.median(x), 2), "p95": round(x[int(0.95 * (len(x) - 1))], 2),
                "max": round(x[-1], 2), "n": len(x)}

    res["startup_window_ms"] = round(ms_since_start(), 1)
    res["phases_ms"] = {k: round(v, 1) for k, v in _MARKS.items()}      # time since our script started
    _prev, _d = 0.0, {}
    for _k, _v in sorted(_MARKS.items(), key=lambda kv: kv[1]):         # time spent in each step
        _d[_k] = round(_v - _prev, 1)
        _prev = _v
    res["phase_deltas_ms"] = _d
    if created:
        res["interp_start_ms"] = round((time.time() - (time.perf_counter() - _T0) - created) * 1000, 1)   # before our script ran
    ready = {"t": None}
    orig_loaded = Browser.on_loaded

    def on_loaded(self, v, ok):
        v._bench_loaded = True
        if ready["t"] is None and v is self.cur():
            ready["t"] = ms_since_start()
        orig_loaded(self, v, ok)
    Browser.on_loaded = on_loaded

    def finish(err=None):
        if err:
            res["error"] = err
        res["gui_cpu_s"] = round(time.process_time(), 2)
        try:
            Path(out_path).write_text(json.dumps(res, indent=1), encoding="utf-8")
        except Exception:
            pass
        app.quit()

    def guard(fn):
        def run(*a):
            try:
                fn(*a)
            except Exception:
                import traceback
                finish(traceback.format_exc())
        return run

    def wait_ready():
        if ready["t"] is None:
            if ms_since_start() > 90000:
                return finish("first page never finished loading")
            return QTimer.singleShot(50, guard(wait_ready))
        res["startup_ready_ms"] = round(ready["t"], 1)
        QTimer.singleShot(3000, guard(after_startup))

    def after_startup():
        mb, n, _ = tree()
        res["mem_startup_mb"], res["procs_startup"] = round(mb, 1), n
        res["breakdown_startup"] = breakdown()
        nt = win.tabbar.count()
        cur = win.tabbar.currentIndex()
        for k in ("first_call", "first_idle", "first_ready", "revisit_call", "revisit_idle"):
            res[k + "_ms"] = []
        if nt < 2:
            return switching_done()
        steps, idx = [], cur
        for _ in range((nt - 1) + 3 * nt):          # one pass over every other tab, then three revisit rounds
            idx = (idx + 1) % nt
            steps.append(idx)
        run_step(0, steps, {cur})

    def run_step(k, steps, visited):
        if k >= len(steps):
            return switching_done()
        i = steps[k]
        first = i not in visited
        visited.add(i)
        t0 = time.perf_counter()
        win.tabbar.setCurrentIndex(i)                 # same code path as clicking the tab
        call_ms = (time.perf_counter() - t0) * 1000

        def idle():
            idle_ms = (time.perf_counter() - t0) * 1000   # until the event loop is idle again
            if first:
                res["first_call_ms"].append(round(call_ms, 2))
                res["first_idle_ms"].append(round(idle_ms, 2))
                wait_loaded(t0, k, steps, visited)
            else:
                res["revisit_call_ms"].append(round(call_ms, 2))
                res["revisit_idle_ms"].append(round(idle_ms, 2))
                QTimer.singleShot(250, guard(lambda: run_step(k + 1, steps, visited)))
        QTimer.singleShot(0, guard(idle))

    def wait_loaded(t0, k, steps, visited):
        v = win.cur()
        if getattr(v, "_bench_loaded", False) or (time.perf_counter() - t0) > 8:
            res["first_ready_ms"].append(round((time.perf_counter() - t0) * 1000, 1))
            QTimer.singleShot(300, guard(lambda: run_step(k + 1, steps, visited)))
        else:
            QTimer.singleShot(30, guard(lambda: wait_loaded(t0, k, steps, visited)))

    def switching_done():
        QTimer.singleShot(2000, guard(sample_after))

    def sample_after():
        mb, n, cpu0 = tree()
        res["mem_after_tabs_mb"], res["procs_after_tabs"] = round(mb, 1), n
        res["breakdown_after_tabs"] = breakdown()
        w0 = time.time()
        QTimer.singleShot(10000, guard(lambda: idle_done(cpu0, w0)))

    def idle_done(cpu0, w0):
        mb, n, cpu1 = tree()
        res["idle_cpu_pct"] = round((cpu1 - cpu0) / max(0.001, time.time() - w0) * 100, 2)
        res["summary"] = {k: stats(res.get(k + "_ms", [])) for k in
                          ("first_call", "first_idle", "first_ready", "revisit_call", "revisit_idle")}
        finish()

    QTimer.singleShot(0, guard(wait_ready))


if __name__ == "__main__":
    try:
        # pythonw has no console: send output to a log file and keep the app alive on stray errors
        if sys.stdout is None:
            sys.stdout = open(os.devnull, "w")
        if sys.stderr is None:
            try:
                DATA.mkdir(parents=True, exist_ok=True)
                sys.stderr = open(DATA / "error.log", "a", buffering=1, encoding="utf-8")
            except Exception:
                sys.stderr = open(os.devnull, "w")

        def _hook(t, v, tb):
            try:
                import traceback
                sys.stderr.write("".join(traceback.format_exception(t, v, tb)) + "\n")
            except Exception:
                pass
        sys.excepthook = _hook
        try:
            import faulthandler                  # a native crash then leaves the Python stack in error.log
            faulthandler.enable(file=sys.stderr, all_threads=True)
        except Exception:
            pass
        app = QApplication(sys.argv)
        _mark("qapp_created")
        argv = sys.argv[1:]
        bench_out = None
        if "--bench-out" in argv:         # benchmark mode: isolated run, writes a JSON report and quits
            k = argv.index("--bench-out")
            bench_out = argv[k + 1] if k + 1 < len(argv) else None
            del argv[k:k + 2]
        arg = normalize_arg(argv[0]) if argv else ""
        if not bench_out and send_to_running(arg):          # already running: pass the link over and quit
            sys.exit(0)
        icons = DATA / "icons"
        icons.mkdir(parents=True, exist_ok=True)
        ico = icons / "litebrowser.ico"
        if ico.exists() and ico.stat().st_size > 0:          # drawn once, then reused (saves time on every start)
            app_icon = QIcon(str(ico))
            APP_ICON_PATH = str(ico)
        else:
            app_pm = make_app_icon()
            if app_pm.save(str(ico), "ICO"):
                APP_ICON_PATH = str(ico)
            app_icon = QIcon(app_pm)
        app.setWindowIcon(app_icon)
        splash = None
        if not bench_out:                                    # something to look at while the engine starts
            splash = Splash(app_icon)
            splash.show()
            app.processEvents()
        app.setStyle("Fusion")
        app.setPalette(make_palette())
        close_png = icons / "close.png"
        if not close_png.exists():
            pm_icon("close", "#f3d6da", size=16, width=5).save(str(close_png))
        app.setStyleSheet(STYLE.replace("__CLOSE__", close_png.as_posix()))
        _mark("style_icons_done")
        if bench_out and os.environ.get("LB_PROFILE"):       # benchmark.py --profile: where does window start-up time go?
            import cProfile
            import io as _io
            import pstats
            pr = cProfile.Profile()
            pr.enable()
            win = Browser(arg)
            pr.disable()
            buf = _io.StringIO()
            pstats.Stats(pr, stream=buf).sort_stats("cumulative").print_stats(45)
            Path(bench_out + ".profile.txt").write_text(buf.getvalue(), encoding="utf-8")
        else:
            win = Browser(arg)
        _mark("browser_built")
        if not bench_out:
            server = QLocalServer()
            QLocalServer.removeServer(SERVER_NAME)
            server.listen(SERVER_NAME)
            server.newConnection.connect(lambda: on_instance_connection(server, win))
        app.aboutToQuit.connect(win.cookies.save)
        app.aboutToQuit.connect(win.adblock.save)
        app.aboutToQuit.connect(win.save_session)
        app.aboutToQuit.connect(win.history.flush)
        win.show()
        _mark("shown")
        if not bench_out:
            try:
                win.setWindowOpacity(0.0)
                _oa = QPropertyAnimation(win, b"windowOpacity", win)
                _oa.setDuration(240)
                _oa.setStartValue(0.0)
                _oa.setEndValue(1.0)
                _oa.setEasingCurve(QEasingCurve.Type.OutCubic)
                _oa.finished.connect(lambda: win.setWindowOpacity(1.0))
                _oa.start()
                win._open_anim = _oa
            except Exception:
                pass
        if splash is not None:
            splash.close()
        if bench_out:
            start_bench(win, app, bench_out)
        import gc                      # fewer/shorter garbage-collection pauses
        gc.collect()
        gc.freeze()
        gc.set_threshold(40000, 25, 25)
        _rc = app.exec()
        if not bench_out:
            _wd = threading.Timer(4.0, lambda: os._exit(0))   # if the engine ever hangs while closing, still end the process
            _wd.daemon = True
            _wd.start()
            win.shutdown_web()
            try:
                sys.stdout.flush()
                sys.stderr.flush()
            except Exception:
                pass
            os._exit(_rc)                                    # no hidden leftover process that blocks the next start
        sys.exit(_rc)

    except SystemExit:
        raise
    except BaseException:
        import traceback
        _fatal("LiteBrowser could not start", traceback.format_exc())
        os._exit(1)
