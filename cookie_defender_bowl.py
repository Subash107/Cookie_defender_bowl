#always keep open the tab
# cookie_defender_fishbowl.py
"""
Fishbowl Cookies + Windows Defender Threat Counter Auto-Drop (Windows)

What it does:
- Reads Windows Defender status + threat detections via PowerShell:
    - Get-MpComputerStatus
    - Get-MpThreatDetection
- Auto-drops cookies when NEW detections appear (delta-based, not duplicate spam).
- Colors cookies by severity (Severe/High -> red, Moderate -> orange, Low -> yellow, Unknown -> purple).
- Keeps: anti-flicker (sleeping bodies), underwater tint + wobble, 3D highlight cookies, export JSON.

Run:
  python cookie_defender_fishbowl.py

Build EXE:
  python -m PyInstaller --onefile --noconsole cookie_defender_fishbowl.py

Notes:
- Requires Windows + Microsoft Defender cmdlets available.
- Some systems may require running PowerShell with permission; app handles failures gracefully.
"""

from __future__ import annotations

import json
import math
import random
import subprocess
import threading
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Optional
import tkinter as tk
from tkinter import ttk

COLORS = [
    "green", "blue", "yellow", "red", "purple", "orange",
    "pink", "brown", "black", "white", "cyan", "magenta",
]

# Physics tuning
GRAVITY_AIR = 1750.0
GRAVITY_WATER = 720.0
BOWL_RESTITUTION = 0.45
COOKIE_RESTITUTION = 0.10
FRICTION_AIR = 0.985
FRICTION_WATER = 0.965
MAX_COOKIES = 260

# Stability tuning
SLEEP_SPEED = 22.0
SLEEP_FRAMES = 18
COLLISION_PASSES = 2
SUBSTEPS = 2

# Fill thresholds
OVERFLOW_AT = 0.95
HARD_STOP_AT = 1.10

# Underwater visuals
WATER_TINT = (40, 110, 170)
UNDERWATER_DARKEN = 0.65
TINT_STRENGTH = 0.35

# Underwater wobble
WOBBLE_ACCEL = 120.0
WOBBLE_FREQ_MIN = 0.6
WOBBLE_FREQ_MAX = 1.6
WOBBLE_DAMP = 0.10

# Cookie 3D look
HIGHLIGHT_SCALE = 0.36
HIGHLIGHT_OFFSET = (-0.28, -0.28)
HIGHLIGHT_ALPHA_SIM = 0.72
OUTLINE_COLOR = "#2a2a2a"
SHADOW_COLOR = "#d9d9d9"

# Defender polling
DEFENDER_POLL_SECONDS = 4.0
MAX_DROPS_PER_TICK = 6  # prevents huge bursts freezing UI


@dataclass
class CookieBody:
    color_name: str
    r: float
    x: float
    y: float
    vx: float
    vy: float
    item_id: int
    shadow_id: int
    highlight_id: int
    asleep: bool = False
    sleep_counter: int = 0
    underwater: bool = False
    wobble_phase: float = 0.0
    wobble_freq: float = 1.0


def safe_fg(bg: str) -> str:
    dark = {"black", "brown", "purple", "blue", "red", "magenta"}
    return "white" if bg.lower() in dark else "black"


def clamp(v: float, lo: float, hi: float) -> float:
    return lo if v < lo else hi if v > hi else v


def gray(level: int) -> str:
    level = int(clamp(level, 0, 255))
    return f"#{level:02x}{level:02x}{level:02x}"


def rgb_to_hex(rgb: tuple[int, int, int]) -> str:
    r, g, b = (int(clamp(rgb[0], 0, 255)), int(clamp(rgb[1], 0, 255)), int(clamp(rgb[2], 0, 255)))
    return f"#{r:02x}{g:02x}{b:02x}"


def hex_to_rgb(h: str) -> tuple[int, int, int]:
    h = h.lstrip("#")
    if len(h) == 3:
        h = "".join(ch * 2 for ch in h)
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


def blend_rgb(a: tuple[int, int, int], b: tuple[int, int, int], t: float) -> tuple[int, int, int]:
    t = clamp(t, 0.0, 1.0)
    return (
        int(a[0] * (1 - t) + b[0] * t),
        int(a[1] * (1 - t) + b[1] * t),
        int(a[2] * (1 - t) + b[2] * t),
    )


COLOR_RGB: dict[str, tuple[int, int, int]] = {
    "green": (0, 128, 0),
    "blue": (0, 0, 255),
    "yellow": (255, 255, 0),
    "red": (255, 0, 0),
    "purple": (128, 0, 128),
    "orange": (255, 165, 0),
    "pink": (255, 192, 203),
    "brown": (139, 69, 19),
    "black": (0, 0, 0),
    "white": (255, 255, 255),
    "cyan": (0, 255, 255),
    "magenta": (255, 0, 255),
}


def underwater_color(name: str) -> str:
    base = COLOR_RGB.get(name.lower(), (180, 180, 180))
    dark = (base[0] * UNDERWATER_DARKEN, base[1] * UNDERWATER_DARKEN, base[2] * UNDERWATER_DARKEN)
    tint = (
        dark[0] * (1 - TINT_STRENGTH) + WATER_TINT[0] * TINT_STRENGTH,
        dark[1] * (1 - TINT_STRENGTH) + WATER_TINT[1] * TINT_STRENGTH,
        dark[2] * (1 - TINT_STRENGTH) + WATER_TINT[2] * TINT_STRENGTH,
    )
    return rgb_to_hex((int(tint[0]), int(tint[1]), int(tint[2])))


def highlight_color(fill_hex_or_name: str) -> str:
    if fill_hex_or_name.startswith("#"):
        base = hex_to_rgb(fill_hex_or_name)
    else:
        base = COLOR_RGB.get(fill_hex_or_name.lower(), (180, 180, 180))
    return rgb_to_hex(blend_rgb(base, (255, 255, 255), HIGHLIGHT_ALPHA_SIM))


def defender_severity_to_cookie_color(severity_id: Optional[int], severity_text: Optional[str]) -> str:
    """
    Defender fields vary by system/version.
    Heuristic mapping:
      Severe/High -> red
      Medium/Moderate -> orange
      Low -> yellow
      Unknown -> purple
    """
    if severity_text:
        s = severity_text.strip().lower()
        if "severe" in s or "high" in s:
            return "red"
        if "moder" in s or "medium" in s:
            return "orange"
        if "low" in s:
            return "yellow"
    if severity_id is None:
        return "purple"
    if severity_id >= 5:
        return "red"
    if severity_id == 4:
        return "red"
    if severity_id in (2, 3):
        return "orange"
    if severity_id == 1:
        return "yellow"
    return "purple"


class EllipseBowlCollider:
    def __init__(self, cx: float, cy: float, a: float, b: float, rim_y: float) -> None:
        self.cx = cx
        self.cy = cy
        self.a = a
        self.b = b
        self.rim_y = rim_y
        self._rim_left = cx - a * 0.3
        self._rim_right = cx + a * 0.3
        self._bowl_area = 1.0
        self._recalc_rim()
        self._recalc_area()

    def _recalc_rim(self) -> None:
        dy = (self.rim_y - self.cy)
        t = 1.0 - (dy * dy) / (self.b * self.b)
        if t <= 0:
            self._rim_left = self.cx - self.a * 0.05
            self._rim_right = self.cx + self.a * 0.05
            return
        dx = self.a * math.sqrt(t)
        self._rim_left = self.cx - dx
        self._rim_right = self.cx + dx

    def _recalc_area(self) -> None:
        samples_x = 140
        samples_y = 180
        x0 = self.cx - self.a
        x1 = self.cx + self.a
        y0 = self.rim_y
        y1 = self.cy + self.b
        dx = (x1 - x0) / samples_x
        dy = (y1 - y0) / samples_y

        inside = 0
        total = samples_x * samples_y
        for iy in range(samples_y):
            y = y0 + (iy + 0.5) * dy
            for ix in range(samples_x):
                x = x0 + (ix + 0.5) * dx
                if self.is_inside_point(x, y):
                    inside += 1
        rect_area = (x1 - x0) * (y1 - y0)
        self._bowl_area = max(1.0, rect_area * (inside / total))

    @property
    def rim_left(self) -> float:
        return self._rim_left

    @property
    def rim_right(self) -> float:
        return self._rim_right

    @property
    def bowl_area(self) -> float:
        return self._bowl_area

    def is_inside_point(self, x: float, y: float) -> bool:
        dx = (x - self.cx) / self.a
        dy = (y - self.cy) / self.b
        return (dx * dx + dy * dy) <= 1.0 and y >= self.rim_y

    def opening_clamp_x(self, x: float, r: float) -> float:
        return clamp(x, self._rim_left + r + 6.0, self._rim_right - r - 6.0)

    def collide_cookie(self, c: CookieBody) -> None:
        if c.y < self.rim_y - c.r * 0.6:
            c.x = self.opening_clamp_x(c.x, c.r)
            return

        a = max(5.0, self.a - c.r)
        b = max(5.0, self.b - c.r)
        dx = c.x - self.cx
        dy = c.y - self.cy

        ex = dx / a
        ey = dy / b
        s2 = ex * ex + ey * ey

        if s2 <= 1.0:
            if c.y < self.rim_y + c.r:
                c.x = self.opening_clamp_x(c.x, c.r)
            return

        s = math.sqrt(s2) if s2 > 1e-12 else 1.0
        c.x = self.cx + dx / s
        c.y = self.cy + dy / s

        nx = dx / (a * a)
        ny = dy / (b * b)
        nlen = math.hypot(nx, ny)
        if nlen < 1e-9:
            return
        nx /= nlen
        ny /= nlen

        vdotn = c.vx * nx + c.vy * ny
        c.vx = c.vx - (1.0 + BOWL_RESTITUTION) * vdotn * nx
        c.vy = c.vy - (1.0 + BOWL_RESTITUTION) * vdotn * ny
        c.vx *= 0.99
        c.vy *= 0.995

        if c.y < self.rim_y + c.r:
            c.x = self.opening_clamp_x(c.x, c.r)


def run_powershell_json(command: str, timeout: float = 6.0) -> Any:
    completed = subprocess.run(
        ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", command],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if completed.returncode != 0:
        raise RuntimeError((completed.stderr or completed.stdout or "").strip() or "PowerShell error")
    out = (completed.stdout or "").strip()
    if not out:
        return None
    return json.loads(out)


def fetch_defender_snapshot() -> dict[str, Any]:
    status_cmd = (
        "Get-MpComputerStatus | "
        "Select-Object AMServiceEnabled,AntivirusEnabled,RealTimeProtectionEnabled,"
        "BehaviorMonitorEnabled,IoavProtectionEnabled,AntispywareEnabled,IsTamperProtected,"
        "SignatureAge,EngineVersion,AntivirusSignatureVersion | "
        "ConvertTo-Json -Depth 3"
    )
    threats_cmd = (
        "Get-MpThreatDetection | "
        "Select-Object ThreatName,SeverityID,Severity,ActionSuccess,DetectionTime,Resources | "
        "ConvertTo-Json -Depth 5"
    )

    status = run_powershell_json(status_cmd)
    threats = run_powershell_json(threats_cmd)

    if threats is None:
        threats_list: list[dict[str, Any]] = []
    elif isinstance(threats, list):
        threats_list = threats
    else:
        threats_list = [threats]

    return {"status": status, "threats": threats_list, "fetched_at": datetime.now().isoformat(timespec="seconds")}


class App:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Fishbowl Cookies + Windows Defender Threat Auto-Drop")
        self.root.resizable(False, False)

        self.canvas_w = 760
        self.canvas_h = 520

        self.bowl_cx = self.canvas_w * 0.52
        self.bowl_cy = self.canvas_h * 0.67
        self.bowl_a = self.canvas_w * 0.235
        self.bowl_b = self.canvas_h * 0.295
        self.rim_y = self.canvas_h * 0.30

        self.collider = EllipseBowlCollider(self.bowl_cx, self.bowl_cy, self.bowl_a, self.bowl_b, self.rim_y)
        self.water_y = self.rim_y + self.bowl_b * 0.20

        self.cookies: list[CookieBody] = []
        self.counts: dict[str, int] = {}

        self.auto_enabled = tk.BooleanVar(value=False)
        self.auto_rate = tk.DoubleVar(value=3.0)
        self.auto_random_color = tk.BooleanVar(value=True)
        self.auto_color = tk.StringVar(value=COLORS[0])
        self._auto_accum = 0.0

        # Defender auto-drop
        self.def_auto_drop = tk.BooleanVar(value=True)
        self.def_poll = tk.BooleanVar(value=True)
        self._defender_lock = threading.Lock()
        self._defender_last_ids: set[str] = set()
        self._defender_pending_colors: list[str] = []
        self._defender_last_error: str = ""
        self._defender_status_text: str = "Not checked yet"
        self._defender_total: int = 0
        self._defender_last_fetch: str = ""

        self._last_t = time.perf_counter()
        self._sim_t = 0.0

        self._build_ui()
        self._draw_bowl()

        self._start_defender_thread()
        self._loop()

    def _build_ui(self) -> None:
        outer = ttk.Frame(self.root, padding=12)
        outer.grid(row=0, column=0)

        ttk.Label(
            outer,
            text="Fishbowl Cookie Physics — Defender detections auto-drop cookies",
            font=("Segoe UI", 12, "bold"),
        ).grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 10))

        left = ttk.Frame(outer)
        left.grid(row=1, column=0, sticky="ns", padx=(0, 10))

        palette = ttk.LabelFrame(left, text="Palette (Click to drop)")
        palette.grid(row=0, column=0, sticky="ew")
        p = ttk.Frame(palette, padding=8)
        p.grid(row=0, column=0)

        for i, color in enumerate(COLORS):
            r, c = divmod(i, 2)
            tk.Button(
                p, text=color, width=10, bg=color, fg=safe_fg(color),
                relief="raised", command=lambda col=color: self.spawn_cookie(col),
            ).grid(row=r, column=c, padx=5, pady=5, sticky="ew")

        autodrop = ttk.LabelFrame(left, text="Auto-drop (Manual stress test)")
        autodrop.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        a = ttk.Frame(autodrop, padding=8)
        a.grid(row=0, column=0, sticky="ew")

        ttk.Checkbutton(a, text="Enable Auto-drop", variable=self.auto_enabled).grid(row=0, column=0, sticky="w")
        ttk.Label(a, text="Rate (cookies/sec)").grid(row=1, column=0, sticky="w", pady=(8, 0))

        scale = ttk.Scale(a, from_=0.0, to=25.0, variable=self.auto_rate, orient="horizontal", length=210)
        scale.grid(row=2, column=0, sticky="ew")

        self.rate_label = ttk.Label(a, text="3.0 / sec", foreground="#555555")
        self.rate_label.grid(row=3, column=0, sticky="w", pady=(4, 0))

        def _upd(_evt: object = None) -> None:
            self.rate_label.config(text=f"{self.auto_rate.get():.1f} / sec")

        scale.bind("<B1-Motion>", _upd)
        scale.bind("<ButtonRelease-1>", _upd)
        _upd()

        ttk.Checkbutton(a, text="Random color", variable=self.auto_random_color).grid(row=4, column=0, sticky="w", pady=(10, 0))
        row = ttk.Frame(a)
        row.grid(row=5, column=0, sticky="ew", pady=(6, 0))
        ttk.Label(row, text="Fixed color:").grid(row=0, column=0, sticky="w")
        ttk.Combobox(row, values=COLORS, state="readonly", width=12, textvariable=self.auto_color).grid(row=0, column=1, padx=(8, 0), sticky="w")

        defender = ttk.LabelFrame(left, text="Windows Defender")
        defender.grid(row=2, column=0, sticky="ew", pady=(10, 0))
        d = ttk.Frame(defender, padding=8)
        d.grid(row=0, column=0, sticky="ew")

        ttk.Checkbutton(d, text="Poll Defender", variable=self.def_poll).grid(row=0, column=0, sticky="w")
        ttk.Checkbutton(d, text="Auto-drop from detections", variable=self.def_auto_drop).grid(row=1, column=0, sticky="w", pady=(4, 0))
        ttk.Button(d, text="Sync now", command=self.sync_defender_now).grid(row=2, column=0, sticky="w", pady=(8, 0))

        self.def_label = ttk.Label(d, text="Status: Not checked yet", foreground="#444")
        self.def_label.grid(row=3, column=0, sticky="w", pady=(8, 0))

        actions = ttk.LabelFrame(left, text="Actions")
        actions.grid(row=3, column=0, sticky="ew", pady=(10, 0))
        ac = ttk.Frame(actions, padding=8)
        ac.grid(row=0, column=0)
        ttk.Button(ac, text="Shake", command=self.shake).grid(row=0, column=0, padx=(0, 8))
        ttk.Button(ac, text="Clear", command=self.clear).grid(row=0, column=1, padx=(0, 8))
        ttk.Button(ac, text="Export JSON", command=self.export_json).grid(row=0, column=2)

        center = ttk.Frame(outer)
        center.grid(row=1, column=1)
        self.canvas = tk.Canvas(center, width=self.canvas_w, height=self.canvas_h, bg="white",
                                highlightthickness=1, highlightbackground="#dddddd")
        self.canvas.grid(row=0, column=0)

        right = ttk.Frame(outer)
        right.grid(row=1, column=2, sticky="ns", padx=(10, 0))

        meter = ttk.LabelFrame(right, text="Bowl Fill")
        meter.grid(row=0, column=0, sticky="ew")
        m = ttk.Frame(meter, padding=10)
        m.grid(row=0, column=0)
        self.fill_var = tk.DoubleVar(value=0.0)
        ttk.Progressbar(m, orient="horizontal", length=220, mode="determinate",
                        maximum=100.0, variable=self.fill_var).grid(row=0, column=0, sticky="ew")
        self.fill_label = ttk.Label(m, text="0.0%")
        self.fill_label.grid(row=1, column=0, sticky="w", pady=(6, 0))
        self.warn_label = ttk.Label(m, text="", foreground="#b00020")
        self.warn_label.grid(row=2, column=0, sticky="w", pady=(6, 0))

        stats = ttk.LabelFrame(right, text="Counts")
        stats.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        s = ttk.Frame(stats, padding=10)
        s.grid(row=0, column=0)
        self.total_label = ttk.Label(s, text="Total: 0", font=("Segoe UI", 10, "bold"))
        self.total_label.grid(row=0, column=0, sticky="w")
        self.listbox = tk.Listbox(s, width=24, height=17)
        self.listbox.grid(row=1, column=0, pady=(8, 0))

        self.status = ttk.Label(right, text="", foreground="#555555")
        self.status.grid(row=2, column=0, sticky="w", pady=(10, 0))

    def _draw_bowl(self) -> None:
        self.canvas.delete("bowl")
        cx, cy, a, b, rim_y = self.bowl_cx, self.bowl_cy, self.bowl_a, self.bowl_b, self.rim_y

        self.canvas.create_oval(int(cx - a * 1.05), int(cy + b * 0.80),
                                int(cx + a * 1.05), int(cy + b * 1.02),
                                fill=gray(220), outline="", tags="bowl")

        self.canvas.create_oval(int(cx - a), int(cy - b), int(cx + a), int(cy + b),
                                fill=gray(248), outline=gray(135), width=3, tags="bowl")

        for i in range(16):
            inset_x = a * (0.05 + i * 0.012)
            inset_y = b * (0.06 + i * 0.010)
            shade = 250 - i * 4
            self.canvas.create_oval(int(cx - a + inset_x), int(cy - b + inset_y),
                                    int(cx + a - inset_x), int(cy + b - inset_y),
                                    fill=gray(shade), outline="", tags="bowl")

        rim_w = a * 1.03
        rim_h = b * 0.17
        self.canvas.create_oval(int(cx - rim_w), int(rim_y - rim_h),
                                int(cx + rim_w), int(rim_y + rim_h),
                                fill="white", outline=gray(125), width=2, tags="bowl")
        self.canvas.create_oval(int(cx - rim_w * 0.98), int(rim_y - rim_h * 0.70),
                                int(cx + rim_w * 0.98), int(rim_y + rim_h * 0.70),
                                fill="", outline=gray(85), width=2, tags="bowl")

        water_top = self.water_y
        self.canvas.create_oval(int(cx - a * 0.92), int(water_top),
                                int(cx + a * 0.92), int(cy + b * 0.92),
                                fill=rgb_to_hex((220, 238, 250)), outline="", tags="bowl")
        self.canvas.create_line(int(cx - a * 0.92), int(water_top),
                                int(cx + a * 0.92), int(water_top),
                                fill=gray(95), width=3, tags="bowl")

        self.canvas.create_oval(int(cx - a * 0.78), int(cy - b * 0.85),
                                int(cx - a * 0.40), int(cy + b * 0.75),
                                fill="white", outline="", tags="bowl")

        self.canvas.create_text(self.canvas_w // 2, 26,
                                text="Defender detections → auto-drop cookies (severity color). Underwater: tinted + wobble.",
                                fill="#888", font=("Segoe UI", 10), tags="bowl")
        self.canvas.tag_lower("bowl")

    # ---------- Defender ----------
    def _start_defender_thread(self) -> None:
        t = threading.Thread(target=self._defender_loop, daemon=True)
        t.start()

    def sync_defender_now(self) -> None:
        threading.Thread(target=self._defender_sync_once, daemon=True).start()

    def _defender_loop(self) -> None:
        while True:
            try:
                if self.def_poll.get():
                    self._defender_sync_once()
            except Exception:
                pass
            time.sleep(DEFENDER_POLL_SECONDS)

    def _defender_sync_once(self) -> None:
        try:
            snap = fetch_defender_snapshot()
            threats = snap.get("threats", [])
            status = snap.get("status", {}) or {}
            fetched_at = snap.get("fetched_at", "")

            # Build stable ids for detections (best-effort)
            new_colors: list[str] = []
            current_ids: set[str] = set()

            for t in threats:
                name = str(t.get("ThreatName", "") or "")
                det_time = str(t.get("DetectionTime", "") or "")
                sev_id = t.get("SeverityID", None)
                sev_txt = t.get("Severity", None)
                res = t.get("Resources", "")
                rid = f"{name}|{det_time}|{sev_id}|{res}"
                current_ids.add(rid)
                if rid not in self._defender_last_ids:
                    new_colors.append(defender_severity_to_cookie_color(
                        int(sev_id) if isinstance(sev_id, (int, float)) else None,
                        str(sev_txt) if sev_txt is not None else None,
                    ))

            am_on = bool(status.get("AMServiceEnabled", False))
            av_on = bool(status.get("AntivirusEnabled", False))
            rtp = bool(status.get("RealTimeProtectionEnabled", False))
            sig_age = status.get("SignatureAge", None)
            ver = status.get("AntivirusSignatureVersion", None)

            status_line = f"Status: AM={am_on} AV={av_on} RTP={rtp} | Detections={len(threats)}"
            if sig_age is not None:
                status_line += f" | SigAge={sig_age}"
            if ver is not None:
                status_line += f" | SigVer={ver}"

            with self._defender_lock:
                self._defender_last_error = ""
                self._defender_status_text = status_line
                self._defender_total = len(threats)
                self._defender_last_fetch = fetched_at
                self._defender_last_ids = current_ids
                if new_colors:
                    self._defender_pending_colors.extend(new_colors)

        except Exception as e:
            with self._defender_lock:
                self._defender_last_error = str(e)
                self._defender_status_text = "Status: Error reading Defender (see right panel)"
                self._defender_last_fetch = datetime.now().isoformat(timespec="seconds")

    # ---------- Cookies ----------
    def _cookie_fill(self, c: CookieBody) -> str:
        return underwater_color(c.color_name) if c.underwater else c.color_name

    def _highlight_fill(self, c: CookieBody) -> str:
        return highlight_color(self._cookie_fill(c))

    def spawn_cookie(self, color: str) -> None:
        ratio = self._fill_ratio()
        if ratio >= HARD_STOP_AT:
            self.status.config(text="Hard stop: bowl is overfilled. Clear some cookies.")
            return
        if len(self.cookies) >= MAX_COOKIES and ratio >= OVERFLOW_AT:
            self.status.config(text="Too many cookies for stability. Clear or export.")
            return

        r = random.uniform(11.0, 18.0)
        x = random.uniform(self.collider.rim_left + r + 10, self.collider.rim_right - r - 10)
        y = self.collider.rim_y - r - random.uniform(45.0, 120.0)
        vx = random.uniform(-240.0, 240.0)
        vy = random.uniform(-40.0, 120.0)

        shadow_id = self.canvas.create_oval(
            int(x - r * 0.92), int((y + r * 0.60) - r * 0.18),
            int(x + r * 0.92), int((y + r * 0.60) + r * 0.18),
            fill=SHADOW_COLOR, outline="", tags="cookie"
        )
        item_id = self.canvas.create_oval(
            int(x - r), int(y - r), int(x + r), int(y + r),
            fill=color, outline=OUTLINE_COLOR, width=1, tags="cookie"
        )
        hr = r * HIGHLIGHT_SCALE
        hx = x + HIGHLIGHT_OFFSET[0] * r
        hy = y + HIGHLIGHT_OFFSET[1] * r
        highlight_id = self.canvas.create_oval(
            int(hx - hr), int(hy - hr), int(hx + hr), int(hy + hr),
            fill=highlight_color(color), outline="", tags="cookie"
        )

        c = CookieBody(
            color_name=color, r=r, x=x, y=y, vx=vx, vy=vy,
            item_id=item_id, shadow_id=shadow_id, highlight_id=highlight_id,
            wobble_phase=random.random() * math.tau,
            wobble_freq=random.uniform(WOBBLE_FREQ_MIN, WOBBLE_FREQ_MAX),
        )

        self.cookies.append(c)
        self.counts[color] = self.counts.get(color, 0) + 1
        self._refresh_stats()

    def _apply_underwater_mode(self, c: CookieBody) -> None:
        is_under = c.y >= self.water_y
        if is_under == c.underwater:
            return
        c.underwater = is_under
        self.canvas.itemconfigure(c.item_id, fill=self._cookie_fill(c))
        self.canvas.itemconfigure(c.highlight_id, fill=self._highlight_fill(c))

        if is_under:
            c.vx *= 0.78
            c.vy *= 0.60
        else:
            c.vx *= 1.05

    def _underwater_wobble_ax(self, c: CookieBody) -> float:
        speed = math.hypot(c.vx, c.vy)
        fade = clamp(speed / (SLEEP_SPEED * 2.5), 0.0, 1.0)
        wob = math.sin(c.wobble_phase + math.tau * c.wobble_freq * self._sim_t)
        return WOBBLE_ACCEL * wob * fade

    # ---------- Actions ----------
    def shake(self) -> None:
        for c in self.cookies:
            c.asleep = False
            c.sleep_counter = 0
            c.vx += random.uniform(-760.0, 760.0)
            c.vy += random.uniform(-560.0, 220.0)

    def clear(self) -> None:
        self.canvas.delete("cookie")
        self.cookies.clear()
        self.counts.clear()
        self._auto_accum = 0.0
        with self._defender_lock:
            self._defender_pending_colors.clear()
        self._refresh_stats()
        self._refresh_fill_meter()
        self.status.config(text="")

    def export_json(self) -> None:
        with self._defender_lock:
            defender = {
                "status_text": self._defender_status_text,
                "last_error": self._defender_last_error,
                "total_detections": self._defender_total,
                "last_fetch": self._defender_last_fetch,
            }

        payload = {
            "exported_at": datetime.now().isoformat(timespec="seconds"),
            "total_cookies": len(self.cookies),
            "cookie_counts": dict(sorted(self.counts.items(), key=lambda kv: kv[0])),
            "fill_percent": round(self._fill_ratio() * 100.0, 2),
            "defender": defender,
        }
        out = Path.cwd() / "cookie_defender_export.json"
        out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        self.status.config(text=f"Exported: {out.name}")

    # ---------- Loop / physics ----------
    def _loop(self) -> None:
        now = time.perf_counter()
        dt = min(now - self._last_t, 1 / 30)
        self._last_t = now
        self._sim_t += dt

        self._auto_drop_step(dt)
        self._defender_drop_step()
        self._step(dt)
        self._render()
        self._update_defender_ui()

        self.root.after(16, self._loop)

    def _auto_drop_step(self, dt: float) -> None:
        if not self.auto_enabled.get():
            self._auto_accum = 0.0
            return
        rate = max(0.0, float(self.auto_rate.get()))
        if rate <= 0.0:
            return

        self._auto_accum += dt * rate
        to_spawn = int(self._auto_accum)
        if to_spawn <= 0:
            return
        self._auto_accum -= to_spawn
        to_spawn = min(to_spawn, 10)

        for _ in range(to_spawn):
            color = random.choice(COLORS) if self.auto_random_color.get() else (self.auto_color.get() or COLORS[0])
            self.spawn_cookie(color)

    def _defender_drop_step(self) -> None:
        if not self.def_auto_drop.get():
            return
        dropped = 0
        with self._defender_lock:
            while self._defender_pending_colors and dropped < MAX_DROPS_PER_TICK:
                color = self._defender_pending_colors.pop(0)
                self.spawn_cookie(color)
                dropped += 1

    def _step(self, dt: float) -> None:
        sub_dt = dt / SUBSTEPS
        for _ in range(SUBSTEPS):
            for c in self.cookies:
                self._apply_underwater_mode(c)
                if c.asleep:
                    continue

                gravity = GRAVITY_WATER if c.underwater else GRAVITY_AIR
                friction = FRICTION_WATER if c.underwater else FRICTION_AIR

                if c.underwater:
                    c.vx += self._underwater_wobble_ax(c) * sub_dt
                    c.vx *= (1.0 - WOBBLE_DAMP * sub_dt)

                c.vy += gravity * sub_dt
                c.x += c.vx * sub_dt
                c.y += c.vy * sub_dt
                c.vx *= friction
                c.vy *= 0.999 if not c.underwater else 0.990

                self.collider.collide_cookie(c)

            for _pass in range(COLLISION_PASSES):
                n = len(self.cookies)
                for i in range(n):
                    a = self.cookies[i]
                    for j in range(i + 1, n):
                        b = self.cookies[j]
                        self._resolve_circle_collision(a, b)

        for c in self.cookies:
            if c.asleep:
                continue
            speed = math.hypot(c.vx, c.vy)
            if speed < SLEEP_SPEED and c.y > self.collider.rim_y + c.r:
                c.sleep_counter += 1
                if c.sleep_counter >= SLEEP_FRAMES:
                    c.asleep = True
                    c.vx = 0.0
                    c.vy = 0.0
            else:
                c.sleep_counter = 0

        self._refresh_fill_meter()

    def _resolve_circle_collision(self, a: CookieBody, b: CookieBody) -> None:
        dx = b.x - a.x
        dy = b.y - a.y
        dist2 = dx * dx + dy * dy
        min_dist = a.r + b.r

        if dist2 <= 1e-9:
            ang = random.random() * math.tau
            dx = math.cos(ang) * 0.01
            dy = math.sin(ang) * 0.01
            dist2 = dx * dx + dy * dy

        if dist2 >= min_dist * min_dist:
            return

        dist = math.sqrt(dist2)
        nx = dx / dist
        ny = dy / dist
        overlap = (min_dist - dist)

        if a.asleep and not b.asleep:
            b.x += nx * overlap
            b.y += ny * overlap
        elif b.asleep and not a.asleep:
            a.x -= nx * overlap
            a.y -= ny * overlap
        else:
            push = overlap * 0.5
            a.x -= nx * push
            a.y -= ny * push
            b.x += nx * push
            b.y += ny * push

        if overlap > 0.6:
            a.asleep = False
            b.asleep = False
            a.sleep_counter = 0
            b.sleep_counter = 0

        rvx = b.vx - a.vx
        rvy = b.vy - a.vy
        vel_n = rvx * nx + rvy * ny
        if vel_n > 0:
            return

        j = -(1.0 + COOKIE_RESTITUTION) * vel_n / 2.0
        ix = j * nx
        iy = j * ny

        if not a.asleep:
            a.vx -= ix
            a.vy -= iy
        if not b.asleep:
            b.vx += ix
            b.vy += iy

    def _render(self) -> None:
        for c in self.cookies:
            shadow_y = c.y + c.r * 0.60
            self.canvas.coords(
                c.shadow_id,
                int(c.x - c.r * 0.92), int(shadow_y - c.r * 0.18),
                int(c.x + c.r * 0.92), int(shadow_y + c.r * 0.18),
            )
            self.canvas.coords(
                c.item_id,
                int(c.x - c.r), int(c.y - c.r),
                int(c.x + c.r), int(c.y + c.r),
            )
            hr = c.r * HIGHLIGHT_SCALE
            hx = c.x + HIGHLIGHT_OFFSET[0] * c.r
            hy = c.y + HIGHLIGHT_OFFSET[1] * c.r
            self.canvas.coords(
                c.highlight_id,
                int(hx - hr), int(hy - hr), int(hx + hr), int(hy + hr),
            )
            self.canvas.tag_raise(c.highlight_id, c.item_id)

        self.canvas.tag_lower("bowl")

    # ---------- UI updates ----------
    def _update_defender_ui(self) -> None:
        with self._defender_lock:
            txt = self._defender_status_text
            err = self._defender_last_error
            pending = len(self._defender_pending_colors)
            last_fetch = self._defender_last_fetch

        if err:
            self.def_label.config(text=f"{txt}\nError: {err}\nLast: {last_fetch}", foreground="#b00020")
        else:
            extra = f" | Pending drops: {pending}"
            self.def_label.config(text=f"{txt}{extra}\nLast: {last_fetch}", foreground="#444")

    # ---------- Fill / stats ----------
    def _fill_ratio(self) -> float:
        filled = 0.0
        for c in self.cookies:
            filled += math.pi * c.r * c.r
        return filled / max(1.0, self.collider.bowl_area)

    def _refresh_fill_meter(self) -> None:
        ratio = self._fill_ratio()
        pct = ratio * 100.0
        self.fill_var.set(min(pct, 150.0))
        self.fill_label.config(text=f"{pct:.1f}%")
        if ratio >= HARD_STOP_AT:
            self.warn_label.config(text="OVERFLOW: Hard stop reached")
        elif ratio >= OVERFLOW_AT:
            self.warn_label.config(text="Warning: Bowl almost full")
        else:
            self.warn_label.config(text="")

    def _refresh_stats(self) -> None:
        self.total_label.config(text=f"Total: {len(self.cookies)}")
        self.listbox.delete(0, tk.END)
        for color in sorted(self.counts.keys()):
            self.listbox.insert(tk.END, f"{color:>8}  x {self.counts[color]}")


def main() -> None:
    root = tk.Tk()
    style = ttk.Style()
    try:
        style.theme_use("clam")
    except tk.TclError:
        pass
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
