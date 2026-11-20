#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Времето в България – карта с температури и приблизителни фронтове.

Само стандартен Python 3 + tkinter (без допълнителни пакети).
Данни: Open-Meteo (безплатно, без регистрация, нужен е интернет).
Контур на България: Natural Earth (обществено достояние), вграден в програмата.

Ако нещо не работи, програмата записва подробности във файла:
    ~/bg_vreme_log.txt   (в личната ти папка)
"""

import bisect  # noqa: F401  (запазено за бъдещи нужди)
import json
import math
import os
import threading
import traceback
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone

import tkinter as tk
from tkinter import font as tkfont

# --------------------------------------------------------------------------
#  НАСТРОЙКИ (можеш спокойно да ги променяш)
# --------------------------------------------------------------------------
OFFSETS = list(range(0, 73))                          # часове напред: 0 … 72
REFRESH_MS = 30 * 60 * 1000  # презареждане на данните на 30 минути
RETRY_MS = 30 * 1000         # при грешка – нов опит след 30 секунди
FRONT_TH = 0.20              # праг на температурна адвекция (K/час).
                             # По-малко = повече/по-големи фронтове
CELL = 4                     # размер на "пиксела" на оцветяването

# Цветове
C_OUT = "#E6EAEE"    # извън България
C_LAND = "#F7F3E8"   # суша без фронт
C_COLD = "#C2DBFF"   # блед син  – студен фронт
C_WARM = "#FFC9C9"   # блед червен – топъл фронт
C_BORDER = "#56626C"

# Граници на картата
LON0, LON1 = 22.0, 29.0
LAT0, LAT1 = 40.9, 44.7

# Мрежа от точки за изчисляване на фронтовете
GRID_LONS = [22.0 + 0.7 * i for i in range(11)]   # 22.0 … 29.0
GRID_LATS = [41.0 + 0.5 * j for j in range(8)]    # 41.0 … 44.5

WEEKDAYS = ["понеделник", "вторник", "сряда", "четвъртък",
            "петък", "събота", "неделя"]

# (име, ширина, дължина)
CITIES = [
    ("София", 42.70, 23.32), ("Пловдив", 42.15, 24.75),
    ("Варна", 43.21, 27.91), ("Бургас", 42.50, 27.47),
    ("Русе", 43.85, 25.97), ("Стара Загора", 42.43, 25.64),
    ("Плевен", 43.42, 24.62), ("Велико Търново", 43.08, 25.65),
    ("Добрич", 43.57, 27.83), ("Шумен", 43.27, 26.93),
    ("Сливен", 42.68, 26.32), ("Хасково", 41.93, 25.56),
    ("Благоевград", 42.02, 23.09), ("Кърджали", 41.65, 25.37),
    ("Видин", 43.99, 22.87), ("Монтана", 43.41, 23.23),
    ("Враца", 43.20, 23.55), ("Ловеч", 43.14, 24.72),
    ("Габрово", 42.87, 25.33), ("Разград", 43.53, 26.52),
    ("Силистра", 44.12, 27.26), ("Ямбол", 42.48, 26.51),
    ("Смолян", 41.58, 24.71), ("Кюстендил", 42.28, 22.69),
    ("Сандански", 41.57, 23.28), ("Свиленград", 41.77, 26.20),
]

# Контур на България [дължина, ширина]
RING = [[26.333,41.713],[26.274,41.715],[26.234,41.746],[26.212,41.75],[26.19,41.735],[26.108,41.728],[26.054,41.702],[26.047,41.675],[26.055,41.649],[26.067,41.635],[26.107,41.624],[26.115,41.617],[26.13,41.583],[26.131,41.553],[26.158,41.542],[26.163,41.506],[26.146,41.478],[26.174,41.446],[26.176,41.432],[26.159,41.422],[26.121,41.358],[26.022,41.342],[25.96,41.315],[25.921,41.316],[25.882,41.304],[25.863,41.31],[25.833,41.335],[25.811,41.341],[25.763,41.319],[25.717,41.314],[25.68,41.297],[25.64,41.311],[25.551,41.316],[25.538,41.312],[25.524,41.292],[25.505,41.281],[25.453,41.28],[25.286,41.239],[25.239,41.241],[25.22,41.25],[25.177,41.294],[25.117,41.321],[25.102,41.337],[25.08,41.334],[24.886,41.401],[24.803,41.393],[24.803,41.362],[24.794,41.347],[24.774,41.348],[24.699,41.409],[24.638,41.418],[24.644,41.428],[24.596,41.43],[24.58,41.441],[24.581,41.46],[24.549,41.485],[24.543,41.521],[24.531,41.548],[24.51,41.562],[24.459,41.55],[24.439,41.528],[24.296,41.515],[24.287,41.518],[24.286,41.54],[24.251,41.563],[24.196,41.547],[24.182,41.537],[24.17,41.512],[24.146,41.527],[24.077,41.536],[24.047,41.526],[24.052,41.463],[24.035,41.451],[24.001,41.464],[23.965,41.438],[23.95,41.438],[23.895,41.464],[23.852,41.44],[23.777,41.429],[23.754,41.401],[23.672,41.403],[23.653,41.398],[23.612,41.371],[23.579,41.372],[23.513,41.398],[23.415,41.4],[23.347,41.371],[23.326,41.369],[23.288,41.398],[23.27,41.397],[23.224,41.379],[23.21,41.369],[23.2,41.333],[23.157,41.316],[23.115,41.313],[22.917,41.336],[22.941,41.35],[22.944,41.368],[22.937,41.411],[22.955,41.432],[22.946,41.453],[22.943,41.539],[22.949,41.561],[22.932,41.598],[22.936,41.626],[22.946,41.641],[22.967,41.647],[22.999,41.693],[23.01,41.716],[23.009,41.74],[22.991,41.761],[22.946,41.769],[22.918,41.814],[22.901,41.86],[22.881,41.873],[22.855,41.983],[22.838,42.019],[22.821,42.025],[22.799,42.021],[22.781,42.043],[22.718,42.044],[22.706,42.056],[22.676,42.061],[22.618,42.083],[22.531,42.129],[22.495,42.165],[22.481,42.193],[22.444,42.214],[22.345,42.313],[22.364,42.321],[22.424,42.326],[22.438,42.34],[22.454,42.377],[22.47,42.392],[22.509,42.405],[22.533,42.458],[22.537,42.478],[22.525,42.508],[22.425,42.573],[22.449,42.668],[22.442,42.682],[22.483,42.734],[22.453,42.764],[22.427,42.814],[22.445,42.83],[22.481,42.847],[22.506,42.87],[22.538,42.868],[22.564,42.884],[22.591,42.887],[22.666,42.872],[22.727,42.887],[22.739,42.897],[22.776,42.98],[22.829,42.994],[22.884,43.037],[22.902,43.07],[22.935,43.086],[22.956,43.108],[22.985,43.175],[22.981,43.199],[22.898,43.22],[22.827,43.281],[22.817,43.315],[22.805,43.329],[22.733,43.382],[22.703,43.394],[22.665,43.397],[22.638,43.426],[22.596,43.429],[22.566,43.453],[22.519,43.474],[22.478,43.559],[22.483,43.579],[22.477,43.591],[22.482,43.599],[22.466,43.649],[22.426,43.668],[22.405,43.687],[22.386,43.725],[22.389,43.758],[22.363,43.781],[22.349,43.808],[22.377,43.884],[22.379,43.913],[22.392,43.932],[22.4,43.993],[22.412,44.007],[22.504,44.02],[22.534,44.057],[22.593,44.064],[22.605,44.079],[22.597,44.119],[22.609,44.16],[22.606,44.175],[22.649,44.214],[22.692,44.228],[22.906,44.123],[23.031,44.093],[23.04,44.062],[23.023,44.032],[22.988,44.018],[22.906,44.004],[22.886,43.995],[22.851,43.897],[22.851,43.874],[22.863,43.855],[22.889,43.84],[22.92,43.834],[23.132,43.848],[23.234,43.877],[23.325,43.887],[23.485,43.881],[23.593,43.837],[23.636,43.832],[23.721,43.846],[23.743,43.843],[23.8,43.818],[24.159,43.753],[24.358,43.76],[24.431,43.794],[24.466,43.802],[24.5,43.799],[24.706,43.744],[24.753,43.739],[24.964,43.75],[25.082,43.719],[25.252,43.705],[25.36,43.654],[25.403,43.65],[25.467,43.668],[25.557,43.67],[25.617,43.688],[25.671,43.717],[25.74,43.719],[25.781,43.732],[25.806,43.764],[25.839,43.788],[25.869,43.801],[25.916,43.844],[25.934,43.87],[26.054,43.934],[26.079,43.969],[26.116,43.999],[26.151,44.012],[26.231,44.027],[26.311,44.053],[26.614,44.085],[26.709,44.108],[26.754,44.108],[26.789,44.116],[26.884,44.157],[27.002,44.165],[27.027,44.177],[27.1,44.144],[27.206,44.129],[27.227,44.121],[27.251,44.122],[27.269,44.112],[27.264,44.09],[27.285,44.072],[27.342,44.053],[27.384,44.015],[27.575,44.016],[27.633,44.03],[27.656,44.024],[27.676,43.994],[27.722,43.949],[27.787,43.96],[27.856,43.989],[27.912,43.993],[27.936,43.964],[27.981,43.849],[28.015,43.83],[28.221,43.762],[28.435,43.735],[28.578,43.741],[28.573,43.606],[28.576,43.593],[28.603,43.553],[28.604,43.538],[28.56,43.454],[28.489,43.406],[28.474,43.384],[28.473,43.367],[28.459,43.381],[28.415,43.399],[28.394,43.414],[28.322,43.428],[28.243,43.408],[28.157,43.408],[28.119,43.392],[28.092,43.364],[28.018,43.233],[28.0,43.223],[27.904,43.202],[27.904,43.196],[27.946,43.169],[27.911,43.065],[27.884,43.031],[27.904,42.942],[27.898,42.875],[27.904,42.86],[27.884,42.848],[27.897,42.784],[27.892,42.711],[27.733,42.715],[27.719,42.695],[27.717,42.675],[27.74,42.661],[27.647,42.641],[27.628,42.629],[27.63,42.603],[27.65,42.558],[27.634,42.564],[27.541,42.565],[27.511,42.553],[27.48,42.483],[27.462,42.49],[27.453,42.48],[27.453,42.465],[27.466,42.456],[27.461,42.444],[27.466,42.428],[27.473,42.462],[27.514,42.435],[27.544,42.46],[27.562,42.448],[27.571,42.458],[27.596,42.448],[27.629,42.459],[27.643,42.456],[27.636,42.448],[27.652,42.419],[27.668,42.416],[27.692,42.428],[27.699,42.414],[27.719,42.415],[27.719,42.407],[27.698,42.4],[27.705,42.391],[27.719,42.387],[27.709,42.377],[27.714,42.349],[27.74,42.334],[27.78,42.339],[27.774,42.322],[27.788,42.311],[27.763,42.296],[27.751,42.277],[27.756,42.258],[27.78,42.243],[27.774,42.236],[27.81,42.218],[27.831,42.195],[27.856,42.181],[27.849,42.167],[27.879,42.154],[27.904,42.12],[27.958,42.094],[27.973,42.075],[27.987,42.072],[27.982,42.061],[28.007,42.038],[28.0,42.03],[28.019,42.008],[28.017,41.973],[27.966,41.982],[27.917,41.978],[27.852,41.995],[27.812,41.995],[27.803,41.96],[27.818,41.953],[27.815,41.947],[27.79,41.943],[27.724,41.968],[27.687,41.969],[27.609,41.953],[27.603,41.939],[27.591,41.943],[27.572,41.93],[27.551,41.924],[27.561,41.918],[27.549,41.911],[27.563,41.906],[27.546,41.901],[27.494,41.943],[27.397,41.989],[27.332,42.057],[27.273,42.092],[27.216,42.096],[27.174,42.057],[27.116,42.062],[27.084,42.078],[27.047,42.083],[27.023,42.074],[27.0,42.043],[26.967,42.028],[26.939,41.996],[26.911,41.997],[26.89,41.985],[26.861,41.988],[26.819,41.966],[26.781,41.983],[26.737,41.959],[26.606,41.967],[26.543,41.92],[26.56,41.907],[26.559,41.902],[26.548,41.856],[26.526,41.824],[26.478,41.813],[26.376,41.817],[26.334,41.79],[26.32,41.765],[26.316,41.744],[26.333,41.713]]

LOG_PATH = os.path.join(os.path.expanduser("~"), "bg_vreme_log.txt")


def log(msg):
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(datetime.now().strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")
    except Exception:
        pass


# --------------------------------------------------------------------------
#  ЗАРЕЖДАНЕ НА ДАННИ
# --------------------------------------------------------------------------
def http_json(url):
    req = urllib.request.Request(url, headers={"User-Agent": "BG-Weather-Map/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", "replace")[:200]
        except Exception:
            body = ""
        raise RuntimeError("HTTP %s %s" % (e.code, body))


def as_list(x):
    return x if isinstance(x, list) else [x]


def fill_missing(vals, default):
    good = [v for v in vals if v is not None]
    rep = (sum(good) / len(good)) if good else default
    return [rep if v is None else float(v) for v in vals]


def smooth3(A):
    ny, nx = len(A), len(A[0])
    out = [[0.0] * nx for _ in range(ny)]
    for j in range(ny):
        for i in range(nx):
            s = 0.0
            n = 0
            for dj in (-1, 0, 1):
                for di in (-1, 0, 1):
                    jj, ii = j + dj, i + di
                    if 0 <= jj < ny and 0 <= ii < nx:
                        s += A[jj][ii]
                        n += 1
            out[j][i] = s / n
    return out


def advection(T, WS, WD):
    """Температурна адвекция в K/час. Отрицателна = студен въздух напредва
    (студен фронт), положителна = топъл въздух напредва (топъл фронт)."""
    ny, nx = len(GRID_LATS), len(GRID_LONS)
    A = [[0.0] * nx for _ in range(ny)]
    for j in range(ny):
        for i in range(nx):
            i0, i1 = max(i - 1, 0), min(i + 1, nx - 1)
            j0, j1 = max(j - 1, 0), min(j + 1, ny - 1)
            dx = (GRID_LONS[i1] - GRID_LONS[i0]) * 111320.0 * math.cos(math.radians(GRID_LATS[j]))
            dy = (GRID_LATS[j1] - GRID_LATS[j0]) * 110540.0
            dTdx = (T[j][i1] - T[j][i0]) / dx
            dTdy = (T[j1][i] - T[j0][i]) / dy
            ang = math.radians(WD[j][i])
            u = -WS[j][i] * math.sin(ang)   # посоката е "откъде духа"
            v = -WS[j][i] * math.cos(ang)
            A[j][i] = -(u * dTdx + v * dTdy) * 3600.0
    return smooth3(A)


def load_all():
    base = "https://api.open-meteo.com/v1/forecast"

    # 1) температури в градовете
    q = {
        "latitude": ",".join("%.2f" % c[1] for c in CITIES),
        "longitude": ",".join("%.2f" % c[2] for c in CITIES),
        "hourly": "temperature_2m",
        "timezone": "Europe/Sofia",
        "forecast_days": 6,
    }
    cres = as_list(http_json(base + "?" + urllib.parse.urlencode(q)))
    if len(cres) != len(CITIES):
        raise RuntimeError("Неочакван брой градове в отговора")

    off = cres[0].get("utc_offset_seconds", 7200)
    now = datetime.now(timezone.utc).replace(tzinfo=None) + timedelta(seconds=off)
    now_h = now.replace(minute=0, second=0, microsecond=0)
    times = cres[0]["hourly"]["time"]
    key = now_h.strftime("%Y-%m-%dT%H:00")
    if key not in times:
        raise RuntimeError("Няма данни за текущия час")
    idx = times.index(key)
    if idx + max(OFFSETS) >= len(times):
        raise RuntimeError("Прогнозата е твърде кратка")

    city_temps = []
    for r in cres:
        arr = r["hourly"]["temperature_2m"]
        city_temps.append([arr[idx + o] for o in OFFSETS])

    # 2) мрежа за фронтовете (850 hPa ≈ 1,5 км височина)
    lats, lons = [], []
    for la in GRID_LATS:
        for lo in GRID_LONS:
            lats.append("%.2f" % la)
            lons.append("%.2f" % lo)
    q = {
        "latitude": ",".join(lats),
        "longitude": ",".join(lons),
        "hourly": "temperature_850hPa,wind_speed_850hPa,wind_direction_850hPa",
        "wind_speed_unit": "ms",
        "timezone": "Europe/Sofia",
        "forecast_days": 6,
    }
    gres = as_list(http_json(base + "?" + urllib.parse.urlencode(q)))
    ny, nx = len(GRID_LATS), len(GRID_LONS)
    if len(gres) != ny * nx:
        raise RuntimeError("Неочакван брой точки в мрежата")
    gtimes = gres[0]["hourly"]["time"]
    if key not in gtimes:
        raise RuntimeError("Няма данни за мрежата в текущия час")
    gidx = gtimes.index(key)

    adv = []
    for o in OFFSETS:
        h = gidx + o
        Tv = fill_missing([r["hourly"]["temperature_850hPa"][h] for r in gres], 0.0)
        Sv = fill_missing([r["hourly"]["wind_speed_850hPa"][h] for r in gres], 0.0)
        Dv = fill_missing([r["hourly"]["wind_direction_850hPa"][h] for r in gres], 0.0)
        T = [Tv[j * nx:(j + 1) * nx] for j in range(ny)]
        S = [Sv[j * nx:(j + 1) * nx] for j in range(ny)]
        D = [Dv[j * nx:(j + 1) * nx] for j in range(ny)]
        adv.append(advection(T, S, D))

    return {
        "city_temps": city_temps,
        "adv": adv,
        "valid": [now_h + timedelta(hours=o) for o in OFFSETS],
        "updated": now,
    }


# --------------------------------------------------------------------------
#  ПОМОЩНИ ФУНКЦИИ ЗА ПОКАЗВАНЕ
# --------------------------------------------------------------------------
def frame_label(h):
    if h == 0:
        return "Сега"
    return "След %d %s" % (h, "час" if h == 1 else "часа")


def fmt_temp(t):
    if t is None:
        return "–"
    return "%d°" % int(round(t))


def temp_color(t):
    if t is None:
        return "#444444"
    if t <= 0:
        return "#0A4A9E"
    if t >= 25:
        return "#B3261E"
    return "#1B1B1B"


# --------------------------------------------------------------------------
#  ПРОЗОРЕЦ
# --------------------------------------------------------------------------
class App:
    def __init__(self, root):
        self.root = root
        root.title("Времето в България")
        root.geometry("1150x780")
        root.minsize(640, 480)

        # плъзгач долу (ръчно управление на часа напред)
        bar = tk.Frame(root, bg="#D5DBE1")
        bar.pack(side="bottom", fill="x")
        tk.Label(bar, text="Часове напред:", bg="#D5DBE1",
                 font=("DejaVu Sans", 11, "bold")).pack(side="left", padx=(12, 6), pady=6)
        self.slider = tk.Scale(bar, from_=0, to=max(OFFSETS), orient="horizontal",
                               resolution=1, showvalue=True, length=400,
                               bg="#D5DBE1", highlightthickness=0, troughcolor="#FFFFFF",
                               font=("DejaVu Sans", 10), command=self.on_slide)
        self.slider.pack(side="left", fill="x", expand=True, padx=(0, 14), pady=4)

        self.canvas = tk.Canvas(root, bg=C_OUT, highlightthickness=0)
        self.canvas.pack(side="top", fill="both", expand=True)

        self.W = 0
        self.H = 0
        self.data = None
        self.cache = {}
        self.frame = 0
        self.result = None
        self.fetching = False
        self.warn = ""
        self.message = "Зареждане на данните…"
        self.resize_job = None
        self.city_items = []
        self.title_item = None
        self.sub_item = None
        self.bg_item = None

        self.cosphi = math.cos(math.radians(42.7))
        self.k = 1.0
        self.offx = 0.0
        self.offy = 0.0

        self.canvas.bind("<Configure>", self.on_configure)
        self.start_fetch()
        self.root.after(300, self.poll)

    # ---------- мрежа ----------
    def start_fetch(self):
        if self.fetching:
            return
        self.fetching = True
        threading.Thread(target=self._worker, daemon=True).start()

    def _worker(self):
        try:
            self.result = ("ok", load_all())
        except Exception as e:  # noqa: BLE001
            log("Грешка при зареждане: " + traceback.format_exc())
            self.result = ("err", str(e))

    def poll(self):
        try:
            if self.result is not None:
                kind, val = self.result
                self.result = None
                self.fetching = False
                if kind == "ok":
                    self.data = val
                    self.warn = ""
                    self.message = ""
                    self.relayout()
                    self.root.after(REFRESH_MS, self.start_fetch)
                else:
                    if self.data is None:
                        self.message = ("Няма връзка с данните. Проверете интернета.\n"
                                        "Опитвам отново след 30 секунди…\n\n(" + val[:120] + ")")
                    else:
                        self.warn = "Няма връзка – показани са последните налични данни."
                    self.relayout()
                    self.root.after(RETRY_MS, self.start_fetch)
        except Exception:  # noqa: BLE001
            log("Грешка в poll: " + traceback.format_exc())
        finally:
            self.root.after(300, self.poll)

    # ---------- размер ----------
    def on_configure(self, e):
        if e.width < 100 or e.height < 100:
            return
        if (e.width, e.height) == (self.W, self.H):
            return
        self.W, self.H = e.width, e.height
        if self.resize_job is not None:
            self.root.after_cancel(self.resize_job)
        self.resize_job = self.root.after(200, self.relayout)

    # ---------- проекция ----------
    def setup_projection(self):
        lonr = LON1 - LON0
        latr = LAT1 - LAT0
        self.k = min(self.W / (lonr * self.cosphi), self.H / latr)
        self.offx = (self.W - lonr * self.cosphi * self.k) / 2.0
        self.offy = (self.H - latr * self.k) / 2.0

    def px(self, lon, lat):
        return (self.offx + (lon - LON0) * self.cosphi * self.k,
                self.offy + (LAT1 - lat) * self.k)

    # ---------- оцветяване ----------
    def build_images(self):
        s = CELL
        cw = self.W // s + 1
        ch = self.H // s + 1
        pts = [self.px(lo, la) for lo, la in RING]
        edges = []
        for a, b in zip(pts, pts[1:] + pts[:1]):
            if a[1] != b[1]:
                edges.append((a[0], a[1], b[0], b[1]))

        nx, ny = len(GRID_LONS), len(GRID_LATS)
        dlon = GRID_LONS[1] - GRID_LONS[0]
        dlat = GRID_LATS[1] - GRID_LATS[0]
        cells = []
        for r in range(ch):
            y = (r + 0.5) * s
            xs = []
            for x1, y1, x2, y2 in edges:
                if (y1 <= y < y2) or (y2 <= y < y1):
                    xs.append(x1 + (y - y1) * (x2 - x1) / (y2 - y1))
            xs.sort()
            lat = LAT1 - (y - self.offy) / self.k
            fj = (lat - GRID_LATS[0]) / dlat
            fj = min(max(fj, 0.0), ny - 1.0001)
            j0 = int(fj)
            fy = fj - j0
            for n in range(0, len(xs) - 1, 2):
                c0 = int(math.ceil(xs[n] / s - 0.5))
                c1 = int(math.floor(xs[n + 1] / s - 0.5))
                for c in range(max(c0, 0), min(c1, cw - 1) + 1):
                    lon = LON0 + ((c + 0.5) * s - self.offx) / (self.cosphi * self.k)
                    fi = (lon - GRID_LONS[0]) / dlon
                    fi = min(max(fi, 0.0), nx - 1.0001)
                    i0 = int(fi)
                    cells.append((r, c, i0, fi - i0, j0, fy))

        self.cells = cells
        self.cw, self.ch = cw, ch
        self.cache = {}
        self.border_pts = pts

    def get_image(self, k):
        """Картинката за k часа напред (прави се при нужда и се пази в кеш)."""
        if k in self.cache:
            return self.cache[k]
        s = CELL
        cw, ch = self.cw, self.ch
        rows = [[C_OUT] * cw for _ in range(ch)]
        if self.data:
            A = self.data["adv"][k]
            for r, c, i0, fx, j0, fy in self.cells:
                v = ((A[j0][i0] * (1 - fx) + A[j0][i0 + 1] * fx) * (1 - fy)
                     + (A[j0 + 1][i0] * (1 - fx) + A[j0 + 1][i0 + 1] * fx) * fy)
                rows[r][c] = C_WARM if v > FRONT_TH else (C_COLD if v < -FRONT_TH else C_LAND)
        else:
            for r, c, *_ in self.cells:
                rows[r][c] = C_LAND
        small = tk.PhotoImage(width=cw, height=ch)
        small.put(" ".join("{" + " ".join(row) + "}" for row in rows))
        big = small.zoom(s, s)
        if len(self.cache) >= 12:
            self.cache.pop(next(iter(self.cache)))
        self.cache[k] = big
        return big

    # ---------- рисуване ----------
    def relayout(self):
        self.resize_job = None
        if self.W < 100 or self.H < 100:
            return
        try:
            c = self.canvas
            c.delete("all")
            self.setup_projection()
            self.build_images()
            self.bg_item = c.create_image(0, 0, image=self.get_image(self.frame if self.data else 0), anchor="nw")

            flat = []
            for x, y in self.border_pts:
                flat += [x, y]
            c.create_line(*flat, fill=C_BORDER, width=2, joinstyle="round")

            fam = "DejaVu Sans"
            name_sz = max(7, int(self.k / 21))
            temp_sz = name_sz + 3
            f_name = (fam, name_sz)
            f_temp = (fam, temp_sz, "bold")
            lh_temp = tkfont.Font(family=fam, size=temp_sz, weight="bold").metrics("linespace")

            # надпис "Черно море"
            sx, sy = self.px(28.55, 43.0)
            c.create_text(sx, sy, text="Черно\nморе", fill="#7C93AB",
                          font=(fam, name_sz + 1, "italic"), justify="center")

            self.city_items = []
            if self.data:
                for n, (name, lat, lon) in enumerate(CITIES):
                    x, y = self.px(lon, lat)
                    c.create_oval(x - 3, y - 3, x + 3, y + 3, fill="#2B2B2B", outline="#FFFFFF")
                    t_item = c.create_text(x, y - 5, text="", anchor="s", font=f_temp)
                    c.create_text(x, y - 5 - lh_temp + 2, text=name, anchor="s",
                                  font=f_name, fill="#33404A")
                    self.city_items.append(t_item)

            # заглавие горе вляво
            self.title_item = c.create_text(18, 12, anchor="nw", text="",
                                            font=(fam, 28, "bold"), fill="#16212B")
            self.sub_item = c.create_text(20, 58, anchor="nw", text="",
                                          font=(fam, 12), fill="#33404A")

            # легенда долу вдясно
            x0 = self.W - 14 - 235
            fnt = (fam, 10)
            for n, (col, edge, txt) in enumerate((
                    (C_WARM, "#AA9999", "Топъл фронт (затопляне)"),
                    (C_COLD, "#8899AA", "Студен фронт (захлаждане)"))):
                yy = self.H - 48 + n * 24
                c.create_rectangle(x0, yy, x0 + 18, yy + 14, fill=col, outline=edge)
                c.create_text(x0 + 26, yy + 7, anchor="w", text=txt, font=fnt, fill="#222")

            # бележка долу вляво
            note = "Данни: Open-Meteo.  Фронтовете са приблизителни – изчислени от температурна адвекция на 850 hPa."
            if self.data:
                note += "\nОбновено в %s ч." % self.data["updated"].strftime("%H:%M")
            c.create_text(12, self.H - 10, anchor="sw", text=note, font=(fam, 9), fill="#55616B")
            if self.warn:
                c.create_text(12, self.H - 52, anchor="sw", text=self.warn,
                              font=(fam, 10, "bold"), fill="#B3261E")

            if self.message and not self.data:
                c.create_text(self.W / 2, self.H / 2, text=self.message, justify="center",
                              font=(fam, 14), fill="#33404A")

            self.show_frame(self.frame)
        except Exception:  # noqa: BLE001
            log("Грешка в relayout: " + traceback.format_exc())

    def on_slide(self, value):
        try:
            self.frame = int(float(value))
            self.show_frame(self.frame)
        except Exception:  # noqa: BLE001
            log("Грешка в on_slide: " + traceback.format_exc())

    def show_frame(self, i):
        if not self.data or self.bg_item is None:
            return
        c = self.canvas
        c.itemconfigure(self.bg_item, image=self.get_image(i))
        for n, item in enumerate(self.city_items):
            t = self.data["city_temps"][n][i]
            c.itemconfigure(item, text=fmt_temp(t), fill=temp_color(t))
        v = self.data["valid"][i]
        c.itemconfigure(self.title_item, text=frame_label(i))
        c.itemconfigure(self.sub_item, text="%s, %02d.%02d.  %02d:00 ч." % (
            WEEKDAYS[v.weekday()], v.day, v.month, v.hour))


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
