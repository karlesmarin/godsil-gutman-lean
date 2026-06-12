"""Weight-2 paper, figure 1: the real dilogarithm with its machine-checked values.

Li2 drawn from the defining series (mpmath polylog); the four special values proven in
Dilog/Basic.lean are ASSERTED against high-precision numerics before drawing:
  Li2(1/2)      = pi^2/12 - log^2(2)/2          (Euler; reflection at the fixed point)
  Li2(1/phi)    = pi^2/10 - log^2(phi)          (Landen; the golden ladder)
  Li2(1/phi^2)  = pi^2/15 - log^2(phi)
  Li2(-1/phi)   = log^2(phi)/2 - pi^2/15
"""
from fig_style import COL, setup, save
import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf, polylog, log, pi, sqrt

mp.dps = 40
phi = (1 + sqrt(5)) / 2

# --- machine-checked values, asserted against the series ---------------------
special = [
    (float(1 / phi**2), float(pi**2 / 15 - log(phi)**2),
     r"$\mathrm{Li}_2(1/\varphi^2)=\frac{\pi^2}{15}-\ln^2\varphi$"),
    (0.5, float(pi**2 / 12 - log(2)**2 / 2),
     r"$\mathrm{Li}_2(\frac{1}{2})=\frac{\pi^2}{12}-\frac{\ln^2 2}{2}$"),
    (float(1 / phi), float(pi**2 / 10 - log(phi)**2),
     r"$\mathrm{Li}_2(1/\varphi)=\frac{\pi^2}{10}-\ln^2\varphi$"),
    (float(-1 / phi), float(log(phi)**2 / 2 - pi**2 / 15),
     r"$\mathrm{Li}_2(-1/\varphi)=\frac{\ln^2\varphi}{2}-\frac{\pi^2}{15}$"),
]
for x, v, _ in special:
    assert abs(float(polylog(2, mpf(x))) - v) < 1e-12, (x, v)
assert abs(float(polylog(2, mpf(1))) - float(pi**2 / 6)) < 1e-12   # Basel
assert abs(float(polylog(2, mpf(-1))) + float(pi**2 / 12)) < 1e-12  # eta(2)

# --- draw --------------------------------------------------------------------
setup()
fig, ax = plt.subplots(figsize=(6.4, 4.0))
xs = np.linspace(-1, 1, 600)
ys = [float(polylog(2, mpf(float(t)))) for t in xs]
ax.plot(xs, ys, color=COL["pos"], lw=2.0, zorder=3)
ax.axhline(0, color=COL["grey"], lw=0.6)
ax.axvline(0, color=COL["grey"], lw=0.6)

offsets = [(-0.04, 0.34), (-0.30, 0.62), (0.045, -0.22), (0.06, -0.10)]
for (x, v, lab), (dx, dy) in zip(special, offsets):
    ax.plot([x], [v], "o", color=COL["accent"], ms=6, zorder=4)
    ax.annotate(lab, (x, v), xytext=(x + dx, v + dy), fontsize=9,
                arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))
ax.plot([1], [float(pi**2 / 6)], "s", color=COL["neg"], ms=6, zorder=4)
ax.annotate(r"$\mathrm{Li}_2(1)=\frac{\pi^2}{6}$", (1, float(pi**2 / 6)),
            xytext=(0.52, 1.62), fontsize=9,
            arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))

ax.set_xlabel(r"$x$")
ax.set_ylabel(r"$\mathrm{Li}_2(x)$")
ax.set_xlim(-1.05, 1.13)
ax.set_title("The real dilogarithm and its machine-checked special values", fontsize=11)
save(fig, "dilog_fig1_golden")
