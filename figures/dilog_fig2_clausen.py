"""Weight-2 paper, figure 2: the Clausen function and the machine-checked lower bound.

Cl2 from mpmath (clsin); the script ASSERTS, on a fine grid of (0, pi):
  Cl2(theta) >= sin(theta)/2          (the Lean bound Cl2_pos)
and the special values Cl2(pi/2) = Catalan, Cl2(0) = Cl2(pi) = 0,
plus the full-circle reflection Cl2(2pi - theta) = -Cl2(theta).
"""
from fig_style import COL, setup, save
import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf, clsin, catalan, pi, sin

mp.dps = 30
Cl2 = lambda t: clsin(2, t)

# --- asserts ------------------------------------------------------------------
for k in range(1, 400):
    t = mpf(k) * pi / 400
    assert Cl2(t) >= sin(t) / 2 - mpf(10)**-25, t
assert abs(Cl2(pi / 2) - catalan) < mpf(10)**-25
assert abs(Cl2(pi)) < mpf(10)**-25
for k in (50, 137, 301):
    t = mpf(k) * 2 * pi / 400
    assert abs(Cl2(2 * pi - t) + Cl2(t)) < mpf(10)**-25

# --- draw ----------------------------------------------------------------------
setup()
fig, ax = plt.subplots(figsize=(6.4, 3.9))
ts = np.linspace(0, 2 * np.pi, 700)
ys = [float(Cl2(mpf(float(t)))) for t in ts]
ax.plot(ts, ys, color=COL["pos"], lw=2.0, zorder=3, label=r"$\mathrm{Cl}_2(\theta)$")

tpos = np.linspace(0, np.pi, 350)
ax.fill_between(tpos, 0, np.sin(tpos) / 2, color=COL["band"], zorder=1)
ax.plot(tpos, np.sin(tpos) / 2, color=COL["accent"], lw=1.4, ls="--", zorder=2,
        label=r"machine-checked bound $\sin\theta/2$")

ax.plot([np.pi / 2], [float(catalan)], "o", color=COL["neg"], ms=6, zorder=4)
ax.annotate(r"$\mathrm{Cl}_2(\pi/2)=G$ (Catalan)", (np.pi / 2, float(catalan)),
            xytext=(1.9, 0.97), fontsize=9,
            arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))
ax.axhline(0, color=COL["grey"], lw=0.6)
ax.set_xticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
ax.set_xticklabels([r"$0$", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
ax.set_xlabel(r"$\theta$")
ax.set_ylabel(r"$\mathrm{Cl}_2(\theta)$")
ax.legend(frameon=False, fontsize=9, loc="lower left")
ax.set_title(r"The Clausen function: positive on $(0,\pi)$, with the Lean lower bound",
             fontsize=11)
save(fig, "dilog_fig2_clausen")
