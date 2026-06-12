"""Weight-2 paper, figure 3: the clock that never ticks.

|S(theta)| for two quantum states with equally spaced levels E_n = n:
  zeta state  p_n = (6/pi^2)/n^2 : |S| = (6/pi^2)|Li2(e^{-i theta})|  -- never 0
  ML-sharp    p_0 = p_1 = 1/2    : |S| = |cos(theta/2)|               -- hits 0 at pi
ASSERTS: min over the grid of |Li2| equals pi^2/12 at theta = pi (eta(2)), bounded
away from zero; the two-level state hits zero at pi (Enestrom--Kakeya equality case).
"""
from fig_style import COL, setup, save
import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf, polylog, exp, pi, cos

mp.dps = 25

# --- asserts -------------------------------------------------------------------
vals = [(k, abs(polylog(2, exp(-1j * mpf(k) * 2 * pi / 720)))) for k in range(1, 720)]
kmin, vmin = min(vals, key=lambda kv: kv[1])
assert kmin == 360                                   # the minimum sits at theta = pi
assert abs(vmin - pi**2 / 12) < mpf(10)**-20         # and equals eta(2) = pi^2/12
assert abs(cos(pi / 2)) < mpf(10)**-20               # two-level state: S(pi) = 0

# --- draw ------------------------------------------------------------------------
setup()
fig, ax = plt.subplots(figsize=(6.4, 3.9))
ts = np.linspace(0.001, 2 * np.pi - 0.001, 700)
zeta = [float((6 / pi**2) * abs(polylog(2, exp(-1j * mpf(float(t)))))) for t in ts]
two = np.abs(np.cos(ts / 2))
ax.plot(ts, zeta, color=COL["pos"], lw=2.0, zorder=3,
        label=r"zeta state $p_n\propto 1/n^2$:  $\frac{6}{\pi^2}|\mathrm{Li}_2(e^{-i\theta})|$")
ax.plot(ts, two, color=COL["neg"], lw=1.6, ls="--", zorder=2,
        label=r"two-level state $\frac{|0\rangle+|2E\rangle}{\sqrt{2}}$:  $|\cos(\theta/2)|$")
ax.axhline(float(6 / pi**2 * (pi**2 / 12)), color=COL["accent"], lw=1.0, ls=":",
           zorder=1)
ax.annotate(r"floor $=\frac{6}{\pi^2}\cdot\frac{\pi^2}{12}=\frac{1}{2}$  (never orthogonal)",
            (np.pi, 0.5), xytext=(3.5, 0.585), fontsize=9,
            arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))
ax.annotate(r"orthogonal: ML bound saturated", (np.pi, 0.0), xytext=(3.6, 0.12),
            fontsize=9, arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))
ax.set_xticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
ax.set_xticklabels([r"$0$", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
ax.set_xlabel(r"$\theta = $ time (units $\hbar/E$-spacing)")
ax.set_ylabel(r"$|S(\theta)| = |\langle\psi_0|\psi_\theta\rangle|$")
ax.set_ylim(-0.05, 1.05)
ax.legend(frameon=False, fontsize=9, loc="upper right")
ax.set_title("The clock that never ticks: two states, same level spacing", fontsize=11)
save(fig, "dilog_fig3_clock")
