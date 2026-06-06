"""Figure 4 — what the Ihara zeta counts: prime (non-backtracking) cycles, whose Euler product
has reciprocal the finite determinant det(I - uB)."""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()

# house graph: square 0-1-2-3 + roof triangle 2-3-4
pos = {0: (-0.8, -0.9), 1: (0.8, -0.9), 2: (0.8, 0.4), 3: (-0.8, 0.4), 4: (0.0, 1.3)}
edges = [(0, 1), (1, 2), (2, 3), (3, 0), (2, 4), (3, 4)]
tri = [(2, 3), (3, 4), (4, 2)]      # prime cycle of length 3
sq = [(0, 1), (1, 2), (2, 3), (3, 0)]  # prime cycle of length 4

fig = plt.figure(figsize=(9.4, 4.2))
gs = fig.add_gridspec(1, 2, width_ratios=[1.0, 1.35], wspace=0.05)

ax = fig.add_subplot(gs[0, 0])
for (i, j) in edges:
    (x0, y0), (x1, y1) = pos[i], pos[j]
    ax.plot([x0, x1], [y0, y1], color=COL['grey'], lw=1.6, zorder=1)
def cycle(ax, cyc, color, lw, rad=0):
    for (i, j) in cyc:
        (x0, y0), (x1, y1) = pos[i], pos[j]
        ax.plot([x0, x1], [y0, y1], color=color, lw=lw, zorder=2, solid_capstyle='round')
cycle(ax, tri, COL['pos'], 3.4)
cycle(ax, sq, COL['accent'], 3.0)
for v, (px, py) in pos.items():
    ax.scatter([px], [py], s=210, color=COL['node'], zorder=3, edgecolors='white', linewidths=1.4)
ax.text(0.0, 0.92, r"$\ell=3$", color=COL['pos'], fontsize=10, ha='center', zorder=4)
ax.text(0.0, -0.62, r"$\ell=4$", color=COL['accent'], fontsize=10, ha='center', zorder=4)
ax.set_xlim(-1.4, 1.4); ax.set_ylim(-1.4, 1.7); ax.set_aspect('equal'); ax.axis('off')
ax.set_title("two prime cycles\n(closed, non-backtracking, not a power)", fontsize=9.6)

axr = fig.add_subplot(gs[0, 1]); axr.axis('off')
axr.add_patch(plt.Rectangle((0.03, 0.30), 0.94, 0.52, transform=axr.transAxes,
              facecolor=COL['band'], edgecolor=COL['pos'], lw=1.3, zorder=0))
axr.text(0.5, 0.71, r"$\zeta_G(u)=\prod_{[C]\ \mathrm{prime}}\dfrac{1}{1-u^{\ell(C)}}$",
         ha='center', va='center', fontsize=13)
axr.text(0.5, 0.50, r"$\zeta_G(u)^{-1}=\det(I-uB)$", ha='center', va='center', fontsize=13)
axr.text(0.5, 0.355, "infinite Euler product   =   finite determinant", ha='center', va='center',
         fontsize=8.6, color=COL['grey'])
axr.text(0.5, 0.13, "the object Bass's formula computes (this paper)", ha='center', va='center',
         fontsize=8.4, color=COL['node'])

fig.suptitle(r"The Ihara zeta counts prime non-backtracking cycles; its reciprocal is $\det(I-uB)$",
             fontsize=11.3, y=1.0)
save(fig, "bass_fig4_primecycles")
