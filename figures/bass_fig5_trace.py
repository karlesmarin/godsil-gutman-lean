"""Figure 5 — the two sides of one trace formula: tr(A^k) splits into a tree/matching (Plancherel)
part p_k and a non-backtracking/cycle (Ihara) part N_k, the same band governing both."""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from fig_style import setup, save, COL
setup()

fig = plt.figure(figsize=(9.6, 4.0))
gs = fig.add_gridspec(1, 2, width_ratios=[1, 1], wspace=0.12)

# --- left: tree side (matching polynomial / Plancherel) ---
axl = fig.add_subplot(gs[0, 0])
# a small rooted tree (universal cover fragment)
tpos = {0: (0, 1.1), 1: (-0.7, 0.3), 2: (0.7, 0.3),
        3: (-1.05, -0.5), 4: (-0.35, -0.5), 5: (0.35, -0.5), 6: (1.05, -0.5)}
tedges = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)]
for (i, j) in tedges:
    (x0, y0), (x1, y1) = tpos[i], tpos[j]
    axl.plot([x0, x1], [y0, y1], color=COL['lyr1'], lw=2.0, zorder=1)
# a tree-like back-and-forth walk 0->1->0 (Plancherel: returns on the tree)
a = FancyArrowPatch(tpos[0], tpos[1], connectionstyle="arc3,rad=0.25", arrowstyle='-|>',
                    mutation_scale=12, lw=2.4, color=COL['pos'], zorder=2, shrinkA=10, shrinkB=10)
axl.add_patch(a)
a2 = FancyArrowPatch(tpos[1], tpos[0], connectionstyle="arc3,rad=0.25", arrowstyle='-|>',
                     mutation_scale=12, lw=2.4, color=COL['pos'], zorder=2, shrinkA=10, shrinkB=10)
axl.add_patch(a2)
for v, (px, py) in tpos.items():
    axl.scatter([px], [py], s=150, color=COL['node'], zorder=3, edgecolors='white', linewidths=1.2)
axl.set_xlim(-1.45, 1.45); axl.set_ylim(-0.95, 1.45); axl.set_aspect('equal'); axl.axis('off')
axl.set_title(r"tree / Plancherel side: $p_k$"
              "\n" r"matching polynomial $\mu_G$  (Papers I, II)", fontsize=9.6)

# --- right: cycle side (non-backtracking / Ihara) ---
axr = fig.add_subplot(gs[0, 1])
th = np.linspace(0, 2 * np.pi, 6, endpoint=False) + np.pi / 2
cx, cy = np.cos(th), np.sin(th)
for k in range(5):
    axr.plot([cx[k], cx[k + 1]], [cy[k], cy[k + 1]], color=COL['lyr1'], lw=2.0, zorder=1)
axr.plot([cx[5], cx[0]], [cy[5], cy[0]], color=COL['lyr1'], lw=2.0, zorder=1)
# a non-backtracking closed walk around the cycle
for k in range(6):
    p, q = (cx[k], cy[k]), (cx[(k + 1) % 6], cy[(k + 1) % 6])
    a = FancyArrowPatch(p, q, connectionstyle="arc3,rad=0.14", arrowstyle='-|>',
                        mutation_scale=11, lw=2.2, color=COL['neg'], zorder=2, shrinkA=9, shrinkB=9)
    axr.add_patch(a)
for k in range(6):
    axr.scatter([cx[k]], [cy[k]], s=150, color=COL['node'], zorder=3, edgecolors='white', linewidths=1.2)
axr.set_xlim(-1.5, 1.5); axr.set_ylim(-1.5, 1.5); axr.set_aspect('equal'); axr.axis('off')
axr.set_title(r"cycle / $\pi_1$ side: $N_k$"
              "\n" r"non-backtracking $\det(I-uB)$  (this paper)", fontsize=9.6)

# center banner: the trace formula
fig.text(0.5, 0.97, r"$\operatorname{tr}(A^k)\;=\;p_k\;+\;N_k$",
         ha='center', va='top', fontsize=14, color=COL['node'])
fig.text(0.5, 0.025, r"the same band $2\sqrt{\Delta-1}$ governs both sides",
         ha='center', va='bottom', fontsize=9.2, color=COL['grey'])
save(fig, "bass_fig5_trace")
