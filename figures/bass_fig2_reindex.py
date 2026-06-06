"""Figure 2 — the orientation reindex: 2|E| darts sorted into |E| reversal pairs
block-diagonalize J, so det(I + uJ) = (1 - u^2)^|E|."""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Rectangle
from fig_style import setup, save, COL
setup()

fig, ax = plt.subplots(figsize=(9.6, 3.9))
ax.axis('off'); ax.set_xlim(0, 10); ax.set_ylim(0, 4)

# --- left: 2|E| darts, paired by reversal ---
ax.text(1.5, 3.7, r"$2|E|$ darts", ha='center', fontsize=10.5, color=COL['node'])
pairs_y = [3.0, 2.1, 1.2, 0.3]
for k, y in enumerate(pairs_y):
    # positive dart (teal) and its reversal (grey), joined
    ax.scatter([0.7], [y], s=70, color=COL['pos'], zorder=3)
    ax.scatter([2.3], [y], s=70, color=COL['grey'], zorder=3)
    ax.plot([0.7, 2.3], [y, y], color=COL['grey'], lw=1.0, ls=(0, (3, 2)), zorder=1)
    ax.text(0.7, y + 0.18, r"$d_%d$" % (k + 1), ha='center', fontsize=8, color=COL['pos'])
    ax.text(2.3, y + 0.18, r"$d_%d^{\mathrm{symm}}$" % (k + 1), ha='center', fontsize=8, color=COL['grey'])
ax.text(1.5, -0.25, r"reversal pairs $d\leftrightarrow d^{\mathrm{symm}}$", ha='center',
        fontsize=8.5, color=COL['grey'])

# arrow
a = FancyArrowPatch((3.0, 1.7), (4.0, 1.7), arrowstyle='-|>', mutation_scale=15,
                    lw=2.2, color=COL['accent'])
ax.add_patch(a)
ax.text(3.5, 2.05, "dartEquiv", ha='center', fontsize=8.5, color=COL['accent'], family='monospace')
ax.text(3.5, 1.35, r"$\simeq\mathrm{Bool}\times\{\mathrm{pos}\}$", ha='center', fontsize=8, color=COL['grey'])

# --- middle: block-diagonal I + uJ ---
ax.text(6.0, 3.7, r"$I+uJ$  (block diagonal)", ha='center', fontsize=10.5, color=COL['node'])
bx, by = 4.6, 0.4
for k in range(4):
    yy = by + (3 - k) * 0.78
    ax.add_patch(Rectangle((bx, yy), 0.78, 0.62, facecolor=COL['band'],
                 edgecolor=COL['pos'], lw=1.2, zorder=1))
    ax.text(bx + 0.2, yy + 0.42, "1", ha='center', fontsize=8.5)
    ax.text(bx + 0.58, yy + 0.42, "u", ha='center', fontsize=8.5, color=COL['accent'])
    ax.text(bx + 0.2, yy + 0.18, "u", ha='center', fontsize=8.5, color=COL['accent'])
    ax.text(bx + 0.58, yy + 0.18, "1", ha='center', fontsize=8.5)
ax.text(bx + 0.39, by - 0.25, "one [[1,u],[u,1]] per edge",
        ha='center', fontsize=8.2, color=COL['grey'])

# arrow
a2 = FancyArrowPatch((6.1, 1.7), (7.0, 1.7), arrowstyle='-|>', mutation_scale=15,
                     lw=2.2, color=COL['accent'])
ax.add_patch(a2)
ax.text(6.55, 2.05, r"$\det_{\mathrm{block}}$", ha='center', fontsize=8.5, color=COL['accent'])

# --- right: result box ---
ax.add_patch(Rectangle((7.25, 1.15), 2.6, 1.15, facecolor=COL['band'],
             edgecolor=COL['pos'], lw=1.3, zorder=1))
ax.text(8.55, 1.95, r"$\det(I+uJ)$", ha='center', fontsize=11)
ax.text(8.55, 1.55, r"$=(1-u^2)^{|E|}$", ha='center', fontsize=11.5)
ax.text(8.55, 0.78, "det_one_add_smul_reversal", ha='center', fontsize=6.8,
        color=COL['node'], family='monospace')
ax.text(8.55, 0.52, r"$\det\,[[1,u],[u,1]]=1-u^2$",
        ha='center', fontsize=8.2, color=COL['grey'])

fig.suptitle(r"Orientation reindex: $J$ is $|E|$ disjoint swaps, so $I+uJ$ is block-diagonal and $\det(I+uJ)=(1-u^2)^{|E|}$",
             fontsize=11, y=1.0)
save(fig, "bass_fig2_reindex")
