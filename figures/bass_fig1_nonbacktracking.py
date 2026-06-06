"""Figure 1 — Bass on a small graph: the non-backtracking operator B on the 2|E| darts,
and the reduction of det(I - uB) to |V|-dimensional adjacency/degree data."""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from fig_style import setup, save, COL
setup()

# C4 on a square
pos = {0: (0, 1), 1: (1, 0), 2: (0, -1), 3: (-1, 0)}
edges = [(0, 1), (1, 2), (2, 3), (3, 0)]

def darrow(ax, p, q, color, lw=2.2, rad=0.16, alpha=1.0, z=2):
    a = FancyArrowPatch(pos[p], pos[q], connectionstyle=f"arc3,rad={rad}",
                        arrowstyle='-|>', mutation_scale=13, lw=lw, color=color,
                        alpha=alpha, zorder=z, shrinkA=12, shrinkB=12)
    ax.add_patch(a)

fig = plt.figure(figsize=(9.4, 4.2))
gs = fig.add_gridspec(1, 3, width_ratios=[1.25, 0.5, 1.45], wspace=0.1)

# --- left: the graph with darts; one non-backtracking step highlighted ---
ax = fig.add_subplot(gs[0, 0])
for (i, j) in edges:
    darrow(ax, i, j, COL['grey'], lw=1.4, alpha=0.45)
    darrow(ax, j, i, COL['grey'], lw=1.4, alpha=0.45)
# highlight a non-backtracking transition: dart 0->1 then 1->2 (allowed)
darrow(ax, 0, 1, COL['pos'], lw=2.8)
darrow(ax, 1, 2, COL['accent'], lw=2.8)
# the forbidden U-turn 1->0 (faded red, dashed)
a = FancyArrowPatch(pos[1], pos[0], connectionstyle="arc3,rad=0.16", arrowstyle='-|>',
                    mutation_scale=12, lw=2.0, color=COL['neg'], ls=(0, (3, 2)),
                    alpha=0.6, zorder=2, shrinkA=12, shrinkB=12)
ax.add_patch(a)
for v, (px, py) in pos.items():
    ax.scatter([px], [py], s=240, color=COL['node'], zorder=4, edgecolors='white', linewidths=1.5)
    ax.text(px, py, str(v), color='white', ha='center', va='center', fontsize=10, zorder=5)
ax.text(0.5, 0.62, r"$d$", color=COL['pos'], fontsize=12, zorder=6)
ax.text(0.58, -0.52, r"$e$", color=COL['accent'], fontsize=12, zorder=6)
ax.text(-0.62, 0.5, r"U-turn", color=COL['neg'], fontsize=8.5, zorder=6)
ax.set_xlim(-1.6, 1.6); ax.set_ylim(-1.5, 1.5); ax.set_aspect('equal'); ax.axis('off')
ax.set_title(r"$B_{d,e}=1$: head of $d$ = tail of $e$, $e\neq d^{\mathrm{symm}}$"
             "\n" r"($2|E|=8$ darts)", fontsize=9.8)

# --- middle: arrow ---
axa = fig.add_subplot(gs[0, 1]); axa.axis('off')
axa.annotate("", xy=(0.95, 0.5), xytext=(0.05, 0.5), xycoords='axes fraction',
             arrowprops=dict(arrowstyle='-|>', lw=2.2, color=COL['accent']))
axa.text(0.5, 0.62, "Bass", ha='center', va='bottom', fontsize=10.5, color=COL['accent'])

# --- right: the reduction, boxed ---
axr = fig.add_subplot(gs[0, 2]); axr.axis('off')
axr.add_patch(plt.Rectangle((0.02, 0.34), 0.96, 0.50, transform=axr.transAxes,
              facecolor=COL['band'], edgecolor=COL['pos'], lw=1.3, zorder=0))
axr.text(0.5, 0.70, r"$(1-u^2)^{|V|}\det(I-uB)$", ha='center', va='center', fontsize=11.5)
axr.text(0.5, 0.575, r"$=\,(1-u^2)^{|E|}\det(I-uA+u^2(D-I))$",
         ha='center', va='center', fontsize=10.5)
axr.text(0.5, 0.435, r"$2|E|$-dim  $\longrightarrow$  $|V|$-dim", ha='center', va='center',
         fontsize=9.2, color=COL['grey'])
axr.text(0.5, 0.16, "bass_determinant   (Lean 4 - axioms: propext, choice, Quot.sound)",
         ha="center", va="center", fontsize=7.2, color=COL["node"], family="monospace")

fig.suptitle(r"Bass's formula: the $2|E|$-dimensional non-backtracking determinant, from $|V|$-dimensional data",
             fontsize=11.5, y=1.0)
save(fig, "bass_fig1_nonbacktracking")
