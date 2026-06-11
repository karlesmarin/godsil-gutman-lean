"""Part VI figure 2: why the window is sharp — the walk that breaks it.

Left panel: inside the window (k = g) the only closed walks the tree cannot explain are the
pure cycle traversals, and they are exactly the non-backtracking ones: both censuses count
the same object.
Right panel: at k = g + 2 the first 'lollipop' appears — wrap the pentagon, then take the
tail out and back. It wraps a cycle, so it does NOT lift to the path tree (the left census
counts it); but the tail tip is an immediate backtrack, so it is NOT non-backtracking (the
right census rejects it). The two censuses part company, on every graph.
"""
from fig_style import COL, setup, save
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyArrowPatch

setup()
fig, axes = plt.subplots(1, 2, figsize=(8.6, 4.0))

def pentagon(ax, cx=0.0, cy=0.0, r=1.0):
    ang = np.pi / 2 + np.arange(5) * 2 * np.pi / 5
    pts = np.c_[cx + r * np.cos(ang), cy + r * np.sin(ang)]
    return pts

def draw_graph(ax, pts, extra=None):
    n = len(pts)
    for i in range(n):
        j = (i + 1) % n
        ax.plot([pts[i, 0], pts[j, 0]], [pts[i, 1], pts[j, 1]],
                color=COL["grey"], lw=1.4, zorder=1)
    if extra is not None:
        ax.plot([pts[0, 0], extra[0]], [pts[0, 1], extra[1]],
                color=COL["grey"], lw=1.4, zorder=1)
        ax.scatter([extra[0]], [extra[1]], s=110, color=COL["node"], zorder=3)
    ax.scatter(pts[:, 0], pts[:, 1], s=110, color=COL["node"], zorder=3)

def walk_arrow(ax, p, q, color, shrink=11, rad=0.18, lw=2.0):
    ax.add_patch(FancyArrowPatch(p, q, connectionstyle=f"arc3,rad={rad}",
                                 arrowstyle="-|>", mutation_scale=13,
                                 shrinkA=shrink, shrinkB=shrink, color=color,
                                 lw=lw, zorder=4))

# ---- left panel: the window walk = the cycle traversal ----------------------
ax = axes[0]
pts = pentagon(ax)
draw_graph(ax, pts)
for i in range(5):
    walk_arrow(ax, pts[i], pts[(i + 1) % 5], COL["pos"])
ax.scatter([pts[0, 0]], [pts[0, 1]], s=180, facecolor="white",
           edgecolor=COL["pos"], lw=2.0, zorder=2)
ax.text(pts[0, 0], pts[0, 1] + 0.22, "base", ha="center", fontsize=9,
        color=COL["pos"])
ax.set_title("inside the window: $k = g$", fontsize=11)
ax.text(0, -1.62,
        "the only walk the tree cannot explain\nis the cycle itself",
        ha="center", fontsize=9.5, color=COL["node"])
ax.text(0, -2.12,
        "no lift  $\\checkmark$        non-backtracking  $\\checkmark$\n"
        "counted by BOTH censuses",
        ha="center", fontsize=9.5, color=COL["pos"])

# ---- right panel: the lollipop at k = g + 2 ---------------------------------
ax = axes[1]
pts = pentagon(ax)
tip = np.array([pts[0, 0] + 1.05, pts[0, 1] + 0.12])
draw_graph(ax, pts, extra=tip)
for i in range(5):
    walk_arrow(ax, pts[i], pts[(i + 1) % 5], COL["pos"])
# the tail: out and immediately back (the backtrack)
walk_arrow(ax, pts[0], tip, COL["neg"], rad=0.30)
walk_arrow(ax, tip, pts[0], COL["neg"], rad=0.30)
ax.text(tip[0] + 0.08, tip[1] - 0.34, "backtrack!", fontsize=9.5,
        color=COL["neg"], ha="center")
ax.scatter([pts[0, 0]], [pts[0, 1]], s=180, facecolor="white",
           edgecolor=COL["pos"], lw=2.0, zorder=2)
ax.set_title("one step past it: $k = g+2$", fontsize=11)
ax.text(0.2, -1.62,
        "the lollipop: wrap the cycle,\nthen the tail out and back",
        ha="center", fontsize=9.5, color=COL["node"])
ax.text(0.2, -2.12,
        "no lift  $\\checkmark$        non-backtracking  $\\times$\n"
        "counted by ONE census only — the law breaks",
        ha="center", fontsize=9.5, color=COL["neg"])

for ax in axes:
    ax.set_xlim(-1.7, 2.1)
    ax.set_ylim(-2.45, 1.55)
    ax.set_aspect("equal")
    ax.axis("off")

fig.suptitle("Why the window is sharp: the first walk that one census sees and the other does not",
             fontsize=11.5, y=0.99)
fig.tight_layout()
save(fig, "gw_fig2_families")
