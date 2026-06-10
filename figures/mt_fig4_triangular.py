"""Fig 4 (Paper V, centerpiece): the parent-edge recolumning makes the tree
minor upper-triangular. Exact 7-vertex example, root v0; rows/columns sorted
by the key (dist to root, vertex)."""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import COL, setup, save

setup()

# rooted tree on 0..6, root 0
TE = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (5, 6)]
dist = {0: 0, 1: 1, 2: 1, 3: 2, 4: 2, 5: 2, 6: 3}
parent_edge = {1: (0, 1), 2: (0, 2), 3: (1, 3), 4: (1, 4), 5: (2, 5), 6: (5, 6)}
order = sorted([v for v in range(7) if v != 0], key=lambda v: (dist[v], v))
assert order == [1, 2, 3, 4, 5, 6]


def entry(v, e):
    a, b = e
    if v == max(a, b):
        return 1
    if v == min(a, b):
        return -1
    return 0


T = np.array([[entry(u, parent_edge[w]) for w in order] for u in order])
assert all(T[i, j] == 0 for i in range(6) for j in range(i))      # upper-triangular
assert all(abs(T[i, i]) == 1 for i in range(6))                   # unit diagonal
assert round(abs(np.linalg.det(T))) == 1

fig = plt.figure(figsize=(8.8, 3.6))
gs = fig.add_gridspec(1, 2, width_ratios=[1.0, 1.15], wspace=0.12)

# left: the rooted tree with distance levels
axT = fig.add_subplot(gs[0])
pos = {0: (1.5, 3.0), 1: (0.7, 2.0), 2: (2.3, 2.0),
       3: (0.2, 1.0), 4: (1.2, 1.0), 5: (2.3, 1.0), 6: (2.3, 0.0)}
for d in range(4):
    axT.axhspan(2.55 - d, 3.45 - d, color=COL["band"], alpha=0.45 if d % 2 else 0.22)
    axT.text(3.35, 3.0 - d, rf"$d={d}$", fontsize=9, color=COL["grey"], va="center")
for a, b in TE:
    axT.plot(*zip(pos[a], pos[b]), color=COL["grey"], lw=1.6, zorder=2)
for v, (x, y) in pos.items():
    fc = COL["accent"] if v == 0 else COL["node"]
    axT.scatter([x], [y], s=420, color=fc, zorder=3)
    axT.text(x, y, rf"$v_{v}$" if v == 0 else str(v), color="white",
             ha="center", va="center", fontsize=10, zorder=4)
axT.set_xlim(-0.4, 3.9); axT.set_ylim(-0.6, 3.6)
axT.set_aspect("equal"); axT.axis("off")
axT.set_title("a spanning tree, rooted; key $=$ (distance, vertex)", fontsize=11)

# right: the recolumned, sorted matrix
axM = fig.add_subplot(gs[1])
n = 6
cw = 0.7
for i in range(n):
    for j in range(n):
        v = T[i, j]
        if v > 0:
            fc, tc = COL["pos"], "white"
        elif v < 0:
            fc, tc = COL["neg"], "white"
        else:
            fc, tc = ("#f2f5f7", COL["grey"])
        axM.add_patch(plt.Rectangle((j * cw, (n - 1 - i) * cw), cw, cw,
                                    facecolor=fc, edgecolor="white", lw=1.6))
        axM.text((j + 0.5) * cw, (n - 0.5 - i) * cw, str(v),
                 ha="center", va="center", fontsize=10, color=tc)
# diagonal frame
for i in range(n):
    axM.add_patch(plt.Rectangle((i * cw, (n - 1 - i) * cw), cw, cw, fill=False,
                                edgecolor=COL["accent"], lw=2.0, zorder=5))
for j, w in enumerate(order):
    a, b = parent_edge[w]
    axM.text((j + 0.5) * cw, n * cw + 0.10, rf"$e_{{{w}}}$", ha="center", fontsize=10)
    axM.text((j + 0.5) * cw, n * cw + 0.42, rf"$\{{{a},{b}\}}$",
             ha="center", fontsize=8, color=COL["grey"])
for i, u in enumerate(order):
    axM.text(-0.22, (n - 0.5 - i) * cw, str(u), ha="center", va="center", fontsize=10)
axM.text(n * cw / 2, -0.62,
         "rows: vertices by key$\\uparrow$ · columns: their parent edges\n"
         "zeros below the diagonal, $\\pm1$ on it $\\Rightarrow$ $\\det = \\pm 1$",
         ha="center", fontsize=9.5, color=COL["node"])
axM.set_xlim(-0.55, n * cw + 0.3); axM.set_ylim(-1.15, n * cw + 0.75)
axM.set_aspect("equal"); axM.axis("off")

save(fig, "mt_fig4_triangular")
