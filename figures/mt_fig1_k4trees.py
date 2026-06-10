"""Fig 1 (Paper V): K4, its reduced Laplacian, and the sixteen spanning trees.
All data exact: the 16 spanning trees of K4 enumerated by brute force; det L0 = 16."""
from itertools import combinations
import numpy as np
import matplotlib.pyplot as plt
from fig_style import COL, setup, save

setup()

# --- exact data -------------------------------------------------------------
V = [0, 1, 2, 3]
E = list(combinations(V, 2))            # 6 edges of K4


def connected(edges):
    adj = {v: set() for v in V}
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    seen, stack = {0}, [0]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w); stack.append(w)
    return len(seen) == 4


trees = [S for S in combinations(E, 3) if connected(S)]
assert len(trees) == 16
# reduced Laplacian of K4 at v0 = 0  (rows/cols 1,2,3)
L0 = np.array([[3, -1, -1], [-1, 3, -1], [-1, -1, 3]])
assert round(np.linalg.det(L0)) == 16

# --- layout -----------------------------------------------------------------
fig = plt.figure(figsize=(8.6, 4.4))
gs = fig.add_gridspec(1, 2, width_ratios=[1.05, 2.1], wspace=0.18)

# left panel: K4 + the reduced Laplacian
axL = fig.add_subplot(gs[0])
pos = {0: (0, 1), 1: (1, 1), 2: (0, 0), 3: (1, 0)}
for a, b in E:
    axL.plot(*zip(pos[a], pos[b]), color=COL["grey"], lw=1.6, zorder=1)
for v, (x, y) in pos.items():
    fc = COL["accent"] if v == 0 else COL["node"]
    axL.scatter([x], [y], s=460, color=fc, zorder=2)
    axL.text(x, y, str(v), color="white", ha="center", va="center",
             fontsize=11, zorder=3)
axL.text(0, 1.24, r"root $v_0$", ha="center", fontsize=10, color=COL["accent"])
rows = [[3, -1, -1], [-1, 3, -1], [-1, -1, 3]]
axL.text(0.02, -0.38, r"$L_0\;=$", ha="center", fontsize=11)
for i, row in enumerate(rows):
    for j, x in enumerate(row):
        axL.text(0.30 + 0.22 * j, -0.20 - 0.18 * i, f"${x}$",
                 ha="center", va="center", fontsize=10)
axL.plot([0.20, 0.17, 0.17, 0.20], [-0.10, -0.10, -0.66, -0.66],
         color=COL["node"], lw=1.0)
axL.plot([0.84, 0.87, 0.87, 0.84], [-0.10, -0.10, -0.66, -0.66],
         color=COL["node"], lw=1.0)
axL.text(0.52, -0.86, r"$\det L_0 = 16$", ha="center", fontsize=11,
         color=COL["accent"])
axL.set_xlim(-0.45, 1.45); axL.set_ylim(-1.05, 1.45)
axL.set_aspect("equal"); axL.axis("off")
axL.set_title(r"$K_4$ and its reduced Laplacian", fontsize=11)

# right panel: the 16 spanning trees, 4x4 grid
axR = fig.add_subplot(gs[1])
axR.set_title(r"the sixteen spanning trees that $\det L_0$ counts", fontsize=11)
sp = 1.6
for k, S in enumerate(trees):
    ox, oy = (k % 4) * sp, (3 - k // 4) * sp
    for a, b in E:
        x = [pos[a][0] + ox, pos[b][0] + ox]
        y = [pos[a][1] * 0.9 + oy, pos[b][1] * 0.9 + oy]
        if (a, b) in S:
            axR.plot(x, y, color=COL["pos"], lw=2.0, zorder=2)
        else:
            axR.plot(x, y, color=COL["band"], lw=0.9, zorder=1)
    for v, (x, y) in pos.items():
        fc = COL["accent"] if v == 0 else COL["node"]
        axR.scatter([x + ox], [y * 0.9 + oy], s=26, color=fc, zorder=3)
axR.set_xlim(-0.4, 3 * sp + 1.4); axR.set_ylim(-0.4, 3 * sp + 1.35)
axR.set_aspect("equal"); axR.axis("off")

save(fig, "mt_fig1_k4trees")
