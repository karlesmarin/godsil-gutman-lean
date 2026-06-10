"""Fig 3 (Paper V): the oriented incidence matrix and its Gram factorization
N N^T = D - A on the triangle-with-tail graph. All entries exact."""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import COL, setup, save

setup()

# triangle 1,2,3 plus tail 3-4 (paper labels 1..4; code 0..3)
E = [(0, 1), (0, 2), (1, 2), (2, 3)]
N = np.zeros((4, 4), dtype=int)
for j, (a, b) in enumerate(E):
    N[max(a, b), j] = 1
    N[min(a, b), j] = -1
L = N @ N.T
Lexp = np.array([[2, -1, -1, 0], [-1, 2, -1, 0], [-1, -1, 3, -1], [0, 0, -1, 1]])
assert (L == Lexp).all()


def draw_mat(ax, M, x0, y0, cw, ch, signed=True, fs=10):
    m, n = M.shape
    for i in range(m):
        for j in range(n):
            v = M[i, j]
            if signed and v > 0:
                fc = COL["pos"]; tc = "white"
            elif signed and v < 0:
                fc = COL["neg"]; tc = "white"
            else:
                fc = "white"; tc = COL["grey"]
            ax.add_patch(plt.Rectangle((x0 + j * cw, y0 - (i + 1) * ch), cw, ch,
                                       facecolor=fc, edgecolor=COL["grey"], lw=0.7,
                                       alpha=0.92 if v else 1.0))
            ax.text(x0 + (j + 0.5) * cw, y0 - (i + 0.5) * ch, str(v),
                    ha="center", va="center", fontsize=fs, color=tc)


fig = plt.figure(figsize=(9.0, 3.1))
gs = fig.add_gridspec(1, 2, width_ratios=[0.85, 2.3], wspace=0.10)

# left: the graph, edges drawn as arrows from smaller to larger endpoint
axG = fig.add_subplot(gs[0])
pos = {0: (0.0, 1.0), 1: (1.0, 1.0), 2: (0.5, 0.25), 3: (0.5, -0.75)}
for (a, b) in E:
    (x1, y1), (x2, y2) = pos[a], pos[b]
    axG.annotate("", xy=(x2 + 0.82 * 0, y2), xytext=(x1, y1),
                 arrowprops=dict(arrowstyle="-|>", color=COL["grey"], lw=1.7,
                                 shrinkA=14, shrinkB=14))
for v, (x, y) in pos.items():
    axG.scatter([x], [y], s=430, color=COL["node"], zorder=3)
    axG.text(x, y, str(v + 1), color="white", ha="center", va="center",
             fontsize=11, zorder=4)
axG.text(0.5, -1.25, "arrows: smaller $\\to$ larger endpoint\n($-1$ at tail, $+1$ at head)",
         ha="center", fontsize=9, color=COL["grey"])
axG.set_xlim(-0.4, 1.4); axG.set_ylim(-1.55, 1.35)
axG.set_aspect("equal"); axG.axis("off")

# right: N  N^T  =  D - A
axM = fig.add_subplot(gs[1])
draw_mat(axM, N, 0.0, 2.0, 0.5, 0.5)
axM.text(2.35, 1.0, r"$\cdot$", fontsize=14, ha="center")
draw_mat(axM, N.T, 2.6, 2.0, 0.5, 0.5)
axM.text(4.95, 1.0, r"$=$", fontsize=13, ha="center")
draw_mat(axM, L, 5.25, 2.0, 0.5, 0.5, signed=False)
axM.text(1.0, 2.18, r"$N$", ha="center", fontsize=11)
axM.text(3.6, 2.18, r"$N^{\mathsf{T}}$", ha="center", fontsize=11)
axM.text(6.25, 2.18, r"$D-A$", ha="center", fontsize=11, color=COL["accent"])
axM.set_xlim(-0.2, 7.6); axM.set_ylim(-0.4, 2.5)
axM.set_aspect("equal"); axM.axis("off")

save(fig, "mt_fig3_gram")
