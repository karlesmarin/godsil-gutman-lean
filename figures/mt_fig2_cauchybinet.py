"""Fig 2 (Paper V): Cauchy-Binet on a 2x3 / 3x2 pair -- the three column
selections and their minor products. All numbers exact (det AB = -264)."""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import COL, setup, save

setup()

A = np.array([[1, 2, 3], [4, 5, 6]])
B = np.array([[7, 1], [2, 8], [3, 4]])
AB = A @ B
assert round(np.linalg.det(AB)) == -264
sels = [(0, 1), (0, 2), (1, 2)]
prods = []
for S in sels:
    dA = round(np.linalg.det(A[:, S]))
    dB = round(np.linalg.det(B[S, :]))
    prods.append((dA, dB))
assert sum(a * b for a, b in prods) == -264


def draw_mat(ax, M, x0, y0, cw, ch, hl_cols=None, hl_rows=None, fs=10):
    m, n = M.shape
    for i in range(m):
        for j in range(n):
            sel = (hl_cols is not None and j in hl_cols) or \
                  (hl_rows is not None and i in hl_rows)
            fc = COL["band"] if sel else "white"
            ax.add_patch(plt.Rectangle((x0 + j * cw, y0 - (i + 1) * ch), cw, ch,
                                       facecolor=fc, edgecolor=COL["grey"], lw=0.7))
            ax.text(x0 + (j + 0.5) * cw, y0 - (i + 0.5) * ch, str(M[i, j]),
                    ha="center", va="center", fontsize=fs)


fig, axes = plt.subplots(1, 3, figsize=(8.8, 2.05))
labels = [r"$S=\{1,2\}$", r"$S=\{1,3\}$", r"$S=\{2,3\}$"]
for ax, S, (dA, dB), lab in zip(axes, sels, prods, labels):
    draw_mat(ax, A, 0.0, 2.0, 0.5, 0.5, hl_cols=S)
    ax.text(1.85, 1.75, r"$\times$", fontsize=12, ha="center")
    draw_mat(ax, B, 2.2, 2.25, 0.5, 0.5, hl_rows=S)
    ax.text(1.7, 0.55,
            rf"$\det A_S \cdot \det B_S = ({dA})\cdot({dB}) = {dA*dB}$",
            ha="center", fontsize=10, color=COL["node"])
    ax.set_title(lab, fontsize=11)
    ax.set_xlim(-0.3, 3.9); ax.set_ylim(0.2, 2.6)
    ax.set_aspect("equal"); ax.axis("off")
fig.suptitle(r"$\det(AB) \;=\; -162 \,-\, 150 \,+\, 48 \;=\; -264$"
             r"$\;$ : one product of minors per choice of columns",
             fontsize=11, y=0.02, color=COL["accent"])
fig.subplots_adjust(top=0.86, bottom=0.16)
save(fig, "mt_fig2_cauchybinet")
