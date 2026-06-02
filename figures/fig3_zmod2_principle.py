"""Figure 3 — the ℤ/2 sign-averaging engine and the two results that formally share it."""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from fig_style import setup, save, COL
setup()

fig, ax = plt.subplots(figsize=(9.6,6.0))
ax.set_xlim(0,10); ax.set_ylim(0,10); ax.axis('off')

def box(x,y,w,h,fc,ec,lw=1.4):
    ax.add_patch(FancyBboxPatch((x-w/2,y-h/2),w,h, boxstyle="round,pad=0.02,rounding_size=0.12",
                 facecolor=fc, edgecolor=ec, lw=lw, zorder=2))
def arrow(x0,y0,x1,y1,col,lw=2.0):
    ax.add_patch(FancyArrowPatch((x0,y0),(x1,y1), arrowstyle='-|>', mutation_scale=15,
                 lw=lw, color=col, zorder=1))

# title (own text, not suptitle -> no collision)
ax.text(5,9.55, r"One $\mathbb{Z}/2$ engine, two results that formally share it",
        ha='center', va='center', fontsize=13)

# ENGINE
box(5,7.85,6.9,1.9, "#fbf1de", COL['accent'], 1.9)
ax.text(5,8.52, r"the $\mathbb{Z}/2$ sign-averaging engine", ha='center', va='center', fontsize=12)
ax.text(5,7.85, r"$\sum_{s\in\{\pm1\}} s^{k} = 2\cdot[\,k\ \mathrm{even}\,]$",
        ha='center', va='center', fontsize=12.5, color=COL['node'])
ax.text(5,7.18, "Lean:  sum_signOf_pow_eq_{zero_of_odd, two_of_even}",
        ha='center', va='center', fontsize=8.0, color=COL['grey'], family='monospace')

# LEFT corollary
box(2.5,4.45,4.0,2.0, "#eef4f6", COL['pos'], 1.6)
ax.text(2.5,5.18, "charpoly level", ha='center', fontsize=10.8, color=COL['pos'])
ax.text(2.5,4.82, "(elementary-symmetric)", ha='center', fontsize=8.2, color=COL['grey'])
ax.text(2.5,4.42, r"$\overline{\det(xI-A_s)}=\mu_G$", ha='center', fontsize=11.5)
ax.text(2.5,4.04, r"Godsil-Gutman   gate: $\sigma^2{=}1$", ha='center', fontsize=8.4)
ax.text(2.5,3.70, "godsil_gutman   proven", ha='center', fontsize=7.8,
        color=COL['node'], family='monospace')

# RIGHT corollary
box(7.5,4.45,4.0,2.0, "#f6efea", COL['neg'], 1.6)
ax.text(7.5,5.18, "moment level", ha='center', fontsize=10.8, color=COL['neg'])
ax.text(7.5,4.82, "(power-sum)", ha='center', fontsize=8.2, color=COL['grey'])
ax.text(7.5,4.42, r"$\overline{\mathrm{tr}(A_s^{d})}=P_d$", ha='center', fontsize=11.5)
ax.text(7.5,4.04, "parity-closed walks   gate: edges even", ha='center', fontsize=7.8)
ax.text(7.5,3.70, "sum_signOf_prod_pow   kernel", ha='center', fontsize=7.8,
        color=COL['node'], family='monospace')

# engine feeds BOTH
arrow(3.7,6.85,2.9,5.55, COL['pos'])
arrow(6.3,6.85,7.1,5.55, COL['neg'])

# gate downstream of the moment kernel
box(7.5,1.85,4.0,0.95, COL['band'], COL['grey'], 1.2)
ax.text(7.5,2.04, r"parity gate: survives $\Leftrightarrow$ all even", ha='center', fontsize=8.6)
ax.text(7.5,1.66, "signAvg_ne_zero_iff", ha='center', fontsize=7.8,
        color=COL['node'], family='monospace')
arrow(7.5,3.42,7.5,2.36, COL['grey'], lw=1.6)

# honest caveat, in the clear (under the LEFT box)
ax.text(2.5,1.85, "a shared atomic lemma\n(grep-verifiable),\nnot a single meta-theorem",
        ha='center', va='center', fontsize=8.4, color=COL['grey'], style='italic')

save(fig, "fig3_zmod2_principle")
