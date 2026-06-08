"""Part III, Figure 2 — why the definition matters, and that it is right.

For K4, length k = 0..8:
  * matching power sum  p_k = sum_i theta_i^k  (roots of mu_{K4}=x^4-6x^2+3),
  * the path-tree / tree-like walk count  sum_v [A(T(K4,v))^k]_root,
  * the NAIVE 'acyclic edge-support' count.
The first two coincide exactly (the bijection of this paper); the naive count
agrees through k=5 and then UNDERCOUNTS -- 276 against 324 at k=6 -- because a
tree-like walk may traverse all three edges of a triangle while every
intermediate path stays simple. This is the datapoint that selected the
liftSeq definition before any formal effort.
"""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()

# roots of the matching polynomial of K4:  mu = x^4 - 6 x^2 + 3  ->  x^2 = 3 +- sqrt6
import math
s = math.sqrt(6.0)
roots = [math.sqrt(3 + s), -math.sqrt(3 + s), math.sqrt(3 - s), -math.sqrt(3 - s)]
ks = list(range(0, 9))
pk = [round(sum(r**k for r in roots)) for k in ks]            # = tree-like = path-tree count
# naive acyclic-edge-support closed-walk count on K4 (computed exactly, verify_godsil.py):
naive = [4, 0, 12, 0, 60, 0, 276, 0, 1020]                    # agrees to k=5, breaks at k=6 (276<324)

fig, ax = plt.subplots(figsize=(7.6, 4.3))

ax.plot(ks, pk, '-o', color=COL['pos'], lw=2.4, ms=8, zorder=4,
        label=r'$p_k=\sum_i\theta_i^{\,k}$  $=$  tree-like walk count  $=\ \sum_v[A(T)^k]_{\rm root}$')
ax.plot(ks, naive, '--s', color=COL['neg'], lw=2.0, ms=7, zorder=3, mfc='white',
        label=r'naive "acyclic edge-support" count (wrong)')

# annotate the first divergence at k=6
ax.annotate(r'$324$', (6, 324), textcoords="offset points", xytext=(-2, 12),
            color=COL['pos'], fontsize=11, ha='center', fontweight='bold')
ax.annotate(r'$276$', (6, 276), textcoords="offset points", xytext=(6, -16),
            color=COL['neg'], fontsize=11, ha='center', fontweight='bold')
ax.annotate('first gap\n(traverses a triangle,\nstill tree-like)', (6, 300),
            textcoords="offset points", xytext=(-78, -2), fontsize=8.6, color=COL['grey'],
            ha='center', va='center',
            arrowprops=dict(arrowstyle='-|>', color=COL['grey'], lw=1.1,
                            connectionstyle="arc3,rad=-0.2"))
# shade the agreement region k<=5
ax.axvspan(-0.3, 5.5, color=COL['band'], alpha=0.5, zorder=0)
ax.text(2.45, 760, 'below twice the girth:\ncounts coincide',
        fontsize=8.8, color=COL['grey'], ha='center', va='center')

ax.set_xlabel(r'walk length $k$'); ax.set_ylabel(r'number of closed walks (summed over $v$)')
ax.set_title(r'$K_4$: the corrected count vs. the plausible-but-wrong one', fontsize=11.5, pad=8)
ax.set_xticks(ks)
ax.legend(loc='upper left', fontsize=9.0, frameon=False)
ax.grid(True, axis='y', color=COL['grey'], alpha=0.18, lw=0.7)
for sp in ('top', 'right'):
    ax.spines[sp].set_visible(False)

save(fig, "pt_fig2_moments")
