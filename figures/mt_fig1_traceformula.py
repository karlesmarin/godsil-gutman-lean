"""Part IV, Figure 1 -- the moment theorem as the tree side of the trace formula.

For two graphs (K4, girth 3; Petersen, girth 5) and length k = 0..8:
  * the matching power sum  p_k = sum_i theta_i^k  (roots of the matching polynomial),
    which this paper's theorem identifies with the tree-like walk count
    treeLikeWalkCount(G,k) = sum_v [A(T(G,v))^k]_root  -- the TREE side;
  * tr(A^k) = number of ALL closed walks of length k  -- the CYCLE side.
Below the girth every closed walk is tree-like, so the two coincide (shaded);
the first gap appears exactly at k = girth and counts the shortest cycles,
tr(A^g) - p_g = 2 g c_g.  The moment theorem is the certified identity p_k = treeLike.

m_k (matching counts) computed by brute-force enumeration; tr(A^k) from eigenvalues.
"""
import numpy as np
import matplotlib.pyplot as plt
from itertools import combinations
from fig_style import setup, save, COL
setup()


def matching_counts(n, edges):
    """m_k = number of k-edge matchings; returns list m_0..m_{n//2}."""
    m = [0] * (n // 2 + 1)
    m[0] = 1
    for k in range(1, n // 2 + 1):
        c = 0
        for comb in combinations(edges, k):
            seen = set()
            ok = True
            for (a, b) in comb:
                if a in seen or b in seen:
                    ok = False
                    break
                seen.add(a); seen.add(b)
            if ok:
                c += 1
        m[k] = c
    return m


def matching_poly_roots(n, edges):
    """roots of mu(G,x) = sum_k (-1)^k m_k x^{n-2k}."""
    m = matching_counts(n, edges)
    coeff = [0.0] * (n + 1)            # coeff[j] = coefficient of x^{n-j}, index by power
    poly = np.zeros(n + 1)
    for k, mk in enumerate(m):
        poly[2 * k] += ((-1) ** k) * mk   # term x^{n-2k}: power n-2k -> index 2k from top
    # np.roots wants highest-degree first: poly[0]=x^n coeff, poly[2k]=x^{n-2k}
    return np.roots(poly)


def adjacency(n, edges):
    A = np.zeros((n, n))
    for (a, b) in edges:
        A[a, b] = A[b, a] = 1.0
    return A


def panel(ax, n, edges, girth, title, cg, gap_xy):
    roots = matching_poly_roots(n, edges)
    A = adjacency(n, edges)
    evals = np.linalg.eigvalsh(A)
    ks = list(range(0, 9))
    pk = [int(round(np.real(np.sum(roots ** k)))) for k in ks]      # = treeLikeWalkCount
    trk = [int(round(np.sum(evals ** k))) for k in ks]              # all closed walks

    ax.axvspan(-0.3, girth - 0.5, color=COL['band'], alpha=0.6, zorder=0)
    ax.plot(ks, trk, '--s', color=COL['neg'], lw=1.9, ms=6.5, mfc='white', zorder=3,
            label=r'$\mathrm{tr}(A^k)$  (all closed walks)')
    ax.plot(ks, pk, '-o', color=COL['pos'], lw=2.4, ms=7.5, zorder=4,
            label=r'$p_k=\sum_i\theta_i^{\,k}=\mathrm{treeLikeWalkCount}(G,k)$')

    # mark the first gap at k = girth
    g = girth
    ax.annotate('', xy=(g, trk[g]), xytext=(g, pk[g]),
                arrowprops=dict(arrowstyle='<->', color=COL['accent'], lw=1.4))
    ax.annotate(rf'$\mathrm{{tr}}(A^{{{g}}})-p_{{{g}}}={trk[g]-pk[g]}=2\cdot{g}\cdot{cg}$',
                xy=(g, 0.5 * (trk[g] + pk[g])), textcoords="offset points",
                xytext=gap_xy, fontsize=8.7, color=COL['accent'], fontweight='bold',
                ha='left', va='center')
    ax.set_yscale('symlog')
    ax.set_title(title, fontsize=11, color=COL['node'])
    ax.set_xlabel(r'walk length $k$')
    ax.set_xticks(ks)
    ax.grid(True, which='major', axis='y', color=COL['band'], lw=0.6, alpha=0.7)
    ax.text(0.6, 0.04, r'$k<\mathrm{girth}$: $p_k=\mathrm{tr}(A^k)$', transform=ax.transAxes,
            fontsize=8.4, color=COL['grey'], ha='center')


# K4: vertices 0..3, all pairs
K4_edges = list(combinations(range(4), 2))
# Petersen: standard labelling (outer 0-4 pentagon, inner 5-9 pentagram, spokes)
PET_edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
             (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
             (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

fig, axes = plt.subplots(1, 2, figsize=(11.4, 4.4))
panel(axes[0], 4, K4_edges, 3, r'$K_4$  (girth $3$, $c_3=4$ triangles)', 4, (10, 0))
panel(axes[1], 10, PET_edges, 5, r'Petersen  (girth $5$, $c_5=12$ pentagons)', 12, (8, 0))
axes[0].set_ylabel(r'closed-walk count  (symlog)')
h, l = axes[0].get_legend_handles_labels()
fig.legend(h, l, loc='upper center', ncol=2, frameon=False, fontsize=9.6,
           bbox_to_anchor=(0.5, 1.06))
fig.tight_layout(rect=[0, 0, 1, 0.98])
save(fig, "mt_fig1_traceformula")
