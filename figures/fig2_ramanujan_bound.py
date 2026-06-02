"""Figure 2 — Heilmann-Lieb: roots of the matching polynomial lie in [-2√(Δ-1), 2√(Δ-1)],
the Ramanujan threshold. The endpoint of the formalised story."""
import numpy as np, networkx as nx, itertools
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()

def matching_numbers(G):
    n=G.number_of_nodes(); E=list(G.edges())
    from math import comb
    m={0:1}
    # count k-matchings by brute force over edge subsets (small graphs)
    for k in range(1, n//2+1):
        c=0
        for sub in itertools.combinations(E,k):
            verts=[v for e in sub for v in e]
            if len(set(verts))==2*k: c+=1
        m[k]=c
    return n,m

def matching_poly_roots(G):
    n,m=matching_numbers(G)
    coeffs=[0.0]*(n+1)            # poly in x, degree n
    for k,mk in m.items():
        coeffs[n-(n-2*k)] = 0     # placeholder
    # build mu(x)=sum_k (-1)^k m_k x^{n-2k}; numpy wants highest-first
    poly=np.zeros(n+1)
    for k,mk in m.items():
        poly[2*k] += (-1)**k * mk   # coefficient of x^{n-2k} -> index 2k from the front
    r=np.roots(poly)
    return n, np.sort(r.real)

graphs=[
 ("$K_3$",            nx.complete_graph(3)),
 ("$C_5$",            nx.cycle_graph(5)),
 ("$K_4$",            nx.complete_graph(4)),
 ("Petersen",         nx.petersen_graph()),
 ("$K_{1,4}$ (star)", nx.star_graph(4)),
 ("$K_{3,3}$",        nx.complete_bipartite_graph(3,3)),
]

fig, ax = plt.subplots(figsize=(8.6,4.4))
ymax=len(graphs)
for idx,(name,G) in enumerate(reversed(graphs)):
    y=idx
    Delta=max(d for _,d in G.degree())
    bound=2*np.sqrt(Delta-1)
    n,roots=matching_poly_roots(G)
    # band
    ax.add_patch(plt.Rectangle((-bound,y-0.32),2*bound,0.64, facecolor=COL['band'],
                 edgecolor='none', zorder=0))
    ax.plot([-bound,-bound],[y-0.32,y+0.32],color=COL['pos'],lw=1.5,zorder=1)
    ax.plot([ bound, bound],[y-0.32,y+0.32],color=COL['pos'],lw=1.5,zorder=1)
    # roots
    ax.scatter(roots, [y]*len(roots), s=46, color=COL['neg'], zorder=3,
               edgecolors='white', linewidths=0.7)
    ax.text(-bound-0.18, y, name, ha='right', va='center', fontsize=10.5)
    ax.text(bound+0.18, y, rf"$\Delta={Delta},\ 2\sqrt{{\Delta-1}}={bound:.2f}$",
            ha='left', va='center', fontsize=8.6, color=COL['grey'])

ax.axvline(0, color=COL['grey'], lw=0.6, ls=':', zorder=0)
ax.set_xlim(-5.6,5.6); ax.set_ylim(-0.7, ymax-0.3)
ax.set_yticks([]); ax.spines[['left','right','top']].set_visible(False)
ax.set_xlabel("root of the matching polynomial  (eigenvalue scale)")
ax.set_title(r"Heilmann–Lieb: every root of $\mu_G$ lies in $[-2\sqrt{\Delta-1},\,2\sqrt{\Delta-1}]$"
             "\n"
             r"— the Ramanujan threshold (banded). Where the formalised story ends.",
             fontsize=11, pad=10)
save(fig, "fig2_ramanujan_bound")
