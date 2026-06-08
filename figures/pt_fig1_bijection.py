"""Part III, Figure 1 — the bijection: a closed walk at the root of T(G,u)
and its projection, a tree-like closed walk of G at u.

Left:  G = diamond, the tree-like walk  u -> a -> b -> a -> u  drawn on it,
       edges coloured EXTEND (teal, advance to a fresh vertex) / RETREAT
       (amber, backtrack to the parent).
Right: T(G,u), the SAME walk lifted: root u -> ua -> uab -> ua -> u, a closed
       walk at the root. The down-projection pi (path |-> endpoint) carries the
       right walk to the left one; it is a length-preserving bijection.
"""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from fig_style import setup, save, COL
setup()

# ---------- left: the diamond graph G ----------
gpos = {'u': (0, 1.0), 'a': (-1.0, 0.0), 'b': (1.0, 0.0), 'c': (0, -1.0)}
gedges = [('u', 'a'), ('u', 'b'), ('a', 'b'), ('a', 'c'), ('b', 'c')]
# the tree-like walk u->a->b->a->u as a list of (edge, kind)
gwalk = [('u', 'a', 'ext'), ('a', 'b', 'ext'), ('b', 'a', 'ret'), ('a', 'u', 'ret')]

# ---------- right: the path-tree T(G,u) ----------
tpos = {
    'u':    ('u',    1.60, 3.0),
    'ua':   ('ua',   0.50, 2.0),
    'ub':   ('ub',   2.70, 2.0),
    'uab':  ('uab',  0.00, 1.0),
    'uac':  ('uac',  1.00, 1.0),
    'uba':  ('uba',  2.20, 1.0),
    'ubc':  ('ubc',  3.20, 1.0),
    'uabc': ('uabc', 0.00, 0.0),
    'uacb': ('uacb', 1.00, 0.0),
    'ubac': ('ubac', 2.20, 0.0),
    'ubca': ('ubca', 3.20, 0.0),
}
tedges = [('u', 'ua'), ('u', 'ub'), ('ua', 'uab'), ('ua', 'uac'),
          ('ub', 'uba'), ('ub', 'ubc'), ('uab', 'uabc'), ('uac', 'uacb'),
          ('uba', 'ubac'), ('ubc', 'ubca')]
# the lifted walk u -> ua -> uab -> ua -> u
twalk = [('u', 'ua', 'ext'), ('ua', 'uab', 'ext'), ('uab', 'ua', 'ret'), ('ua', 'u', 'ret')]

fig = plt.figure(figsize=(9.6, 4.2))
gs = fig.add_gridspec(1, 2, width_ratios=[1.0, 1.9], wspace=0.06)


def draw_walk(ax, pos, walk, lab=None):
    """Overlay a walk: teal=extend, amber=retreat, slight curvature so both
    directions of a retraced edge are visible."""
    seen = {}
    for (i, j, kind) in walk:
        (x0, y0) = pos[i][1:] if lab else pos[i]
        (x1, y1) = pos[j][1:] if lab else pos[j]
        key = frozenset((i, j))
        rad = 0.16 if key in seen else -0.16 if (i, j)[::-1] in [w[:2] for w in walk] else 0.0
        seen[key] = True
        col = COL['pos'] if kind == 'ext' else COL['accent']
        arr = FancyArrowPatch((x0, y0), (x1, y1), connectionstyle=f"arc3,rad={rad}",
                              arrowstyle='-|>', mutation_scale=15, lw=2.6,
                              color=col, zorder=5, shrinkA=13, shrinkB=13)
        ax.add_patch(arr)


# --- left panel: G with the tree-like walk ---
axg = fig.add_subplot(gs[0, 0])
for i, j in gedges:
    (x0, y0), (x1, y1) = gpos[i], gpos[j]
    axg.plot([x0, x1], [y0, y1], color=COL['band'], lw=4.0, solid_capstyle='round', zorder=1)
draw_walk(axg, gpos, gwalk)
for v, (px, py) in gpos.items():
    isroot = (v == 'u')
    axg.scatter([px], [py], s=360 if isroot else 250,
                color=COL['accent'] if isroot else COL['node'],
                zorder=6, edgecolors='white', linewidths=1.6)
    axg.text(px, py, v, ha='center', va='center', fontsize=11,
             color='white', zorder=7, family='monospace')
axg.set_xlim(-1.55, 1.35); axg.set_ylim(-1.5, 1.55); axg.set_aspect('equal'); axg.axis('off')
axg.set_title(r"$G$: tree-like walk $u\,a\,b\,a\,u$", fontsize=10.5, pad=6)

# --- right panel: T(G,u) with the lifted walk ---
axt = fig.add_subplot(gs[0, 1])
for i, j in tedges:
    (_, x0, y0), (_, x1, y1) = tpos[i], tpos[j]
    axt.plot([x0, x1], [y0, y1], color=COL['band'], lw=3.2, solid_capstyle='round', zorder=1)
draw_walk(axt, tpos, twalk, lab=True)
for nid, (labtxt, px, py) in tpos.items():
    isroot = (nid == 'u')
    on = nid in ('u', 'ua', 'uab')
    axt.scatter([px], [py], s=620,
                color=COL['accent'] if isroot else (COL['pos'] if on else COL['lyr1']),
                zorder=6, edgecolors='white', linewidths=1.6)
    axt.text(px, py, labtxt, ha='center', va='center', fontsize=8.2,
             color='white', zorder=7, family='monospace')
axt.set_xlim(-0.5, 3.7); axt.set_ylim(-0.6, 3.4); axt.axis('off')
axt.set_title(r"$T(G,u)$: lift $u\rightarrow ua\rightarrow uab\rightarrow ua\rightarrow u$",
              fontsize=10.5, pad=6)

# projection arrow in the clear gap, upper-middle
fig.patches.append(FancyArrowPatch((0.455, 0.72), (0.35, 0.72), transform=fig.transFigure,
                   arrowstyle='-|>', mutation_scale=18, lw=1.6, color=COL['grey']))
fig.text(0.402, 0.76, r"project $\pi$", fontsize=11, color=COL['grey'], ha='center', va='center')

# legend
from matplotlib.lines import Line2D
leg = [Line2D([0], [0], color=COL['pos'], lw=2.6, label='extend (push: fresh vertex)'),
       Line2D([0], [0], color=COL['accent'], lw=2.6, label='retreat (pop: to parent)')]
axg.legend(handles=leg, loc='lower center', bbox_to_anchor=(0.5, -0.18),
           fontsize=8.2, frameon=False, ncol=1)

save(fig, "pt_fig1_bijection")
