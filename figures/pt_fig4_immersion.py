"""Part III, Figure 4 — why pi separates neighbours (the path tree is an
immersion, not a covering).

Sitting on the path-tree vertex p = (u,a,b) -- the simple path u-a-b, drawn in
teal on G = K4 -- the next step looks at the neighbours of its endpoint b. In
G, b is adjacent to a, c and u. Each falls into exactly one case:
  * a = penultimate of the path  -> the PARENT lift (retreat), exists;
  * c = fresh, not on the path    -> a CHILD lift (extend), exists;
  * u = on the path but NOT the parent -> BLOCKED: no lift above p.
So pi is injective on the neighbours of p (parents unique, children unique,
the two families separated by on/off the path), but not surjective -- the
blocked direction is why the path tree is an immersion, and is exactly what
makes a projected walk tree-like.
"""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from fig_style import setup, save, COL
setup()

gpos = {'u': (0, 1.15), 'a': (-1.15, 0.0), 'b': (1.15, 0.0), 'c': (0, -1.15)}
gedges = [('u', 'a'), ('u', 'b'), ('a', 'b'), ('a', 'c'), ('b', 'c')]
path_edges = [('u', 'a'), ('a', 'b')]     # the current simple path u-a-b

fig, ax = plt.subplots(figsize=(7.4, 5.0))

# base graph (faint)
for i, j in gedges:
    (x0, y0), (x1, y1) = gpos[i], gpos[j]
    ax.plot([x0, x1], [y0, y1], color=COL['band'], lw=4.5, solid_capstyle='round', zorder=1)
# the path u-a-b (teal)
for i, j in path_edges:
    (x0, y0), (x1, y1) = gpos[i], gpos[j]
    ax.plot([x0, x1], [y0, y1], color=COL['pos'], lw=4.0, solid_capstyle='round', zorder=2)

# the three rays out of b, classified
rays = {
    'a': ('parent  (penultimate)\nretreat lift', COL['accent'], '-'),
    'c': ('child  (fresh)\nextend lift', COL['pos'], '-'),
    'u': ('blocked  (on path,\nnot parent): no lift', COL['grey'], (0, (4, 3))),
}
for tgt, (lab, col, ls) in rays.items():
    (xb, yb), (xt, yt) = gpos['b'], gpos[tgt]
    arr = FancyArrowPatch((xb, yb), (xt, yt), arrowstyle='-|>', mutation_scale=16,
                          lw=2.6, color=col, ls=ls, zorder=5, shrinkA=16, shrinkB=16)
    ax.add_patch(arr)

# nodes
for v, (px, py) in gpos.items():
    onpath = v in ('u', 'a', 'b')
    ax.scatter([px], [py], s=430 if v == 'b' else 320,
               color=COL['node'] if onpath else COL['grey'],
               zorder=6, edgecolors=(COL['pos'] if onpath else 'white'),
               linewidths=2.4 if onpath else 1.4)
    ax.text(px, py, v, ha='center', va='center', fontsize=12, color='white',
            zorder=7, family='monospace')

# labels for the three cases (placed near each target)
ax.text(-1.95, 0.42, rays['a'][0], ha='center', va='center', fontsize=8.6,
        color=COL['accent'])
ax.text(0.0, -1.95, rays['c'][0], ha='center', va='center', fontsize=8.6, color=COL['pos'])
ax.text(0.02, 1.92, rays['u'][0], ha='center', va='center', fontsize=8.6, color=COL['grey'])

ax.text(-0.66, 0.74, r'path $\langle uab\rangle$', ha='center', va='center', fontsize=9.2,
        color=COL['pos'], rotation=0, style='italic')

ax.set_xlim(-2.8, 2.4); ax.set_ylim(-2.4, 2.4); ax.set_aspect('equal'); ax.axis('off')
ax.set_title(r'On $p=\langle uab\rangle$: $\pi$ separates the neighbours of $b$'
             '\n(an immersion, not a covering)', fontsize=11, pad=2)

save(fig, "pt_fig4_immersion")
