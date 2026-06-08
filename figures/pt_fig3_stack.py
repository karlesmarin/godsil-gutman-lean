"""Part III, Figure 3 — IsTreeLike as a stack discipline (the liftSeq predicate).

The closed walk  u a b a u  of the diamond, read left to right, threading the
current simple path from u as a STACK. Each next vertex either:
  * EXTEND (teal):  not on the stack -> push it;
  * RETREAT (amber): equals the penultimate -> pop.
The walk is tree-like iff the stack ends back at [u]. The stack at step i is
exactly the path-tree vertex the lift sits on (Section 'the liftSeq<->path
invariant'): u, ua, uab, ua, u.
"""
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
from fig_style import setup, save, COL
setup()

# stacks after reading u, a, b, a, u  (bottom = root u)
stacks = [['u'], ['u', 'a'], ['u', 'a', 'b'], ['u', 'a'], ['u']]
# transition (next vertex read, kind) between consecutive stacks
trans = [('a', 'ext'), ('b', 'ext'), ('a', 'ret'), ('u', 'ret')]
tree_label = ['u', 'ua', 'uab', 'ua', 'u']     # path-tree vertex = stack as a word

fig, ax = plt.subplots(figsize=(9.6, 3.7))
bw, bh, gap = 0.74, 0.62, 2.05          # box width/height, column gap
y0 = 0.0

for col, st in enumerate(stacks):
    x = col * gap
    # draw the stack of boxes
    for lvl, v in enumerate(st):
        isroot = (lvl == 0)
        fc = COL['accent'] if isroot else COL['pos']
        box = FancyBboxPatch((x - bw / 2, y0 + lvl * bh), bw, bh * 0.86,
                             boxstyle="round,pad=0.015,rounding_size=0.08",
                             linewidth=0, facecolor=fc, zorder=2)
        ax.add_patch(box)
        ax.text(x, y0 + lvl * bh + bh * 0.43, v, ha='center', va='center',
                color='white', fontsize=12, family='monospace', zorder=3)
    # tree-vertex label under the column
    ax.text(x, y0 - 0.55, r'$\langle$' + tree_label[col] + r'$\rangle$', ha='center',
            va='center', fontsize=10, color=COL['grey'], family='monospace')
    ax.text(x, -1.05, f'step {col}', ha='center', va='center', fontsize=8.5, color=COL['grey'])

# transition arrows + labels
for col, (nxt, kind) in enumerate(trans):
    x0 = col * gap + bw / 2 + 0.06
    x1 = (col + 1) * gap - bw / 2 - 0.06
    ym = 2.55
    col_c = COL['pos'] if kind == 'ext' else COL['accent']
    ax.annotate('', xy=(x1, ym), xytext=(x0, ym),
                arrowprops=dict(arrowstyle='-|>', color=col_c, lw=2.2,
                                shrinkA=0, shrinkB=0))
    verb = f'push {nxt}' if kind == 'ext' else 'pop'
    sub = 'EXTEND' if kind == 'ext' else 'RETREAT'
    ax.text((x0 + x1) / 2, ym + 0.30, verb, ha='center', va='bottom',
            fontsize=9.5, color=col_c, family='monospace')
    ax.text((x0 + x1) / 2, ym - 0.46, f'read {nxt}\n({sub})', ha='center', va='top',
            fontsize=7.8, color=COL['grey'])

ax.text((len(stacks) - 1) * gap, 1.55,
        'ends at\n' + r'$[u]\Rightarrow$' + '\ntree-like', ha='center', va='center',
        fontsize=9.6, color=COL['pos'], style='italic')

ax.set_xlim(-0.7, (len(stacks) - 1) * gap + 0.7)
ax.set_ylim(-1.35, 3.5)
ax.axis('off')
ax.set_title(r'$\mathtt{IsTreeLike}$: the walk $u\,a\,b\,a\,u$ as a stack discipline'
             r'  (stack at step $i$ $=$ path-tree vertex)', fontsize=11, pad=4)

save(fig, "pt_fig3_stack")
