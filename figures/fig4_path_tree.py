"""Figure 4 — Godsil's path-tree T(G,u), the proposed next step (Section: proposal).

Left:  the diamond G = K4 minus an edge, root u highlighted.
Right: its path-tree T(G,u) — vertices are the paths of G starting at u,
       joined when one extends the other by an edge. T is a forest, so on it
       the matching polynomial equals the characteristic polynomial; and
       mu_G divides mu_{T(G,u)}. Those two facts give Heilmann-Lieb.
This construction is PROPOSED, not yet formalized (honest scope).
"""
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()

# ---------- left: the diamond graph G ----------
gpos = {'u':(0,1.0), 'a':(-1.0,0.0), 'b':(1.0,0.0), 'c':(0,-1.0)}
gedges = [('u','a'),('u','b'),('a','b'),('a','c'),('b','c')]

# ---------- right: the path-tree T(G,u) ----------
# node id -> (label, x, y); paths from u, no repeated vertex
tpos = {
    'u'   : ('u',        1.60, 3.0),
    'ua'  : ('ua',       0.50, 2.0),
    'ub'  : ('ub',       2.70, 2.0),
    'uab' : ('uab',      0.00, 1.0),
    'uac' : ('uac',      1.00, 1.0),
    'uba' : ('uba',      2.20, 1.0),
    'ubc' : ('ubc',      3.20, 1.0),
    'uabc': ('uabc',     0.00, 0.0),
    'uacb': ('uacb',     1.00, 0.0),
    'ubac': ('ubac',     2.20, 0.0),
    'ubca': ('ubca',     3.20, 0.0),
}
tedges = [('u','ua'),('u','ub'),
          ('ua','uab'),('ua','uac'),('ub','uba'),('ub','ubc'),
          ('uab','uabc'),('uac','uacb'),('uba','ubac'),('ubc','ubca')]

fig = plt.figure(figsize=(9.4,4.0))
gs = fig.add_gridspec(1, 2, width_ratios=[1.0, 2.05], wspace=0.08)

# --- left panel ---
axg = fig.add_subplot(gs[0,0])
for i,j in gedges:
    (x0,y0),(x1,y1)=gpos[i],gpos[j]
    axg.plot([x0,x1],[y0,y1], color=COL['pos'], lw=2.6, solid_capstyle='round', zorder=1)
for v,(px,py) in gpos.items():
    isroot = (v=='u')
    axg.scatter([px],[py], s=320 if isroot else 230,
                color=COL['accent'] if isroot else COL['node'],
                zorder=3, edgecolors='white', linewidths=1.5)
    axg.text(px,py, v, ha='center', va='center', fontsize=10,
             color='white', zorder=4, family='monospace')
axg.set_xlim(-1.5,1.5); axg.set_ylim(-1.45,1.45); axg.set_aspect('equal'); axg.axis('off')
axg.set_title(r"$G$ = diamond, root $u$", fontsize=10.5, pad=4)

# --- right panel ---
axt = fig.add_subplot(gs[0,1])
for i,j in tedges:
    (_,x0,y0),(_,x1,y1)=tpos[i],tpos[j]
    axt.plot([x0,x1],[y0,y1], color=COL['grey'], lw=1.8, solid_capstyle='round', zorder=1)
for nid,(lab,px,py) in tpos.items():
    isroot = (nid=='u')
    axt.scatter([px],[py], s=560,
                color=COL['accent'] if isroot else COL['pos'],
                zorder=3, edgecolors='white', linewidths=1.5)
    axt.text(px,py, lab, ha='center', va='center', fontsize=8.2,
             color='white', zorder=4, family='monospace')
axt.set_xlim(-0.5,3.7); axt.set_ylim(-0.5,3.4); axt.axis('off')
axt.set_title(r"path-tree $T(G,u)$ — a forest: here $\mu_G \mid \mu_{T(G,u)}$ and $\mu_{T}=\det(xI-A_T)$",
              fontsize=10.5, pad=4)

fig.suptitle(r"The proposed next step: Heilmann–Lieb via Godsil's path-tree (mapped, not yet formalized)",
             fontsize=11.5, y=1.01)
save(fig, "fig4_path_tree")
