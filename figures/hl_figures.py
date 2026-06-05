# Publication-quality figures for the Heilmann-Lieb (Paper II) document.
# Palette: teal #1B6F8C, amber #E08A1E, band #DCE7EB.  Vector PDF output.
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
import networkx as nx

TEAL="#1B6F8C"; AMBER="#E08A1E"; BAND="#DCE7EB"; DARK="#15303a"; GREY="#9aa7ad"
plt.rcParams.update({
    "font.family":"serif","font.serif":["DejaVu Serif"],
    "mathtext.fontset":"dejavuserif","font.size":12,
    "axes.edgecolor":DARK,"axes.linewidth":0.9,"savefig.bbox":"tight","savefig.pad_inches":0.05,
})
OUT="/tmp/figs/"
import os; os.makedirs(OUT,exist_ok=True)

# ---- matching polynomial (numpy coeffs) ----
def matching_counts(edges, n):
    cnt={}
    def rec(s,used,k):
        cnt[k]=cnt.get(k,0)+1
        for i in range(s,len(edges)):
            a,b=edges[i]
            if a not in used and b not in used:
                used.add(a);used.add(b);rec(i+1,used,k+1);used.discard(a);used.discard(b)
    rec(0,set(),0); return cnt
def matching_poly_np(edges,n):
    cnt=matching_counts(edges,n); coeffs=[0.0]*(n+1)
    for k,c in cnt.items(): coeffs[n-2*k]+=((-1)**k)*c    # x^{n-2k}
    return np.array(coeffs[::-1])  # highest-first for np.roots? build poly value
def mpoly_val(edges,n,xs):
    cnt=matching_counts(edges,n); y=np.zeros_like(xs)
    for k,c in cnt.items(): y=y+((-1)**k)*c*xs**(n-2*k)
    return y
def mpoly_roots(edges,n):
    cnt=matching_counts(edges,n); coeff=np.zeros(n+1)  # index = power
    for k,c in cnt.items(): coeff[n-2*k]+=((-1)**k)*c
    r=np.roots(coeff[::-1])
    return sorted(float(z.real) for z in r if abs(z.imag)<1e-7)

# Petersen graph for the headline band figure
P=nx.petersen_graph()
pe=[(u,v) for u,v in P.edges()]; pn=P.number_of_nodes()
Delta=max(dict(P.degree()).values()); q=Delta-1; B=2*math.sqrt(q)

# ============ FIG 1 : the Ramanujan band (headline) ============
fig,ax=plt.subplots(figsize=(7.4,3.4))
xs=np.linspace(-B-0.7,B+0.7,1400); ys=mpoly_val(pe,pn,xs)
ys=ys/np.max(np.abs(ys))  # normalize for display
ax.axvspan(-B,B,color=BAND,zorder=0)
ax.axhline(0,color=GREY,lw=0.8,zorder=1)
ax.plot(xs,ys,color=TEAL,lw=2.0,zorder=3)
rts=mpoly_roots(pe,pn)
ax.scatter(rts,[0]*len(rts),color=AMBER,s=46,zorder=5,edgecolor=DARK,linewidth=0.6)
for xb,lab in [(-B,r"$-2\sqrt{\Delta-1}$"),(B,r"$+2\sqrt{\Delta-1}$")]:
    ax.axvline(xb,color=AMBER,ls="--",lw=1.3,zorder=4)
    ax.text(xb,1.08,lab,ha="center",va="bottom",color=AMBER,fontsize=11)
ax.set_yticks([]); ax.set_ylim(-1.15,1.25); ax.set_xlim(xs[0],xs[-1])
ax.set_xlabel(r"$x$")
ax.text(0,-0.95,r"roots of $\mu_G(x)$",ha="center",color=AMBER,fontsize=11)
ax.set_title(r"Heilmann--Lieb: every root of $\mu_G$ lies in $[-2\sqrt{\Delta-1},\,2\sqrt{\Delta-1}]$",
             fontsize=12.5,color=DARK,pad=8)
for s in ["top","right","left"]: ax.spines[s].set_visible(False)
fig.savefig(OUT+"fig1_band.pdf"); plt.close(fig)

# ============ helper: build path tree of small graph ============
def path_tree(adj, root):
    # nodes = tuples (vertex-simple paths from root); edges connect path to its 1-step extension
    nodes=[(root,)]; edges=[]; frontier=[(root,)]
    while frontier:
        nf=[]
        for p in frontier:
            last=p[-1]
            for w in adj[last]:
                if w not in p:
                    q=p+(w,); nodes.append(q); edges.append((p,q)); nf.append(q)
        frontier=nf
    return nodes,edges

# ============ FIG 2 : unfolding G into the path tree T(G,u) ============
# paw graph: triangle 0-1-2 + pendant 3 on 0; root u=3
adj={0:[1,2,3],1:[0,2],2:[0,1],3:[0]}
Gp=nx.Graph();
for a in adj:
    for b in adj[a]:
        if a<b: Gp.add_edge(a,b)
nodes,tedges=path_tree(adj,3)
fig,(axL,axR)=plt.subplots(1,2,figsize=(8.6,3.7),gridspec_kw={"width_ratios":[1,1.5]})
# left: G
posG={0:(0,0),1:(-0.8,0.9),2:(0.8,0.9),3:(0,-1.0)}
nx.draw_networkx_edges(Gp,posG,ax=axL,edge_color=TEAL,width=2)
nx.draw_networkx_nodes(Gp,posG,ax=axL,node_color="white",edgecolors=TEAL,linewidths=2,node_size=560)
nx.draw_networkx_nodes(Gp,posG,nodelist=[3],ax=axL,node_color=AMBER,edgecolors=DARK,linewidths=1.5,node_size=560)
nx.draw_networkx_labels(Gp,posG,ax=axL,font_size=12,font_color=DARK)
axL.set_title(r"$G$  (root $u$ amber)",fontsize=12,color=DARK); axL.axis("off")
# right: path tree (hierarchical layout by depth)
T=nx.Graph(); T.add_edges_from([(str(a),str(b)) for a,b in tedges])
depth={n:len(n)-1 for n in nodes}
bylevel={}
for n in nodes: bylevel.setdefault(depth[n],[]).append(n)
posT={}
for d,ns in bylevel.items():
    m=len(ns)
    for i,n in enumerate(sorted(ns)):
        posT[str(n)]=((i-(m-1)/2)*1.5, -d*1.0)
lbl={str(n):"".join(str(v) for v in n) for n in nodes}
nx.draw_networkx_edges(T,posT,ax=axR,edge_color=TEAL,width=1.8)
nx.draw_networkx_nodes(T,posT,ax=axR,node_color="white",edgecolors=TEAL,linewidths=1.8,node_size=620)
nx.draw_networkx_nodes(T,posT,nodelist=[str((3,))],ax=axR,node_color=AMBER,edgecolors=DARK,linewidths=1.5,node_size=620)
nx.draw_networkx_labels(T,posT,labels=lbl,ax=axR,font_size=9.5,font_color=DARK)
axR.set_title(r"path tree $T(G,u)$   $\Rightarrow\ \mu_G \mid \mu_{T(G,u)}$",fontsize=12,color=DARK); axR.axis("off")
fig.savefig(OUT+"fig2_pathtree.pdf"); plt.close(fig)

# ============ FIG 3 : the geometric weight and why 2 sqrt(q) ============
fig,ax=plt.subplots(figsize=(7.6,3.8))
# a small rooted tree, branching factor q=2 (Delta=3); weight s^{-depth}, s=sqrt(q)
q3=2; s=math.sqrt(q3)
# positions: root depth0, then 2 children depth1, each 2 children depth2
levels={0:[(0,0)],1:[(-2,-1),(2,-1)],2:[(-3,-2),(-1,-2),(1,-2),(3,-2)]}
coords={}; idx=0
edges3=[]
coords[("r",)] = (0,0)
# build manually
nodesP={"r":(0,0),"a":(-2,-1),"b":(2,-1),"aa":(-3.1,-2),"ab":(-0.9,-2),"ba":(0.9,-2),"bb":(3.1,-2)}
edges3=[("r","a"),("r","b"),("a","aa"),("a","ab"),("b","ba"),("b","bb")]
dep={"r":0,"a":1,"b":1,"aa":2,"ab":2,"ba":2,"bb":2}
for u,v in edges3:
    x1,y1=nodesP[u]; x2,y2=nodesP[v]
    ax.plot([x1,x2],[y1,y2],color=TEAL,lw=1.8,zorder=1)
for nm,(x,y) in nodesP.items():
    w=s**(-dep[nm]); sz=300+1500*w/ (s**0)   # size ~ weight
    ax.scatter([x],[y],s=380*(w**0.8)+120,color="white",edgecolors=TEAL,linewidths=1.8,zorder=2)
    ax.text(x,y+0.0,r"$s^{-%d}$"%dep[nm],ha="center",va="center",fontsize=9.5,color=DARK,zorder=3)
ax.scatter([0],[0],s=420,color=AMBER,edgecolors=DARK,linewidths=1.4,zorder=1.5)
ax.text(0,0,r"$1$",ha="center",va="center",fontsize=10,color=DARK,zorder=3)
# annotation of the balance at an internal vertex 'a'
ax.annotate("", xy=(-2,-1.0), xytext=(-0.2,0.55),
            arrowprops=dict(arrowstyle="->",color=AMBER,lw=1.4))
ax.text(-0.15,0.62,r"row sum at $v$:  $1\cdot s + q\cdot\frac{1}{s} = s+\frac{q}{s}=2\sqrt{q}$",
        ha="left",va="bottom",fontsize=11,color=DARK,
        bbox=dict(boxstyle="round,pad=0.4",fc=BAND,ec=TEAL,lw=1))
ax.text(-0.15,0.40,r"(1 parent $\times\,s$,  $\leq q$ children $\times\,1/s$)",
        ha="left",va="top",fontsize=9.5,color=TEAL)
ax.text(0,-2.75,r"weight $w_v=(\sqrt{\Delta-1})^{-\mathrm{dist}(r,v)}$,"
        r"  $s=\sqrt{\Delta-1}=\sqrt{q}$:  branching $q$ balanced by decay $\sqrt{q}$ per level",
        ha="center",fontsize=10.5,color=DARK)
ax.set_xlim(-4,4.2); ax.set_ylim(-3.1,1.0); ax.axis("off")
ax.set_title(r"Why the ceiling is exactly $2\sqrt{\Delta-1}$ (weighted Gershgorin on the tree)",
             fontsize=12.5,color=DARK)
fig.savefig(OUT+"fig3_weight.pdf"); plt.close(fig)

# ============ FIG 4 : roots(mu_G) subset roots(mu_T) subset band ============
# G = paw (triangle+pendant); T = its path tree from u=3
pawe=[(0,1),(1,2),(2,0),(0,3)]; pawn=4
rG=mpoly_roots(pawe,pawn)
# path tree edges (as integer-labeled): nodes->index
nidx={n:i for i,n in enumerate(nodes)}
te_int=[(nidx[a],nidx[b]) for a,b in tedges]
rT=mpoly_roots(te_int,len(nodes))
Dp=max(dict(Gp.degree()).values()); qp=Dp-1; Bp=2*math.sqrt(qp)
fig,ax=plt.subplots(figsize=(7.4,2.6))
ax.axvspan(-Bp,Bp,color=BAND,zorder=0)
ax.axhline(0.0,color=GREY,lw=0.8)
ax.scatter(rT,[0.16]*len(rT),color=TEAL,s=70,zorder=4,label=r"roots of $\mu_{T(G,u)}$",edgecolor=DARK,linewidth=0.5)
ax.scatter(rG,[-0.16]*len(rG),color=AMBER,s=70,zorder=5,label=r"roots of $\mu_G$",edgecolor=DARK,linewidth=0.5)
for xb in (-Bp,Bp): ax.axvline(xb,color=AMBER,ls="--",lw=1.2)
ax.text(Bp,0.42,r"$2\sqrt{\Delta-1}$",ha="center",color=AMBER,fontsize=10)
ax.set_ylim(-0.55,0.6); ax.set_yticks([]); ax.set_xlim(-Bp-0.5,Bp+0.5); ax.set_xlabel(r"$x$")
ax.legend(loc="lower center",ncol=2,frameon=False,fontsize=10,bbox_to_anchor=(0.5,-0.55))
for sp in ["top","right","left"]: ax.spines[sp].set_visible(False)
ax.set_title(r"$\mathrm{roots}(\mu_G)\subseteq\mathrm{roots}(\mu_{T(G,u)})\subseteq[-2\sqrt{\Delta-1},2\sqrt{\Delta-1}]$",
             fontsize=12,color=DARK,pad=6)
fig.savefig(OUT+"fig4_nested.pdf"); plt.close(fig)

# ============ FIG 5 : circle and shadow (Joukowski) ============
fig,(axc,axi)=plt.subplots(1,2,figsize=(8.4,3.6),gridspec_kw={"width_ratios":[1,1.1]})
q5=2; s5=1/math.sqrt(q5); B5=2*math.sqrt(q5)
th=np.linspace(0,2*np.pi,400)
axc.plot(s5*np.cos(th),s5*np.sin(th),color=TEAL,lw=2)
axc.axhline(0,color=GREY,lw=0.7); axc.axvline(0,color=GREY,lw=0.7)
thp=[0.6,2.1,3.9,5.0]
for t in thp:
    axc.scatter([s5*math.cos(t)],[s5*math.sin(t)],color=AMBER,s=42,zorder=5,edgecolor=DARK,linewidth=0.5)
    axc.scatter([s5*math.cos(-t)],[s5*math.sin(-t)],color=AMBER,s=42,zorder=5,edgecolor=DARK,linewidth=0.5)
axc.set_aspect("equal"); axc.set_title(r"critical circle $|u|=1/\sqrt{q}$",fontsize=11.5,color=DARK)
axc.text(0,s5+0.07,r"$u$",ha="center",color=TEAL); axc.axis("off")
# shadow: interval [-B,B], lambda = 2 sqrt(q) cos theta
axi.axhline(0,color=GREY,lw=0.8)
axi.axvspan(-B5,B5,ymin=0.42,ymax=0.58,color=BAND)
for t in thp:
    lam=B5*math.cos(t)
    axi.scatter([lam],[0],color=AMBER,s=46,zorder=5,edgecolor=DARK,linewidth=0.5)
for xb,l in [(-B5,r"$-2\sqrt{q}$"),(B5,r"$2\sqrt{q}$")]:
    axi.axvline(xb,color=AMBER,ls="--",lw=1.2); axi.text(xb,0.16,l,ha="center",color=AMBER,fontsize=10)
axi.set_ylim(-0.3,0.3); axi.set_yticks([]); axi.set_xlim(-B5-0.5,B5+0.5)
axi.set_title(r"shadow $\lambda=u+q/u=2\sqrt{q}\,\cos\theta$",fontsize=11.5,color=DARK)
for sp in ["top","right","left"]: axi.spines[sp].set_visible(False)
fig.suptitle(r"The band is the Joukowski shadow of the critical circle (conjugate pairs $u,\bar u$)",
             fontsize=12.5,color=DARK,y=1.02)
fig.savefig(OUT+"fig5_joukowski.pdf"); plt.close(fig)

# ============ numerical table data ============
print("=== TABLE 2 data: graph | n | Delta | band 2sqrt(Delta-1) | max|root mu| | in band ===")
def stat(name,Gx):
    e=[(u,v) for u,v in Gx.edges()]; n=Gx.number_of_nodes()
    D=max(dict(Gx.degree()).values()); B=2*math.sqrt(D-1)
    r=mpoly_roots(e,n); mr=max(abs(x) for x in r)
    print("%-16s & %d & %d & %.4f & %.4f & %s \\\\"%(name,n,D,B,mr,"yes" if mr<=B+1e-9 else "NO"))
stat("path $P_6$",nx.path_graph(6))
stat("cycle $C_6$",nx.cycle_graph(6))
stat("star $K_{1,5}$",nx.star_graph(5))
stat("complete $K_5$",nx.complete_graph(5))
stat("Petersen",nx.petersen_graph())
stat("$3$-cube $Q_3$",nx.hypercube_graph(3))
print("DONE")
print(os.listdir(OUT))
