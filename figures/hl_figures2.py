# Two further figures: Kesten-McKay spectral density (why the band IS the band)
# and the MSS interlacing-family tree (the context: bounded average -> existence).
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import networkx as nx

TEAL="#1B6F8C"; AMBER="#E08A1E"; BAND="#DCE7EB"; DARK="#15303a"; GREY="#9aa7ad"
plt.rcParams.update({
    "font.family":"serif","font.serif":["DejaVu Serif"],
    "mathtext.fontset":"dejavuserif","font.size":12,
    "axes.edgecolor":DARK,"axes.linewidth":0.9,"savefig.bbox":"tight","savefig.pad_inches":0.05,
})
import os; OUT="/tmp/figs/"; os.makedirs(OUT,exist_ok=True)

# ============ FIG 6 : Kesten-McKay law -- the band is the support of the limiting density ============
d=3; q=d-1; B=2*math.sqrt(q)
G=nx.random_regular_graph(d,3000,seed=7)
A=nx.to_numpy_array(G)
ev=np.linalg.eigvalsh(A)
# theoretical Kesten-McKay density
xx=np.linspace(-B+1e-6,B-1e-6,800)
km=d*np.sqrt(np.maximum(4*q-xx**2,0))/(2*np.pi*(d*d-xx**2))
fig,ax=plt.subplots(figsize=(7.6,3.7))
ax.axvspan(-B,B,color=BAND,zorder=0)
# histogram of the non-trivial spectrum (exclude the Perron eigenvalue d)
nontriv=ev[ev< d-1e-6]
ax.hist(nontriv,bins=70,density=True,color=TEAL,alpha=0.45,zorder=2,
        edgecolor="white",linewidth=0.3,label="eigenvalues of a random $3$-regular graph")
ax.plot(xx,km,color=DARK,lw=2.2,zorder=4,label="Kesten--McKay density $f_d$")
for xb,l in [(-B,r"$-2\sqrt{d-1}$"),(B,r"$2\sqrt{d-1}$")]:
    ax.axvline(xb,color=AMBER,ls="--",lw=1.4,zorder=5); ax.text(xb,0.40,l,ha="center",color=AMBER,fontsize=11)
# the trivial (Perron) eigenvalue d, sitting outside the band
ax.scatter([d],[0.012],color=AMBER,s=60,zorder=6,edgecolor=DARK,linewidth=0.6)
ax.annotate(r"trivial eigenvalue $d$ (outside the band)",xy=(d,0.012),xytext=(d-0.1,0.20),
            ha="center",fontsize=9.5,color=DARK,
            arrowprops=dict(arrowstyle="->",color=DARK,lw=1))
ax.set_xlim(-B-0.45,d+0.45); ax.set_ylim(0,0.46); ax.set_xlabel(r"$x$"); ax.set_ylabel("density")
ax.legend(loc="upper left",frameon=False,fontsize=9.8)
for s in ["top","right"]: ax.spines[s].set_visible(False)
ax.set_title(r"The band is the support of the limiting spectral density (Kesten--McKay)",
             fontsize=12.5,color=DARK,pad=8)
fig.savefig(OUT+"fig6_kestenmckay.pdf"); plt.close(fig)
print("fig6 eig range:",round(float(nontriv.min()),3),round(float(nontriv.max()),3),"band",round(B,3))

# ============ FIG 7 : the interlacing-family tree (MSS context) ============
fig,ax=plt.subplots(figsize=(7.8,3.9))
# depth-2 binary tree of conditional expected characteristic polynomials
nodes={"":(0,2),"+":(-2.6,1),"-":(2.6,1),
       "++":(-3.6,0),"+-":(-1.6,0),"-+":(1.6,0),"--":(3.6,0)}
edges=[("","+"),("","-"),("+","++"),("+","+-"),("-","-+"),("-","--")]
labels={"":r"$\mu_G=\mathbb{E}[\chi_s]$","+":r"$\mathbb{E}[\chi_s\mid s_1{=}{+}]$",
        "-":r"$\mathbb{E}[\chi_s\mid s_1{=}{-}]$",
        "++":r"$\chi_{++}$","+-":r"$\chi_{+-}$","-+":r"$\chi_{-+}$","--":r"$\chi_{--}$"}
for a,b in edges:
    ax.plot([nodes[a][0],nodes[b][0]],[nodes[a][1],nodes[b][1]],color=TEAL,lw=1.6,zorder=1)
for k,(x,y) in nodes.items():
    isleaf=len(k)==2
    fc = AMBER if k=="" else ("white")
    ax.scatter([x],[y],s=300,color=fc,edgecolors=DARK if k=="" else TEAL,
               linewidths=1.6,zorder=2)
    ax.text(x,y-0.30,labels[k],ha="center",va="top",fontsize=8.6 if not isleaf else 9,color=DARK)
ax.text(0,2.40,r"root $=$ matching polynomial (roots in the band, this paper)",
        ha="center",fontsize=10,color=AMBER)
ax.text(0,-0.62,r"leaves $=$ actual $\pm1$ signings $=$ $2$-lifts",ha="center",fontsize=10,color=DARK)
ax.annotate("",xy=(3.6,-0.05),xytext=(0,1.85),arrowprops=dict(arrowstyle="->",color=GREY,lw=1.2,ls=":"))
ax.text(2.0,1.25,r"interlacing family $\Rightarrow$ some leaf has"+"\n"+r"max-root $\leq$ root's max-root",
        ha="left",fontsize=9.5,color=DARK,bbox=dict(boxstyle="round,pad=0.35",fc=BAND,ec=TEAL,lw=1))
ax.set_xlim(-4.4,4.6); ax.set_ylim(-1.1,2.7); ax.axis("off")
ax.set_title(r"Why the band matters: the matching polynomial is the root of an interlacing family",
             fontsize=12,color=DARK)
fig.savefig(OUT+"fig7_interlacing.pdf"); plt.close(fig)
print("DONE", os.listdir(OUT))
