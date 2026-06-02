"""Figure 1 — the Godsil–Gutman identity, visualised on the triangle K3."""
import numpy as np, sympy as sp, networkx as nx, itertools
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()
x = sp.symbols('x')

# K3 vertices on a triangle
pos = {0:(0,1.0), 1:(-0.87,-0.5), 2:(0.87,-0.5)}
edges = [(0,1),(1,2),(0,2)]

def charpoly_signed(signs):
    A = sp.zeros(3,3)
    for (i,j),s in zip(edges,signs):
        A[i,j]=s; A[j,i]=s
    return sp.expand((x*sp.eye(3)-A).det())

def draw_signed(ax, signs, title):
    for (i,j),s in zip(edges,signs):
        col = COL['pos'] if s==1 else COL['neg']
        ls  = '-' if s==1 else (0,(4,2))
        (x0,y0),(x1,y1)=pos[i],pos[j]
        ax.plot([x0,x1],[y0,y1], color=col, lw=2.6, ls=ls, solid_capstyle='round', zorder=1)
    for v,(px,py) in pos.items():
        ax.scatter([px],[py], s=210, color=COL['node'], zorder=3, edgecolors='white', linewidths=1.4)
    ax.set_xlim(-1.25,1.25); ax.set_ylim(-0.95,1.35); ax.set_aspect('equal'); ax.axis('off')
    ax.set_title(title, fontsize=10.5, pad=2)

# three representative signings: all +, one -, product -1
reps = [((1,1,1),  r"$+++$"),
        ((1,1,-1), r"$++-$"),
        ((-1,1,-1),r"$-+-$")]

fig = plt.figure(figsize=(9.2,3.5))
gs = fig.add_gridspec(1, 5, width_ratios=[1,1,1,0.55,1.55], wspace=0.25)
for k,(signs,lab) in enumerate(reps):
    ax = fig.add_subplot(gs[0,k])
    draw_signed(ax, signs, None)
    cp = charpoly_signed(signs)
    ax.text(0,-1.28, lab+r":  $"+sp.latex(cp)+r"$", ha='center', va='top', fontsize=9.2)

# averaging arrow
axa = fig.add_subplot(gs[0,3]); axa.axis('off')
axa.annotate("", xy=(0.95,0.5), xytext=(0.05,0.5), xycoords='axes fraction',
             arrowprops=dict(arrowstyle='-|>', lw=2.2, color=COL['accent']))
axa.text(0.5,0.66, r"$2^{-|E|}\!\sum_{\text{signings}}$", ha='center', va='bottom', fontsize=10.5, color=COL['accent'])
axa.text(0.5,0.34, r"(all $2^{3}$)", ha='center', va='top', fontsize=8.5, color=COL['grey'])

# result: matching polynomial
axr = fig.add_subplot(gs[0,4]); axr.axis('off')
mpoly = x**3 - 3*x  # matchingPoly(K3) = sum_k (-1)^k m_k x^{n-2k} = x^3 - 3x
axr.add_patch(plt.Rectangle((0.02,0.30),0.96,0.46, transform=axr.transAxes,
              facecolor=COL['band'], edgecolor=COL['pos'], lw=1.2, zorder=0))
axr.text(0.5,0.62, r"$\mu_{K_3}(x)=x^{3}-3x$", ha='center', va='center', fontsize=12)
axr.text(0.5,0.42, "the matching polynomial", ha='center', va='center', fontsize=8.8, color=COL['grey'])
axr.text(0.5,0.12, "godsil_gutman   (Lean 4 - axioms: propext, choice, Quot.sound)",
         ha="center", va="center", fontsize=7.4, color=COL["node"], family="monospace")

fig.suptitle(r"Godsil–Gutman: the average characteristic polynomial of a random $\pm1$ signing is the matching polynomial",
             fontsize=11.5, y=1.02)
save(fig, "fig1_godsil_gutman")
