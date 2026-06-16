#!/usr/bin/env python3
"""
Figure for "Counting with the Derivative Tower" (Budan-Fourier in Lean 4):
the ANATOMY OF A CRITICAL POINT -- the heart of `fourierVar_drop_at_critical_point`.

At a critical point c, a whole BLOCK of consecutive tower members may vanish
(here p and p' both vanish at the double root c=1 of p_A=(x-1)^2(x+1), a block of
length m=2 = the root multiplicity).  The two monotonicity bricks of the
formalization fix every sign just off c from the member listed just BELOW it
(its derivative p^(k+1)):

  * RIGHT of c  (z = c^+): a vanishing member COPIES the sign of its derivative
    (the member below it).  The block collapses to a single sign -> 0 new sign
    variations.  Hence V(c^+) = V(b): the right side carries no information.

  * LEFT of c   (z = c^-): a vanishing member takes the OPPOSITE sign of the one
    below it.  The block fully ALTERNATES -> exactly m sign variations.

So V(c^-) - V(c^+) = m (plus an even amount from interior blocks), which is the
additive existential `V(a) = V(b) + #roots + 2e` proved sorry-free in Lean.

Signs are taken from the EXACT tower of p_A at 1/2, 1, 3/2 (verified by sympy).
Run: python budan_fig2_critical.py
"""
import sympy as sp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, Rectangle

TEAL = "#1B6F8C"
AMBER = "#E08A1E"
PLUM = "#7B4B94"
GREY = "#8A8A8A"

x = sp.symbols("x")
pA = sp.expand((x - 1) ** 2 * (x + 1))
seq = [pA]
for _ in range(3):
    seq.append(sp.diff(seq[-1], x))


def sgn(e, t):
    v = sp.nsimplify(e.subs(x, t))
    return "+" if v > 0 else ("-" if v < 0 else "0")


left = [sgn(e, sp.Rational(1, 2)) for e in seq]   # c^-
atc = [sgn(e, sp.Integer(1)) for e in seq]        # c
right = [sgn(e, sp.Rational(3, 2)) for e in seq]  # c^+
assert left == ["+", "-", "+", "+"], left
assert atc == ["0", "0", "+", "+"], atc
assert right == ["+", "+", "+", "+"], right


def Vof(cols):
    s = [v for v in cols if v != "0"]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


assert Vof(left) == 2 and Vof(right) == 0, (Vof(left), Vof(right))
print("c^- signs", left, "V =", Vof(left))
print("c   signs", atc)
print("c^+ signs", right, "V =", Vof(right))
print("V(c^-) - V(c^+) =", Vof(left) - Vof(right), "= multiplicity m = 2")

# ----------------------------------------------------------------------------
labels = [r"$p$", r"$p'$", r"$p''$", r"$p'''$"]
cols = {"$c^-$ (left)": left, "$c$": atc, "$c^+$ (right)": right}
colx = {"$c^-$ (left)": 0.0, "$c$": 1.6, "$c^+$ (right)": 3.2}
colcolor = {"$c^-$ (left)": PLUM, "$c$": GREY, "$c^+$ (right)": TEAL}

fig, ax = plt.subplots(figsize=(8.6, 5.0))
ax.set_xlim(-1.5, 5.0)
ax.set_ylim(-1.9, 4.4)
ax.axis("off")

# member labels (rows), top = p, going down the tower
ytop = 3.6
dy = 1.0
yof = lambda i: ytop - i * dy
for i, lab in enumerate(labels):
    ax.text(-1.2, yof(i), lab, fontsize=13, color="black", va="center", ha="left")

# the vanishing block bracket (members 0,1 vanish at c)
ax.add_patch(Rectangle((-0.85, yof(1) - 0.4), 0.0, 0.0))  # no-op to keep axis
ax.annotate("", xy=(-0.75, yof(0) + 0.32), xytext=(-0.75, yof(1) - 0.32),
            arrowprops=dict(arrowstyle="-", color=AMBER, lw=2.2))
ax.text(-0.95, (yof(0) + yof(1)) / 2, r"block" "\n" r"$m=2$", color=AMBER,
        fontsize=9, va="center", ha="right", rotation=0)

# column headers + sign cells
for name, col in cols.items():
    cx = colx[name]
    cc = colcolor[name]
    ax.text(cx, ytop + 0.7, name, fontsize=12, color=cc, ha="center", fontweight="bold")
    for i, s in enumerate(col):
        face = "white"
        if s == "0":
            txt, tc = "0", GREY
        elif s == "+":
            txt, tc = "$+$", cc
        else:
            txt, tc = "$-$", cc
        ax.text(cx, yof(i), txt, fontsize=15, color=tc, ha="center", va="center",
                bbox=dict(boxstyle="round,pad=0.28", fc=face, ec=cc, lw=1.3))

# arrows: LEFT side -> alternation (opposite of the one below)
for i in (0, 1):  # vanishing members copy-with-flip from the one below
    ax.add_patch(FancyArrowPatch((colx["$c$"] - 0.32, yof(i)), (colx["$c^-$ (left)"] + 0.34, yof(i)),
                 arrowstyle="-|>", mutation_scale=12, color=PLUM, lw=1.4))
ax.text(colx["$c^-$ (left)"] + 0.3, -0.15,
        "vanishing member =\nOPPOSITE of sign below\n" r"$\Rightarrow$ block alternates: $V(c^-)=2$",
        color=PLUM, fontsize=8.6, ha="center", va="top")

# arrows: RIGHT side -> copy (same as the one below)
for i in (0, 1):
    ax.add_patch(FancyArrowPatch((colx["$c$"] + 0.32, yof(i)), (colx["$c^+$ (right)"] - 0.34, yof(i)),
                 arrowstyle="-|>", mutation_scale=12, color=TEAL, lw=1.4))
ax.text(colx["$c^+$ (right)"] - 0.1, -0.15,
        "vanishing member =\nSAME as sign below\n" r"$\Rightarrow$ block collapses: $V(c^+)=0$",
        color=TEAL, fontsize=8.6, ha="center", va="top")

# bottom headline
ax.text(1.6, -1.65,
        r"$V(c^-)-V(c^+) = m = 2$   (root multiplicity), plus an even surplus from interior blocks",
        fontsize=10.5, color=AMBER, ha="center")

ax.set_title("Anatomy of a critical point: the left block alternates, the right block collapses",
             fontsize=11.5, color=TEAL)

fig.savefig("budan_fig2_critical.pdf", bbox_inches="tight")
fig.savefig("budan_fig2_critical.png", dpi=150, bbox_inches="tight")
print("wrote budan_fig2_critical.{pdf,png}")
