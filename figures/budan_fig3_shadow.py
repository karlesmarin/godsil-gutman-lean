#!/usr/bin/env python3
"""
Figure for "Counting with the Derivative Tower" (Budan-Fourier in Lean 4):
DESCARTES' SHADOW and the even surplus as conjugate pairs.

Budan-Fourier on (0, infinity) degenerates to Descartes' rule: the sign variations of the tower at
large x are the sign variations of the coefficients.  For p(x) = (x^2+1)(x-1) = x^3 - x^2 + x - 1
the coefficient signs are +,-,+,- (three variations), and on (0,2] the tower drop is
V(0)-V(2) = 3.  But p has only ONE real root there (x=1); the surplus 3-1 = 2 is exactly twice the
number of conjugate pairs the interval cannot see (here the single pair +-i).  The surplus is
always even because complex roots of a real polynomial come in conjugate pairs.

This figure plots the roots in the complex plane: the real root inside the interval is counted, the
conjugate pair off the axis contributes +2 to the bound.  Counts are asserted exactly (sympy).
Run: python budan_fig3_shadow.py
"""
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

TEAL = "#1B6F8C"
AMBER = "#E08A1E"
PLUM = "#7B4B94"
BAND = "#DCE7EB"

x = sp.symbols("x")
p = sp.expand((x**2 + 1) * (x - 1))
seq = [p]
for _ in range(3):
    seq.append(sp.diff(seq[-1], x))


def V(t):
    s = [sp.sign(e.subs(x, sp.nsimplify(t))) for e in seq]
    s = [v for v in s if v != 0]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


# exact assertions
assert seq[0] == x**3 - x**2 + x - 1
assert V(0) == 3 and V(2) == 0, (V(0), V(2))
assert V(0) - V(2) == 3
# one real root in (0,2], one conjugate pair: surplus = 2 = 2 * (#pairs)
roots = sp.roots(sp.Poly(p, x))
real_roots = [r for r in roots if r.is_real]
pair_roots = [r for r in roots if not r.is_real]
assert set(real_roots) == {sp.Integer(1)}
assert set(pair_roots) == {sp.I, -sp.I}
assert (V(0) - V(2)) - 1 == 2  # surplus = 2 = one conjugate pair
# Descartes shadow: coefficient sign variations = 3
coeff_signs = [int(sp.sign(c)) for c in sp.Poly(p, x).all_coeffs()]
csv = sum(1 for i in range(len(coeff_signs) - 1) if coeff_signs[i] != coeff_signs[i + 1])
assert csv == 3, csv
print("p =", p, " coeff sign variations =", csv)
print("V(0)-V(2) =", V(0) - V(2), " real roots in (0,2] = 1  -> surplus =", V(0) - V(2) - 1,
      "= 2 x (one conjugate pair)")
print("verified exactly")

# ----------------------------------------------------------------------------
fig, (axc, axb) = plt.subplots(1, 2, figsize=(9.6, 4.4),
                               gridspec_kw={"width_ratios": [1.35, 1.0], "wspace": 0.28})

# ---- left: complex plane with the roots ----
axc.axhline(0, color="0.55", lw=0.9)
axc.axvline(0, color="0.8", lw=0.7)
# interval band (0,2] on the real axis
axc.axvspan(0, 2, color=BAND, alpha=0.7, zorder=0)
axc.text(1.0, -1.55, r"interval $(0,2]$", color=TEAL, fontsize=9, ha="center")
# real root x=1 (counted)
axc.plot([1], [0], "o", color=AMBER, ms=11, zorder=5)
axc.annotate("real root\n(counted: $1$)", xy=(1, 0), xytext=(1.15, 0.7),
             color=AMBER, fontsize=9, ha="left",
             arrowprops=dict(arrowstyle="->", color=AMBER, lw=1.0))
# conjugate pair +-i (phantom, +2)
for y in (1, -1):
    axc.plot([0], [y], "D", color=PLUM, ms=9, zorder=5)
axc.annotate("conjugate pair $\\pm i$\n(unseen: $+2$ to the bound)", xy=(0, 1), xytext=(-2.4, 1.5),
             color=PLUM, fontsize=9, ha="left",
             arrowprops=dict(arrowstyle="->", color=PLUM, lw=1.0))
axc.annotate("", xy=(0, -1), xytext=(-0.55, 1.1),
             arrowprops=dict(arrowstyle="-", color=PLUM, lw=0.8, ls=":"))
axc.set_xlim(-2.6, 3.0)
axc.set_ylim(-2.0, 2.2)
axc.set_xlabel(r"$\mathrm{Re}$", fontsize=10)
axc.set_ylabel(r"$\mathrm{Im}$", fontsize=10)
axc.set_title(r"Roots of $p=(x^2+1)(x-1)$ in $\mathbb{C}$", fontsize=11, color=TEAL)
axc.set_aspect("equal", adjustable="box")
axc.grid(alpha=0.15)

# ---- right: the accounting bar ----
axb.set_xlim(0, 1)
axb.set_ylim(0, 3.6)
axb.axis("off")
# the bound = 3 as a stack: 1 (real root) + 2 (pair)
axb.bar([0.32], [1], width=0.34, bottom=0, color=AMBER, edgecolor="white")
axb.bar([0.32], [2], width=0.34, bottom=1, color=PLUM, edgecolor="white")
axb.text(0.32, 0.5, "real root\n$1$", color="white", ha="center", va="center", fontsize=9)
axb.text(0.32, 2.0, "conjugate\npair: $+2$", color="white", ha="center", va="center", fontsize=9)
# bracket = V(0)-V(2)=3
axb.annotate("", xy=(0.56, 0.02), xytext=(0.56, 3.0),
             arrowprops=dict(arrowstyle="<->", color=TEAL, lw=1.4))
axb.text(0.60, 1.5, r"$V(0)-V(2)=3$", color=TEAL, fontsize=10, rotation=90, va="center")
axb.text(0.32, 3.32, "the Budan--Fourier bound", color=TEAL, fontsize=9.5, ha="center")
axb.text(0.5, -0.05,
         "Descartes' rule is the shadow on $(0,\\infty)$:\n"
         "coeff. sign changes of $+,-,+,-$ $=3$,\n"
         "overcounting by the even number $2$.",
         color="black", fontsize=8.4, ha="center", va="top")

fig.suptitle("Descartes' shadow: the even surplus is twice the unseen conjugate pairs",
             fontsize=11.5, color=TEAL, y=1.0)
fig.savefig("budan_fig3_shadow.pdf", bbox_inches="tight")
fig.savefig("budan_fig3_shadow.png", dpi=150, bbox_inches="tight")
print("wrote budan_fig3_shadow.{pdf,png}")
