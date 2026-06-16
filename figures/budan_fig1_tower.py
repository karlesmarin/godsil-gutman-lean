#!/usr/bin/env python3
"""
Figure for "Counting with the Derivative Tower" (Budan-Fourier in Lean 4).

Two examples, two stacked panels each, contrasting the two clauses of the theorem:

  (A)  p_A(x) = (x-1)^2 (x+1):  the Fourier sign-variation count V(x) drops by
       exactly the ROOT MULTIPLICITY -- a step of 2 at the double root x=1, a
       step of 1 at the simple root x=-1.  On (-2,2] the drop V(-2)-V(2)=3
       equals the root count WITH multiplicity (the inequality is sharp).

  (B)  p_B(x) = x^2 + 1:  no real root, yet V drops by 2 at x=0 -- a critical
       point of the tower (p'=2x vanishes) that is NOT a root of p.  Here
       #roots(-2,2]=0 < V(-2)-V(2)=2, and the surplus is EVEN: the signature of
       a conjugate pair.  This is exactly the `fourierVar_drop_at_critical_point`
       case with a nonzero even witness e.

Every plotted sign and count is asserted in EXACT rational/symbolic arithmetic
(sympy) before anything is drawn.  Run: python budan_fig1_tower.py
"""
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

TEAL = "#1B6F8C"
AMBER = "#E08A1E"
PLUM = "#7B4B94"
BAND = "#DCE7EB"

x = sp.symbols("x")


def tower(p):
    """The derivative tower p, p', p'', ..., p^(deg p) (exact)."""
    P = sp.Poly(p, x)
    seq = [P.as_expr()]
    cur = P.as_expr()
    for _ in range(P.degree()):
        cur = sp.diff(cur, x)
        seq.append(cur)
    return seq


def V(seq, t):
    """exact Fourier sign-variation count of the tower at t."""
    signs = [sp.sign(e.subs(x, sp.nsimplify(t))) for e in seq]
    signs = [s for s in signs if s != 0]
    return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])


def sgn(e, t):
    v = sp.nsimplify(e.subs(x, t))
    return "+" if v > 0 else ("-" if v < 0 else "0")


# ============================================================================
# Example A: a double root -- multiplicity is counted exactly
# ============================================================================
pA = sp.expand((x - 1) ** 2 * (x + 1))
tA = tower(pA)
assert tA == [x**3 - x**2 - x + 1, 3 * x**2 - 2 * x - 1, 6 * x - 2, sp.Integer(6)], tA

# exact staircase: V = 3 on (-2,-1), 2 on (-1,1), 0 on (1,2)
assert V(tA, -2) == 3 and V(tA, sp.Rational(-3, 2)) == 3
assert V(tA, -1) == 2 and V(tA, 0) == 2 and V(tA, sp.Rational(1, 2)) == 2
assert V(tA, 1) == 0 and V(tA, sp.Rational(3, 2)) == 0 and V(tA, 2) == 0
# the headline: drop = root count WITH multiplicity (1 at x=-1, 2 at x=1)
assert V(tA, -2) - V(tA, 2) == 3, "A: drop on (-2,2] must be 3 (= 1 + 2 with mult)"
# the step AT the double root is 2 (left limit 2, value 0)
assert V(tA, sp.Rational(1, 2)) - V(tA, 1) == 2, "A: step at double root must be 2"
assert V(tA, sp.Rational(-3, 2)) - V(tA, -1) == 1, "A: step at simple root must be 1"

# ============================================================================
# Example B: a conjugate pair -- the even surplus (phantom drop)
# ============================================================================
pB = x**2 + 1
tB = tower(pB)
assert tB == [x**2 + 1, 2 * x, sp.Integer(2)], tB

assert V(tB, -2) == 2 and V(tB, -1) == 2
assert V(tB, 0) == 0 and V(tB, 1) == 0 and V(tB, 2) == 0
# #roots(-2,2] = 0  <  V(-2)-V(2) = 2,  surplus even
assert V(tB, -2) - V(tB, 2) == 2, "B: drop must be 2"
# the drop sits at x=0, a critical point that is NOT a root of pB
assert pB.subs(x, 0) != 0 and sp.diff(pB, x).subs(x, 0) == 0

# ============================================================================
# exact sign tables printed for the paper (tab:signsA, tab:signsB)
# ============================================================================
rowsA = [
    ("-2", sp.Integer(-2)), ("-3/2", sp.Rational(-3, 2)), ("-1", sp.Integer(-1)),
    ("0", sp.Integer(0)), ("1/2", sp.Rational(1, 2)), ("1", sp.Integer(1)),
    ("2", sp.Integer(2)),
]
print("== Example A: pA =", pA, " tower =", tA)
for name, t in rowsA:
    print("   x=%-5s  signs=%s  V=%d" % (name, [sgn(e, t) for e in tA], V(tA, t)))
print("   V(-2)-V(2) = %d  (= 3 roots with multiplicity)" % (V(tA, -2) - V(tA, 2)))

rowsB = [("-2", sp.Integer(-2)), ("-1", sp.Integer(-1)), ("0", sp.Integer(0)),
         ("1", sp.Integer(1)), ("2", sp.Integer(2))]
print("== Example B: pB =", pB, " tower =", tB)
for name, t in rowsB:
    print("   x=%-5s  signs=%s  V=%d" % (name, [sgn(e, t) for e in tB], V(tB, t)))
print("   V(-2)-V(2) = %d  but #roots = 0  ->  even surplus 2" % (V(tB, -2) - V(tB, 2)))
print("all sign tables verified in exact arithmetic")

# ============================================================================
# draw: 2 columns (A, B), 2 rows (polynomial / V staircase)
# ============================================================================
fig, axes = plt.subplots(
    2, 2, figsize=(9.4, 5.6), sharex="col",
    gridspec_kw={"height_ratios": [1.1, 1.0], "hspace": 0.13, "wspace": 0.22})
(axpA, axpB), (axvA, axvB) = axes

xs = np.linspace(-2, 2, 800)
fA = sp.lambdify(x, pA, "numpy")
fB = sp.lambdify(x, pB, "numpy")

# ---- Panel A-top: the polynomial with a double root ----
axpA.axhline(0, color="0.6", lw=0.8)
axpA.plot(xs, fA(xs), color=TEAL, lw=2.0)
axpA.plot([-1.0], [0], "o", color=AMBER, ms=7, zorder=5)
axpA.plot([1.0], [0], "o", color=AMBER, ms=8, zorder=5)
axpA.annotate("double root\n(tangent)", xy=(1, 0), xytext=(0.05, 2.3),
              color=AMBER, fontsize=8.5, ha="left",
              arrowprops=dict(arrowstyle="->", color=AMBER, lw=1.0))
axpA.set_ylabel(r"$p_A(x)=(x-1)^2(x+1)$", fontsize=10)
axpA.set_ylim(-2.0, 4.2)
axpA.set_title(r"(A) multiplicity is counted", fontsize=11, color=TEAL)
axpA.grid(alpha=0.18)

# ---- Panel A-bottom: V staircase 3 -> 2 -> 0 ----
for x0, x1, h in [(-2, -1, 3), (-1, 1, 2), (1, 2, 0)]:
    axvA.plot([x0, x1], [h, h], color=TEAL, lw=2.4, solid_capstyle="round")
# step at simple root x=-1 (drop 1)
axvA.plot([-1, -1], [3, 2], color=TEAL, ls=":", lw=1.2)
axvA.plot([-1], [3], "o", mfc="white", mec=TEAL, ms=6, zorder=5)
axvA.plot([-1], [2], "o", color=TEAL, ms=6, zorder=5)
# step at double root x=1 (drop 2)
axvA.plot([1, 1], [2, 0], color=AMBER, ls=":", lw=1.6)
axvA.plot([1], [2], "o", mfc="white", mec=AMBER, ms=7, zorder=5)
axvA.plot([1], [0], "o", color=AMBER, ms=7, zorder=5)
axvA.annotate("step $=2$\n(mult. of root)", xy=(1, 1), xytext=(1.12, 1.7),
              color=AMBER, fontsize=8.3, ha="left",
              arrowprops=dict(arrowstyle="->", color=AMBER, lw=1.0))
axvA.annotate("", xy=(-1.93, 3), xytext=(-1.93, 0),
              arrowprops=dict(arrowstyle="<->", color=AMBER, lw=1.3))
axvA.text(-1.85, 1.5, r"$V(-2)-V(2)=3$", color=AMBER, fontsize=9, rotation=90, va="center")
for r in (-1.0, 1.0):
    axvA.plot([r], [-0.33], "^", color=AMBER, ms=6, clip_on=False)
axvA.set_ylabel(r"$V(x)$", fontsize=11)
axvA.set_xlabel(r"$x$", fontsize=11)
axvA.set_ylim(-0.5, 3.6)
axvA.set_yticks([0, 1, 2, 3])
axvA.set_xlim(-2.05, 2.05)
axvA.grid(alpha=0.18)

# ---- Panel B-top: a polynomial with NO real root ----
axpB.axhline(0, color="0.6", lw=0.8)
axpB.plot(xs, fB(xs), color=TEAL, lw=2.0)
axpB.plot([0.0], [1.0], "s", mfc="white", mec=PLUM, ms=7, zorder=5)
axpB.annotate(r"$p_B'(0)=0$ but $p_B(0)\neq0$", xy=(0, 1.0), xytext=(-1.95, 3.4),
              color=PLUM, fontsize=8.5, ha="left",
              arrowprops=dict(arrowstyle="->", color=PLUM, lw=1.0))
axpB.set_ylabel(r"$p_B(x)=x^2+1$", fontsize=10)
axpB.set_ylim(-0.4, 5.2)
axpB.set_title(r"(B) the even surplus (phantom drop)", fontsize=11, color=TEAL)
axpB.grid(alpha=0.18)

# ---- Panel B-bottom: V staircase 2 -> 0 at x=0 (no root) ----
for x0, x1, h in [(-2, 0, 2), (0, 2, 0)]:
    axvB.plot([x0, x1], [h, h], color=TEAL, lw=2.4, solid_capstyle="round")
axvB.plot([0, 0], [2, 0], color=PLUM, ls=":", lw=1.6)
axvB.plot([0], [2], "s", mfc="white", mec=PLUM, ms=7, zorder=5)
axvB.plot([0], [0], "s", color=PLUM, ms=7, zorder=5)
axvB.annotate("drop $=2$ at a\nNON-root\n(conjugate pair)", xy=(0, 1), xytext=(0.22, 1.25),
              color=PLUM, fontsize=8.3, ha="left",
              arrowprops=dict(arrowstyle="->", color=PLUM, lw=1.0))
axvB.annotate("", xy=(-1.93, 2), xytext=(-1.93, 0),
              arrowprops=dict(arrowstyle="<->", color=AMBER, lw=1.3))
axvB.text(-1.85, 1.0, r"$V(-2)-V(2)=2$" "\n" r"$\#\mathrm{roots}=0$", color=AMBER,
          fontsize=8.3, rotation=90, va="center")
axvB.set_ylabel(r"$V(x)$", fontsize=11)
axvB.set_xlabel(r"$x$", fontsize=11)
axvB.set_ylim(-0.5, 3.6)
axvB.set_yticks([0, 1, 2, 3])
axvB.set_xlim(-2.05, 2.05)
axvB.grid(alpha=0.18)

fig.suptitle("The derivative tower counts roots up to an even surplus",
             fontsize=12, color=TEAL, y=0.99)
fig.savefig("budan_fig1_tower.pdf", bbox_inches="tight")
fig.savefig("budan_fig1_tower.png", dpi=150, bbox_inches="tight")
print("wrote budan_fig1_tower.{pdf,png}")
