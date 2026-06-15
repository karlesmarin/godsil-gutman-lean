#!/usr/bin/env python3
"""
Figure for "The Staircase of Signs" (Sturm in Lean 4).

Two stacked panels for p(x) = x^3 - x = x(x-1)(x+1):
  (A) the polynomial, crossing zero at its three real roots;
  (B) the Sturm sign-variation count V(x), a staircase that drops by exactly one
      at each root of p and does NOT move at a zero of an interior chain member
      (x = +-1/sqrt(3), where p != 0).

Every plotted sign and count is asserted in EXACT rational arithmetic (sympy)
before anything is drawn. Run: python sturm_fig1_staircase.py
"""
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

TEAL = "#1B6F8C"
AMBER = "#E08A1E"
BAND = "#DCE7EB"

x = sp.symbols("x")
p = x**3 - x

# --- build the Sturm sequence by the negated Euclidean recursion (exact) ---
seq = [sp.Poly(p, x), sp.Poly(sp.diff(p, x), x)]
while True:
    a, b = seq[-2], seq[-1]
    r = -sp.rem(a, b)
    if r == 0:
        break
    seq.append(r)
seq_exprs = [s.as_expr() for s in seq]
assert seq_exprs == [x**3 - x, 3*x**2 - 1, sp.Rational(2, 3)*x, sp.Integer(1)], seq_exprs

def V(t):
    """exact sign-variation count of the chain at rational t."""
    signs = [sp.sign(s.as_expr().subs(x, sp.nsimplify(t))) for s in seq]
    signs = [s for s in signs if s != 0]
    return sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])

# --- exact assertions: the staircase shape and the headline count ---
assert V(-2) == 3 and V(sp.Rational(-12, 10)) == 3      # flat left of -1
assert V(-1) == 2 and V(sp.Rational(-1, 2)) == 2        # one drop at -1
assert V(0) == 1 and V(sp.Rational(1, 2)) == 1          # one drop at 0
assert V(1) == 0 and V(2) == 0                          # one drop at 1
# tail-critical points: p_1 = 3x^2-1 = 0 at +-1/sqrt3, where p != 0 -> NO drop
r3 = sp.Rational(577, 1000)  # ~1/sqrt(3), still strictly between roots
assert V(-r3) == 2 and V(r3) == 1
assert V(-2) - V(2) == 3, "Sturm count on (-2,2] must be 3"

# --- exact assertion of the full sign table printed in the paper (tab:signs) ---
def sgn(v):
    v = sp.nsimplify(v)
    return "+" if v > 0 else ("-" if v < 0 else "0")
table_rows = [
    ("-2",        sp.Integer(-2),    ["-", "+", "-", "+"], 3),
    ("-1",        sp.Integer(-1),    ["0", "+", "-", "+"], 2),
    ("-1/2",      sp.Rational(-1,2), ["+", "-", "-", "+"], 2),
    ("-1/sqrt3",  -1/sp.sqrt(3),     ["+", "0", "-", "+"], 2),
    ("0",         sp.Integer(0),     ["0", "-", "0", "+"], 1),
    ("1/sqrt3",   1/sp.sqrt(3),      ["-", "0", "+", "+"], 1),
    ("1",         sp.Integer(1),     ["0", "+", "+", "+"], 0),
    ("2",         sp.Integer(2),     ["+", "+", "+", "+"], 0),
]
for name, t, expected_signs, expected_V in table_rows:
    got = [sgn(s.as_expr().subs(x, t)) for s in seq]
    assert got == expected_signs, f"signs at {name}: {got} != {expected_signs}"
    assert V(t) == expected_V, f"V at {name}: {V(t)} != {expected_V}"
print("chain:", seq_exprs)
print("V(-2)=%d, V(2)=%d  ->  %d roots in (-2,2]" % (V(-2), V(2), V(-2) - V(2)))
print("full sign table (tab:signs) verified in exact arithmetic")

# --- draw ---
fig, (axp, axv) = plt.subplots(
    2, 1, figsize=(7.6, 5.4), sharex=True,
    gridspec_kw={"height_ratios": [1.15, 1.0], "hspace": 0.12})

xs = np.linspace(-2, 2, 800)
pf = sp.lambdify(x, p, "numpy")
roots = [-1.0, 0.0, 1.0]

# Panel A: the polynomial
axp.axhline(0, color="0.6", lw=0.8)
axp.plot(xs, pf(xs), color=TEAL, lw=2.0)
for r in roots:
    axp.plot([r], [0], "o", color=AMBER, ms=7, zorder=5)
axp.annotate("three real roots", xy=(0, 0), xytext=(0.15, 2.4),
             color=AMBER, fontsize=9,
             arrowprops=dict(arrowstyle="->", color=AMBER, lw=1.0))
axp.set_ylabel(r"$p(x)=x^3-x$", fontsize=11)
axp.set_ylim(-3.2, 6.2)
axp.set_title("From a curve to a count, without finding a single root",
              fontsize=11, color=TEAL)
axp.grid(alpha=0.18)

# Panel B: the V staircase
steps = [(-2, -1, 3), (-1, 0, 2), (0, 1, 1), (1, 2, 0)]
for x0, x1, h in steps:
    axv.plot([x0, x1], [h, h], color=TEAL, lw=2.4, solid_capstyle="round")
for r, hi, lo in [(-1, 3, 2), (0, 2, 1), (1, 1, 0)]:
    axv.plot([r, r], [hi, lo], color=TEAL, ls=":", lw=1.2)
    axv.plot([r], [hi], "o", mfc="white", mec=TEAL, ms=6, zorder=5)  # open: left limit
    axv.plot([r], [lo], "o", color=TEAL, ms=6, zorder=5)             # closed: value at root
# tail-critical points: vertical guide, no drop
for tc in (-1/np.sqrt(3), 1/np.sqrt(3)):
    axv.axvline(tc, color=TEAL, ls=(0, (1, 3)), lw=0.9, alpha=0.55)
axv.annotate(r"$p_1=3x^2-1=0$ here," "\n" r"but $p\neq0$: no step",
             xy=(1/np.sqrt(3), 1), xytext=(0.78, 2.35), fontsize=8.3,
             color=TEAL, ha="left",
             arrowprops=dict(arrowstyle="->", color=TEAL, lw=0.9))
# the difference = root count
axv.annotate("", xy=(-1.93, 3), xytext=(-1.93, 0),
             arrowprops=dict(arrowstyle="<->", color=AMBER, lw=1.4))
axv.text(-1.86, 1.5, r"$V(-2)-V(2)=3$", color=AMBER, fontsize=9.5,
         rotation=90, va="center")
for r in roots:
    axv.plot([r], [-0.32], "^", color=AMBER, ms=6, clip_on=False)
axv.set_ylabel(r"$V(x)$", fontsize=11)
axv.set_xlabel(r"$x$", fontsize=11)
axv.set_ylim(-0.5, 3.6)
axv.set_yticks([0, 1, 2, 3])
axv.set_xlim(-2.05, 2.05)
axv.grid(alpha=0.18)

fig.savefig("sturm_fig1_staircase.pdf", bbox_inches="tight")
fig.savefig("sturm_fig1_staircase.png", dpi=150, bbox_inches="tight")
print("wrote sturm_fig1_staircase.{pdf,png}")
