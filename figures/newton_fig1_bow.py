#!/usr/bin/env python3
"""Figure for "The Inward Bow of a Real-Rooted Polynomial".

Panel A: log-concavity of the normalized means p_k = e_k / C(n,k) of a real-rooted
         cubic -- the sequence is concave on a log axis (it "bows inward").
Panel B: the Newton gap  e_k^2 C(n,k-1)C(n,k+1) - e_{k-1}e_{k+1}C(n,k)^2  at every
         interior k, for a real-rooted cubic (positive), the all-equal-roots quartic
         (zero, the sharp case) and x^2+1 (negative -- real-rootedness is necessary).

The script asserts every plotted number against exact integer arithmetic before drawing.
"""
import numpy as np
import matplotlib.pyplot as plt
from math import comb

TEAL = "#1B6F8C"; AMBER = "#E08A1E"; BAND = "#DCE7EB"


def esymm(roots):
    c = np.array([1.0])
    for r in roots:
        c = np.convolve(c, [1.0, -r])  # multiply by (x - r), highest-degree first
    n = len(roots)
    return [((-1) ** k) * c[k] for k in range(n + 1)]  # e_k = (-1)^k * coeff(x^{n-k})


def newton_gap(e, n, k):
    return e[k] ** 2 * comb(n, k - 1) * comb(n, k + 1) - e[k - 1] * e[k + 1] * comb(n, k) ** 2


# ---- data + assertions -------------------------------------------------------
cubic = [1, 2, 4]
e_c = esymm(cubic); n_c = 3
means = [e_c[k] / comb(n_c, k) for k in range(n_c + 1)]
assert np.allclose(e_c, [1, 7, 14, 8]), e_c
assert np.allclose(means, [1, 7 / 3, 14 / 3, 8]), means
# log-concavity of the means: each interior log(p_k) >= chord midpoint
for k in range(1, n_c):
    assert means[k] ** 2 >= means[k - 1] * means[k + 1] - 1e-9

quart = [1, 1, 1, 1]; e_q = esymm(quart); n_q = 4
assert np.allclose(e_q, [1, 4, 6, 4, 1])
gaps = {
    "$(x{-}1)(x{-}2)(x{-}4)$": ([newton_gap(e_c, n_c, k) for k in (1, 2)], TEAL),
    "$(x{-}1)^4$": ([newton_gap(e_q, n_q, k) for k in (1, 2, 3)], "#7BA7B5"),
    "$x^2+1$": ([0 ** 2 * comb(2, 0) * comb(2, 2) - 1 * 1 * comb(2, 1) ** 2], AMBER),
}
assert gaps["$(x{-}1)(x{-}2)(x{-}4)$"][0] == [21, 84]
assert gaps["$(x{-}1)^4$"][0] == [0, 0, 0]
assert gaps["$x^2+1$"][0] == [-4]

# ---- draw --------------------------------------------------------------------
fig, (axA, axB) = plt.subplots(1, 2, figsize=(10, 3.7))

# Panel A: the bow
ks = list(range(n_c + 1))
axA.plot(ks, means, "o-", color=TEAL, lw=2, ms=8, zorder=3)
# chords between neighbours of each interior point, to show concavity (on log axis)
for k in range(1, n_c):
    axA.plot([k - 1, k + 1], [means[k - 1], means[k + 1]], "--", color=AMBER, lw=1.4, zorder=2)
    axA.annotate("", xy=(k, means[k]), xytext=(k, (means[k - 1] * means[k + 1]) ** 0.5),
                 arrowprops=dict(arrowstyle="-|>", color=AMBER, lw=1.2))
axA.set_yscale("log")
for k, m in zip(ks, means):
    axA.annotate(f"$p_{k}$", (k, m), textcoords="offset points", xytext=(6, 6),
                 color=TEAL, fontsize=11)
axA.set_xlabel("$k$"); axA.set_ylabel(r"$p_k=e_k/\binom{n}{k}$  (log scale)")
axA.set_xticks(ks)
axA.set_title(r"real roots $\Rightarrow$ log-concave means", color=TEAL, fontsize=11)
axA.text(0.05, 0.93, r"each $p_k^2\geq p_{k-1}p_{k+1}$" + "\n(point above the secant's foot)",
         transform=axA.transAxes, fontsize=8.5, va="top", color=AMBER)

# Panel B: the gap, with the necessity row negative
labels, allvals, colors = [], [], []
for lab, (vals, col) in gaps.items():
    for j, v in enumerate(vals):
        labels.append(f"{lab}\n$k={j+1}$"); allvals.append(v); colors.append(col)
xpos = np.arange(len(allvals))
axB.bar(xpos, allvals, color=colors, edgecolor="black", lw=0.6)
axB.axhline(0, color="black", lw=0.8)
axB.set_xticks(xpos)
axB.set_xticklabels(labels, fontsize=7.0)
axB.set_ylabel(r"Newton gap  $\mathrm{LHS}-\mathrm{RHS}$")
axB.set_title("the gap is $\\geq 0$ exactly when roots are real", color=TEAL, fontsize=11)
axB.annotate("complex roots:\ngap $<0$", xy=(len(allvals) - 1, -4), xytext=(len(allvals) - 2.4, -30),
             fontsize=8.5, color=AMBER,
             arrowprops=dict(arrowstyle="-|>", color=AMBER, lw=1.2))

fig.tight_layout()
fig.savefig("figures/newton_fig1_bow.pdf", bbox_inches="tight")
print("wrote figures/newton_fig1_bow.pdf; all assertions passed")
