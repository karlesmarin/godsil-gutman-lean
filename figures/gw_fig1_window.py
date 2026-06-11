"""Part VI figure 1: the sharp window of the trace-formula gap law on the Petersen graph.

Exact integer arithmetic throughout (no floats in the data):
  tr(A^k) = 3^k + 5*1^k + 4*(-2)^k                      (Petersen spectrum 3, 1^5, (-2)^4)
  p_k     = Newton power sums of mu(x) = x^10 - 15x^8 + 75x^6 - 145x^4 + 90x^2 - 6
  tr(B^k) = sum_lambda s_k(lambda) + 5*(1 + (-1)^k),    s_k = lambda*s_{k-1} - 2*s_{k-2}
            (Ihara--Bass for 3-regular: per-eigenvalue quadratic mu^2 - lambda*mu + 2 = 0,
             plus (m - n) = 5 copies each of +1 and -1)
The script ASSERTS gap_k == tr(B^k) for 1 <= k <= g+1 = 6 and gap_k != tr(B^k) at k = 7, 8,
then draws the figure. Girth of Petersen = 5.
"""
from fig_style import COL, setup, save
import matplotlib.pyplot as plt
import numpy as np

# --- exact data -------------------------------------------------------------
KMAX = 8
G_GIRTH = 5

trA = [3**k + 5 * 1**k + 4 * (-2)**k for k in range(KMAX + 1)]

# mu coefficients as e_i (only even nonzero): e_2 = -15? careful with signs:
# mu(x) = prod(x - theta) = sum (-1)^i e_i x^{n-i}
# mu = x^10 - 15 x^8 + 75 x^6 - 145 x^4 + 90 x^2 - 6
# => e_2 = -15, e_4 = 75 -> wait: coeff of x^{10-2} is +e_2... mu coeff x^8 = -15 = +e_2
e = {0: 1, 2: -15, 4: 75, 6: -145, 8: 90, 10: -6}
for i in (1, 3, 5, 7, 9):
    e[i] = 0
p = [10]  # p_0 = n
for k in range(1, KMAX + 1):
    s = (-1) ** (k - 1) * k * e.get(k, 0)
    for i in range(1, k):
        s += (-1) ** (i - 1) * e.get(i, 0) * p[k - i]
    p.append(s)

# tr(B^k): per adjacency eigenvalue lambda with multiplicity, s_k recurrence
spec = [(3, 1), (1, 5), (-2, 4)]
trB = []
for k in range(KMAX + 1):
    tot = 0
    for lam, mult in spec:
        s0, s1 = 2, lam
        if k == 0:
            sk = s0
        elif k == 1:
            sk = s1
        else:
            a, b = s0, s1
            for _ in range(2, k + 1):
                a, b = b, lam * b - 2 * a
            sk = b
        tot += mult * sk
    tot += 5 * (1 + (-1) ** k)
    trB.append(tot)

gap = [trA[k] - p[k] for k in range(KMAX + 1)]

# --- the law, asserted ------------------------------------------------------
for k in range(1, G_GIRTH + 2):
    assert gap[k] == trB[k], (k, gap[k], trB[k])
for k in (G_GIRTH + 2, G_GIRTH + 3):
    assert gap[k] != trB[k], (k, gap[k], trB[k])
print("window check OK:", [(k, gap[k], trB[k]) for k in range(1, KMAX + 1)])

# --- figure -----------------------------------------------------------------
setup()
fig, ax = plt.subplots(figsize=(7.6, 4.1))
ks = np.arange(1, KMAX + 1)
w = 0.38
ax.bar(ks - w / 2, [gap[k] for k in ks], width=w,
       color=COL["pos"], label=r"$\mathrm{tr}\,A^k - p_k$  (matching side)")
ax.bar(ks + w / 2, [trB[k] for k in ks], width=w,
       color=COL["accent"], label=r"$\mathrm{tr}\,B^k$  (non-backtracking side)")
ax.set_yscale("symlog", linthresh=10)
ax.set_ylim(0, 30000)          # headroom: keep annotations clear of the title
ax.set_xlabel(r"walk length $k$")
ax.set_ylabel("count (symlog)")
ax.set_xticks(ks)

# window shading and the sharp boundary
ax.axvspan(0.5, G_GIRTH + 1.5, color=COL["band"], alpha=0.55, zorder=0)
ax.axvline(G_GIRTH + 1.5, color=COL["grey"], lw=0.9, ls="--")

# region captions, placed in EMPTY areas (mid-left is empty: bars 1..4 are zero)
ax.text(2.5, 110, "the window  $k \\leq g{+}1$\ntheorem: the sides agree",
        ha="center", va="center", fontsize=10, color=COL["pos"])
ax.text(7.55, 11000, "sharp: first failure\nat $k = g{+}2$",
        ha="center", va="center", fontsize=9.5, color=COL["neg"])

# value labels above each visible bar (small, neutral ink)
def label(x, v, dy=1.25, color=COL["node"]):
    ax.text(x, max(v, 1) * dy + (0 if v else 1.0), f"{v}",
            ha="center", va="bottom", fontsize=8.5, color=color)

for k in (5, 6):
    label(k - w / 2, gap[k])
    label(k + w / 2, trB[k])
for k in (7, 8):
    label(k - w / 2, gap[k], color=COL["neg"])
    label(k + w / 2, trB[k], color=COL["neg"])

# the first nonzero gap, called out once
ax.annotate(f"$2g\\,c_g = {gap[G_GIRTH]}$", xy=(G_GIRTH, gap[G_GIRTH]),
            xytext=(4.0, 900), fontsize=9.5, color=COL["node"], ha="center",
            arrowprops=dict(arrowstyle="-", color=COL["grey"], lw=0.7))

ax.legend(frameon=False, loc="upper left", fontsize=9.5)
ax.set_title("Petersen graph ($g = 5$): the gap law on its sharp window", fontsize=11,
             pad=10)
save(fig, "gw_fig1_window")

# --- table data for the paper ------------------------------------------------
print("\nPetersen exact values:")
print("k   trA      p_k      gap      trB")
for k in range(1, KMAX + 1):
    print(f"{k:<3} {trA[k]:<8} {p[k]:<8} {gap[k]:<8} {trB[k]}")
