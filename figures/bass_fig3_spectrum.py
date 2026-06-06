"""Figure 3 — the non-backtracking spectrum: the (1-u^2)^{|E|-|V|} pile-up at |lambda|=1
plus the cycle disk of radius sqrt(<d^2>/<d> - 1)."""
import numpy as np
import matplotlib.pyplot as plt
from fig_style import setup, save, COL
setup()

rng = np.random.default_rng(7)

def config_model(deg_seq):
    stubs = []
    for v, d in enumerate(deg_seq):
        stubs += [v] * d
    rng.shuffle(stubs)
    edges = set()
    for i in range(0, len(stubs) - 1, 2):
        a, b = stubs[i], stubs[i + 1]
        if a != b and (min(a, b), max(a, b)) not in edges:
            edges.add((min(a, b), max(a, b)))
    return len(deg_seq), [tuple(e) for e in edges]

def hashimoto_eigs(n, edges):
    darts = []
    for a, b in edges:
        darts += [(a, b), (b, a)]
    D2 = len(darts)
    B = np.zeros((D2, D2))
    for i, (a, b) in enumerate(darts):
        for k, (c, d) in enumerate(darts):
            if b == c and (c, d) != (b, a):
                B[i, k] = 1
    return np.linalg.eigvals(B)

n, edges = config_model([2] * 60 + [10] * 60)
deg = np.zeros(n)
for a, b in edges:
    deg[a] += 1; deg[b] += 1
md, m2 = deg.mean(), (deg ** 2).mean()
kappa = m2 / md
r_cyc = np.sqrt(kappa - 1)
ev = hashimoto_eigs(n, edges)
lead = ev[np.argmax(np.abs(ev))].real

fig, ax = plt.subplots(figsize=(6.6, 6.0))
th = np.linspace(0, 2 * np.pi, 400)
# cycle disk (degree-variance radius)
ax.fill(r_cyc * np.cos(th), r_cyc * np.sin(th), color=COL['band'], zorder=0)
ax.plot(r_cyc * np.cos(th), r_cyc * np.sin(th), color=COL['pos'], lw=1.4, zorder=2,
        label=r"radius $\sqrt{\langle d^2\rangle/\langle d\rangle-1}$ (percolation edge)")
# unit circle
ax.plot(np.cos(th), np.sin(th), color=COL['grey'], lw=1.0, ls=(0, (4, 2)), zorder=2,
        label=r"$|\lambda|=1$ pile-up  ($(1-u^2)^{|E|-|V|}$ factor)")
# eigenvalues
ax.scatter(ev.real, ev.imag, s=9, color=COL['neg'], alpha=0.55, zorder=3, edgecolors='none')
# leading eigenvalue
ax.scatter([lead], [0], s=120, color=COL['accent'], zorder=4, edgecolors='white', linewidths=1.3,
           label=r"leading $\approx \langle d^2\rangle/\langle d\rangle-1$")
ax.set_aspect('equal')
lim = lead * 1.12
ax.set_xlim(-2.6, lim); ax.set_ylim(-2.8, 2.8)
ax.axhline(0, color=COL['grey'], lw=0.5, zorder=1)
ax.axvline(0, color=COL['grey'], lw=0.5, zorder=1)
ax.set_xlabel(r"$\mathrm{Re}\,\lambda$"); ax.set_ylabel(r"$\mathrm{Im}\,\lambda$")
ax.legend(loc='upper left', fontsize=8.2, framealpha=0.95)
ax.set_title(r"Non-backtracking spectrum (degrees $\{2,10\}$): a $|\lambda|=1$ pile-up"
             "\n"
             r"from Bass's $(1-u^2)^{|E|-|V|}$, plus a degree-variance cycle disk",
             fontsize=10.5)
save(fig, "bass_fig3_spectrum")
