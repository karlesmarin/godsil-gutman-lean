# Exhaustive small-graph sweep of the trace-formula gap law (Stone A/B numerical lock).
#
# Claim (locked previously on 6 named graphs):
#   gap_k := tr(A^k) - p_k  equals  N_k := tr(B^k)   for 1 <= k <= g+1,
#   and the law is SHARP: it fails at k = g+2.
# Here p_k = power sums of matching-polynomial roots, B = Hashimoto non-backtracking operator,
# g = girth.
#
# Sweep: ALL connected graphs on 4..8 vertices with at least one cycle (girth finite),
# min degree >= 1. Reports any violation of the law in the window, and checks sharpness
# statistics at g+2 (sharpness is claimed as "fails generically", verified per-graph).

from sage.all import graphs, matrix, QQ, Infinity

def hashimoto(G):
    darts = []
    for u, v in G.edges(labels=False):
        darts.append((u, v))
        darts.append((v, u))
    idx = {d: i for i, d in enumerate(darts)}
    m = len(darts)
    B = matrix(QQ, m, m, 0)
    for (a, b) in darts:
        for (c, d) in darts:
            if b == c and d != a:
                B[idx[(a, b)], idx[(c, d)]] = 1
    return B

def matching_powersums(G, kmax):
    mu = G.matching_polynomial()
    R = mu.roots(ring=None, multiplicities=True)  # over QQbar via roots? use companion instead
    # robust route: power sums via Newton from coefficients (no root extraction)
    n = mu.degree()
    c = [mu[n - i] for i in range(n + 1)]  # c[0]=1 leading
    p = [n]  # p_0
    for k in range(1, kmax + 1):
        if k <= n:
            s = -k * c[k]
            for i in range(1, k):
                s -= c[i] * p[k - i]
        else:
            s = 0
            for i in range(1, n + 1):
                s -= c[i] * p[k - i]
        p.append(s)
    return p

def check_graph(G):
    g = int(G.girth())
    kmax = g + 2
    A = G.adjacency_matrix()
    B = hashimoto(G)
    p = matching_powersums(G, kmax)
    Apow = matrix.identity(QQ, A.nrows())
    Bpow = matrix.identity(QQ, B.nrows())
    bad_window = []
    sharp_ok = None
    for k in range(1, kmax + 1):
        Apow = Apow * A
        Bpow = Bpow * B
        gap = Apow.trace() - p[k]
        Nk = Bpow.trace()
        if k <= g + 1:
            if gap != Nk:
                bad_window.append((k, gap, Nk))
        else:  # k = g+2
            sharp_ok = (gap != Nk)
    return g, bad_window, sharp_ok

violations = []
sharp_fail = []   # graphs where law UNEXPECTEDLY holds at g+2
total = 0
for n in range(4, 9):
    for G in graphs.nauty_geng(f"{n} -c"):
        if G.girth() == Infinity:
            continue
        total += 1
        g, bad, sharp = check_graph(G)
        if bad:
            violations.append((G.graph6_string(), g, bad))
        if sharp is False:
            sharp_fail.append((G.graph6_string(), g))
    print(f"n={n} done, cumulative checked={total}, violations={len(violations)}, "
          f"law-still-holds-at-g+2={len(sharp_fail)}", flush=True)

print("=" * 60)
print(f"TOTAL graphs checked: {total}")
print(f"WINDOW VIOLATIONS (k <= g+1): {len(violations)}")
for v in violations[:20]:
    print("  ", v)
print(f"Graphs where law persists at g+2 (sharpness exceptions): {len(sharp_fail)}")
for s in sharp_fail[:20]:
    print("  ", s)
