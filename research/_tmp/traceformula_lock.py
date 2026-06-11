# Exact-arithmetic lock of the trace-formula gap law on the named graphs (Stone A/B).
#
# Companion to gaplaw_sweep.py: that file sweeps ALL connected cyclic graphs on 4..8
# vertices; this file checks the six named graphs of the paper in exact rational arithmetic
# and reproduces Table 1 (Petersen, full k) and Table 3 (the six named graphs).
#
#   gap_k := tr(A^k) - p_k   equals   N_k := tr(B^k)   for 1 <= k <= g+1   (the window),
#   and the law is SHARP: it fails at k = g+2.
#
# p_k = power sums of matching-polynomial roots (Newton from coefficients, no root
# extraction); B = Hashimoto non-backtracking operator; g = girth. At k = g this gives the
# shortest-cycle count c_g = tr(B^g)/(2g).
#
# Run:  sage research/_tmp/traceformula_lock.py

from sage.all import graphs, matrix, QQ


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
    # Newton's identities from the coefficients of the matching polynomial (monic),
    # avoiding any root extraction. p[0] = n.
    mu = G.matching_polynomial()
    n = mu.degree()
    c = [mu[n - i] for i in range(n + 1)]  # c[0] = 1 (leading)
    p = [n]
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


def rows(G):
    g = int(G.girth())
    kmax = g + 2
    A = G.adjacency_matrix().change_ring(QQ)
    B = hashimoto(G)
    p = matching_powersums(G, kmax)
    Apow = matrix.identity(QQ, A.nrows())
    Bpow = matrix.identity(QQ, B.nrows())
    out = []
    for k in range(1, kmax + 1):
        Apow = Apow * A
        Bpow = Bpow * B
        trA = Apow.trace()
        trB = Bpow.trace()
        out.append((k, int(trA), int(p[k]), int(trA - p[k]), int(trB)))
    return g, out


NAMED = [
    ("K3", graphs.CompleteGraph(3)),
    ("C5", graphs.CycleGraph(5)),
    ("K4", graphs.CompleteGraph(4)),
    ("K33", graphs.CompleteBipartiteGraph(3, 3)),
    ("Q3", graphs.CubeGraph(3)),
    ("Petersen", graphs.PetersenGraph()),
]

print("=== Table 1: Petersen, full window + first failures ===")
print(f"{'k':>2} {'trA^k':>7} {'p_k':>7} {'trA^k-p_k':>10} {'trB^k':>7}")
gP, rowsP = rows(graphs.PetersenGraph())
for (k, trA, pk, gap, trB) in rowsP:
    mark = "  <window>" if k <= gP + 1 else "  <broken>" if gap != trB else ""
    print(f"{k:>2} {trA:>7} {pk:>7} {gap:>10} {trB:>7}{mark}")

print()
print("=== Table 3: the six named graphs ===")
print(f"{'graph':<10} {'g':>2} {'c_g':>4} {'gap_g=trB^g':>12} "
      f"{'window':>10} {'1st fail':>9}")
all_ok = True
for name, G in NAMED:
    g, rws = rows(G)
    by_k = {k: (gap, trB) for (k, _, _, gap, trB) in rws}
    # window: gap == trB for 1 <= k <= g+1
    win_ok = all(by_k[k][0] == by_k[k][1] for k in range(1, g + 1 + 1))
    # first failure: smallest k with gap != trB
    fail = next((k for k in range(1, g + 3) if by_k[k][0] != by_k[k][1]), None)
    gap_g, trB_g = by_k[g]
    c_g = trB_g // (2 * g)
    assert gap_g == trB_g and trB_g == 2 * g * c_g, f"{name}: k=g identity broken"
    ok = win_ok and fail == g + 2
    all_ok = all_ok and ok
    print(f"{name:<10} {g:>2} {c_g:>4} {trB_g:>12} "
          f"{'k<='+str(g+1):>10} {'k='+str(fail):>9}{'' if ok else '  <<FAIL'}")

print()
print("ALL NAMED GRAPHS: gap law holds on the window and is sharp at g+2 -> "
      + ("OK" if all_ok else "VIOLATION"))
