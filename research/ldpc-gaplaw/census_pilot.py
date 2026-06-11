# Certified short-cycle census of deployed LDPC codes via the trace-formula gap law.
#
# Pilot: IEEE 802.11n (WiFi) LDPC codes, n=648, z=27, rates 1/2, 2/3, 3/4, 5/6
# (alist files from jeroenoverman/ECC-LDPC-application, derived from the standard).
#
# The gap law (Part III, godsil-gutman-lean):
#     gap_k := tr(A^k) - p_k = tr(B^k)   for 1 <= k <= g+1   (g = girth)
# where p_k = power sums of matching-polynomial roots, B = Hashimoto operator.
# Status: k < g PROVEN in Lean sorry-free (Ihara/NbVanishing.lean, Stone A);
# k = g (the census case, c_g = tr(B^g)/(2g)) numerically locked on 12 064 graphs
# (gaplaw_sweep.py) = Stone B, formalization in progress.
#
# Census routes (mutually independent):
#   R1  c_g = tr(B^g) / (2g)                     [non-backtracking trace]
#   R2  c_g = (tr(A^g) - p_g) / (2g)             [gap law: adjacency + matchings]
#       p_2 = 2 m1,  p_4 = 2 m1^2 - 4 m2,  p_6 = 2 m1^3 - 6 m1 m2 + 6 m3
#       m1 = |E|,  m2 = C(m1,2) - sum_v C(d_v,2),
#       m3 = (1/3) sum_e m2(G - {endpoints of e})   (exact, edge recursion)
#   R3  c_g = subgraph_search_count(C_g) / (2g)   [brute-force VF2 enumeration]
#
# A real-world failure of R1 == R2 == R3 would falsify the (not-yet-formalized)
# Stone B window on deployed engineering artifacts. Agreement = the census.

from sage.all import Graph, matrix, ZZ, graphs, binomial
import sys, time

def parse_alist(path):
    with open(path) as f:
        tok = f.read().split()
    it = iter(tok)
    n = int(next(it)); m = int(next(it))
    _maxcol = int(next(it)); _maxrow = int(next(it))
    coldeg = [int(next(it)) for _ in range(n)]
    rowdeg = [int(next(it)) for _ in range(m)]
    edges = []
    for v in range(n):
        # this alist variant is UNPADDED: exactly coldeg[v] entries per column
        for _ in range(coldeg[v]):
            x = int(next(it))
            if x <= 0:
                raise ValueError(f"col {v}: unexpected non-positive entry {x}")
            edges.append((f"v{v}", f"c{x - 1}"))
    return n, m, edges

def matching_m2(edge_list, deg):
    m1 = len(edge_list)
    s = sum(binomial(d, 2) for d in deg.values())
    return binomial(m1, 2) - s

def matching_m3(G):
    # m3 = (1/3) * sum_e m2(G - endpoints(e))
    total = 0
    for (u, v, _) in G.edges():
        H = G.copy()
        H.delete_vertices([u, v])
        deg = {x: H.degree(x) for x in H.vertices()}
        total += matching_m2(H.edges(), deg)
    assert total % 3 == 0
    return total // 3

def hashimoto_trace_powers(G, kmax):
    darts = []
    for u, v in G.edges(labels=False):
        darts.append((u, v)); darts.append((v, u))
    idx = {d: i for i, d in enumerate(darts)}
    md = len(darts)
    B = matrix(ZZ, md, md, sparse=True)
    for (a, b) in darts:
        for c in G.neighbors(b):
            if c != a:
                B[idx[(a, b)], idx[(b, c)]] = 1
    traces = []
    P = matrix.identity(ZZ, md, sparse=True)
    for k in range(1, kmax + 1):
        P = P * B
        traces.append(P.trace())
    return traces

for rate in ["r1_2", "r2_3", "r3_4", "r5_6"]:
    t0 = time.time()
    n, m, edges = parse_alist(f"/work/H_n648-z27-{rate}.alist")
    G = Graph(edges, multiedges=False)
    g = int(G.girth())
    m1 = G.num_edges()
    print(f"=== 802.11n n=648 z=27 {rate}: Tanner |V|={G.num_verts()} "
          f"(vars {n} + checks {m}), |E|={m1}, girth={g}", flush=True)

    # R1: non-backtracking traces up to g (+ Stone A zeros below g)
    trB = hashimoto_trace_powers(G, g)
    zeros_ok = all(trB[k - 1] == 0 for k in range(1, g))
    c_g_R1 = trB[g - 1] / (2 * g)
    print(f"  Stone A check (tr(B^k)=0 for k<g): {'OK' if zeros_ok else 'VIOLATION!'}")
    print(f"  R1 (NB trace):      c_{g} = {c_g_R1}", flush=True)

    # R2: gap law with adjacency traces + matching power sums
    A = G.adjacency_matrix()
    Apow = A ** g
    trAg = Apow.trace()
    deg = {v: G.degree(v) for v in G.vertices()}
    m2 = matching_m2(G.edges(), deg)
    if g == 4:
        p_g = 2 * m1**2 - 4 * m2
    elif g == 6:
        m3 = matching_m3(G)
        p_g = 2 * m1**3 - 6 * m1 * m2 + 6 * m3
    else:
        p_g = None
    if p_g is not None:
        c_g_R2 = (trAg - p_g) / (2 * g)
        print(f"  R2 (gap law):       c_{g} = {c_g_R2}", flush=True)
    else:
        c_g_R2 = None
        print(f"  R2 skipped (girth {g} needs m_{g//2} recursion beyond pilot)")

    # R3: brute-force VF2 cycle count (independent)
    try:
        copies = G.subgraph_search_count(graphs.CycleGraph(g))
        c_g_R3 = copies / (2 * g)
        print(f"  R3 (VF2 search):    c_{g} = {c_g_R3}", flush=True)
    except Exception as ex:
        c_g_R3 = None
        print(f"  R3 failed: {ex}")

    agree = len({x for x in [c_g_R1, c_g_R2, c_g_R3] if x is not None}) == 1
    print(f"  CENSUS {'AGREES' if agree else 'MISMATCH!'} "
          f"[{time.time()-t0:.0f}s]", flush=True)
