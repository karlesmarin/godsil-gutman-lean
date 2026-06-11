# Certified short-cycle census of deployed LDPC codes via the trace-formula gap law. v2
# Optimized: m3 via bipartite delta formula (no graph copies); R3 independent route:
# common-neighbor formula (g=4) / VF2 (g=6). Output unbuffered to stdout.
#
# Routes (mutually independent):
#   R1  c_g = tr(B^g) / (2g)                      [Hashimoto non-backtracking trace]
#   R2  c_g = (tr(A^g) - p_g) / (2g)              [gap law: adjacency + matchings]
#        p_4 = 2 m1^2 - 4 m2,   p_6 = 2 m1^3 - 6 m1 m2 + 6 m3
#   R3  combinatorial enumeration (codegree pairs for g=4, VF2 for g=6)
# Stone A (k<g zeros) is the Lean-certified part; k=g is Stone B (numerically locked).

from sage.all import Graph, matrix, ZZ, graphs, binomial
import time

def parse_alist(path):
    with open(path) as f:
        tok = f.read().split()
    it = iter(tok)
    n = int(next(it)); m = int(next(it))
    next(it); next(it)
    coldeg = [int(next(it)) for _ in range(n)]
    _rowdeg = [int(next(it)) for _ in range(m)]
    edges = []
    for v in range(n):
        for _ in range(coldeg[v]):
            x = int(next(it))
            if x <= 0:
                raise ValueError(f"col {v}: bad entry {x}")
            edges.append((f"v{v}", f"c{x-1}"))
    return n, m, edges

def matching_m2_global(m1, degs):
    return binomial(m1, 2) - sum(binomial(d, 2) for d in degs)

def matching_m3_bipartite(G, m1, S_global):
    # m3 = (1/3) sum_{(u,v) in E} m2(G - {u,v}); bipartite => N(u), N(v) disjoint
    deg = {x: G.degree(x) for x in G.vertices()}
    total = 0
    for (u, v, _) in G.edges():
        du, dv = deg[u], deg[v]
        mH = m1 - du - dv + 1
        S_H = S_global - binomial(du, 2) - binomial(dv, 2)
        S_H -= sum(deg[x] - 1 for x in G.neighbors(u) if x != v)
        S_H -= sum(deg[x] - 1 for x in G.neighbors(v) if x != u)
        total += binomial(mH, 2) - S_H
    assert total % 3 == 0
    return total // 3

def hashimoto_traces(G, kmax):
    # scipy sparse: tr(B^k) = sum(B^a ∘ (B^b)^T) with a+b=k, never densifying.
    # int64 safe: entries of B^3 <= maxdeg^3 ~ 1331; trace sums << 2^63.
    import numpy as np
    from scipy import sparse as sp
    darts = []
    for u, v in G.edges(labels=False):
        darts.append((u, v)); darts.append((v, u))
    idx = {d: i for i, d in enumerate(darts)}
    md = len(darts)
    rows, cols = [], []
    for (a, b) in darts:
        i = idx[(a, b)]
        for c in G.neighbors(b):
            if c != a:
                rows.append(i); cols.append(idx[(b, c)])
    B = sp.csr_matrix((np.ones(len(rows), dtype=np.int64), (rows, cols)),
                      shape=(md, md))
    half = (kmax + 1) // 2
    pows = {1: B}
    for j in range(2, half + 1):
        pows[j] = pows[j - 1] @ B
    traces = []
    for k in range(1, kmax + 1):
        a = min(k, half); b = k - a
        if b == 0:
            traces.append(int(pows[a].diagonal().sum()))
        else:
            traces.append(int(pows[a].multiply(pows[b].T).sum()))
    return traces

def c4_codegree(G, side_prefix="v"):
    # bipartite 4-cycles = pairs of same-side vertices with >=2 common neighbors
    vs = [x for x in G.vertices() if str(x).startswith(side_prefix)]
    nbr = {x: set(G.neighbors(x)) for x in vs}
    total = 0
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            cod = len(nbr[vs[i]] & nbr[vs[j]])
            if cod >= 2:
                total += binomial(cod, 2)
    return total

for rate in ["r1_2", "r2_3", "r3_4", "r5_6"]:
    t0 = time.time()
    n, m, edges = parse_alist(f"/work/H_n648-z27-{rate}.alist")
    G = Graph(edges, multiedges=False)
    g = int(G.girth())
    m1 = G.num_edges()
    degs = [G.degree(x) for x in G.vertices()]
    S_global = sum(binomial(d, 2) for d in degs)
    print(f"=== 802.11n n=648 z=27 {rate}: |V|={G.num_verts()} |E|={m1} girth={g}",
          flush=True)

    trB = hashimoto_traces(G, g)
    zeros_ok = all(trB[k] == 0 for k in range(g - 1))
    c_R1 = trB[g - 1] / (2 * g)
    print(f"  StoneA tr(B^k)=0 k<g: {'OK' if zeros_ok else 'VIOLATION'}", flush=True)
    print(f"  R1 NB-trace:   c_{g} = {c_R1}", flush=True)

    trAg = (G.adjacency_matrix() ** g).trace()
    m2 = matching_m2_global(m1, degs)
    if g == 4:
        p_g = 2 * m1**2 - 4 * m2
    elif g == 6:
        m3 = matching_m3_bipartite(G, m1, S_global)
        p_g = 2 * m1**3 - 6 * m1 * m2 + 6 * m3
    else:
        p_g = None
    if p_g is not None:
        c_R2 = (trAg - p_g) / (2 * g)
        print(f"  R2 gap-law:    c_{g} = {c_R2}", flush=True)
    else:
        c_R2 = None
        print(f"  R2 skipped (girth {g})", flush=True)

    if g == 4:
        c_R3 = c4_codegree(G)
        print(f"  R3 codegree:   c_4 = {c_R3}", flush=True)
    elif g == 6:
        c_R3 = G.subgraph_search_count(graphs.CycleGraph(6)) / 12
        print(f"  R3 VF2:        c_6 = {c_R3}", flush=True)
    else:
        c_R3 = None

    vals = {x for x in [c_R1, c_R2, c_R3] if x is not None}
    print(f"  CENSUS {'AGREES' if len(vals) == 1 else 'MISMATCH!'}  "
          f"[{time.time()-t0:.0f}s]", flush=True)
