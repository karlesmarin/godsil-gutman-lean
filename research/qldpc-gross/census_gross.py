# PoC: certified short-cycle census of the IBM "gross code" [[144,12,12]] bivariate bicycle
# qLDPC, via the trace-formula gap law (Part VI). Same three independent routes as the WiFi
# census. Run:  sage research/qldpc-gross/census_gross.py
#
# Gross code (Bravyi et al., Nature 2024): l=12, m=6, N=l*m=72; x = S_l (x) I_m, y = I_l (x) S_m;
#   A = x^3 + y + y^2,  B = y^3 + x + x^2;  HX = [A | B]  (N x 2N), HZ = [B^T | A^T].
# We analyse the Tanner graph of HX (HX and HZ graphs are isomorphic for BB codes).
#
# Routes (mutually independent), exactly as in the WiFi census:
#   R1  c_g = tr(B^g) / (2g)              [Hashimoto non-backtracking trace]
#   R2  c_g = (tr(A^g) - p_g) / (2g)      [gap law: adjacency + matching power sums]
#   R3  combinatorial enumeration         [codegree pairs (g=4) / VF2 (g=6)]
# Stone A (tr(B^k)=0 for k<g) is the Lean-certified part; k=g is Stone B (gap law).

from sage.all import Graph, matrix, identity_matrix, ZZ, graphs, binomial
import time

t0 = time.time()
L, M = 12, 6
N = L * M  # 72


def shift(n):
    P = matrix(ZZ, n, n, 0)
    for i in range(n):
        P[i, (i + 1) % n] = 1
    return P


Sl, Sm = shift(L), shift(M)
Il, Im = identity_matrix(ZZ, L), identity_matrix(ZZ, M)
x = Sl.tensor_product(Im)   # x = S_l (x) I_m
y = Il.tensor_product(Sm)   # y = I_l (x) S_m
A = x ** 3 + y + y ** 2
B = y ** 3 + x + x ** 2
HX = A.augment(B)           # N x 2N

assert max(HX.list()) <= 1, "collision: HX has a double edge (entry > 1)"
assert all(sum(HX.row(i)) == 6 for i in range(N)), "check weight != 6"

edges = []
for i in range(N):
    for j in range(2 * N):
        if HX[i, j] != 0:
            edges.append((f"c{i}", f"q{j}"))
G = Graph(edges, multiedges=False)
g = int(G.girth())
m1 = G.num_edges()
degs = [G.degree(v) for v in G.vertices()]
print(f"=== gross code [[144,12,12]] Tanner graph of HX ===")
print(f"|V| = {G.num_verts()}  |E| = {m1}  girth g = {g}")
print(f"check-degree = {max(degs)}  qubit-degree = {min(degs)}")


# ---- census machinery (identical to the WiFi pipeline) ----
def hashimoto_traces(Gr, kmax):
    import numpy as np
    from scipy import sparse as sp
    darts = []
    for u, v in Gr.edges(labels=False):
        darts.append((u, v)); darts.append((v, u))
    idx = {d: i for i, d in enumerate(darts)}
    md = len(darts)
    rows, cols = [], []
    for (a, b) in darts:
        i = idx[(a, b)]
        for c in Gr.neighbors(b):
            if c != a:
                rows.append(i); cols.append(idx[(b, c)])
    Bm = sp.csr_matrix((np.ones(len(rows), dtype=np.int64), (rows, cols)), shape=(md, md))
    half = (kmax + 1) // 2
    pows = {1: Bm}
    for j in range(2, half + 1):
        pows[j] = pows[j - 1] @ Bm
    traces = []
    for k in range(1, kmax + 1):
        a = min(k, half); b = k - a
        if b == 0:
            traces.append(int(pows[a].diagonal().sum()))
        else:
            traces.append(int(pows[a].multiply(pows[b].T).sum()))
    return traces


def m2_global(m1, degs):
    return binomial(m1, 2) - sum(binomial(d, 2) for d in degs)


def m3_bipartite(Gr, m1, S_global):
    deg = {v: Gr.degree(v) for v in Gr.vertices()}
    total = 0
    for (u, v, _) in Gr.edges():
        du, dv = deg[u], deg[v]
        mH = m1 - du - dv + 1
        S_H = S_global - binomial(du, 2) - binomial(dv, 2)
        S_H -= sum(deg[w] - 1 for w in Gr.neighbors(u) if w != v)
        S_H -= sum(deg[w] - 1 for w in Gr.neighbors(v) if w != u)
        total += binomial(mH, 2) - S_H
    assert total % 3 == 0
    return total // 3


def c4_codegree(Gr, side="c"):
    vs = [v for v in Gr.vertices() if str(v).startswith(side)]
    nbr = {v: set(Gr.neighbors(v)) for v in vs}
    total = 0
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            cod = len(nbr[vs[i]] & nbr[vs[j]])
            if cod >= 2:
                total += binomial(cod, 2)
    return total


# Stone A: tr(B^k) = 0 for k < g
trB = hashimoto_traces(G, g)
zeros_ok = all(trB[k] == 0 for k in range(g - 1))
print(f"\nStone A  tr(B^k)=0 for k<g : {'OK' if zeros_ok else 'VIOLATION'}")
c_R1 = trB[g - 1] / (2 * g)
print(f"R1 NB-trace   c_{g} = {c_R1}")

# R2 gap law
trAg = (G.adjacency_matrix() ** g).trace()
S_global = sum(binomial(d, 2) for d in degs)
m2 = m2_global(m1, degs)
if g == 4:
    p_g = 2 * m1 ** 2 - 4 * m2
elif g == 6:
    m3 = m3_bipartite(G, m1, S_global)
    p_g = 2 * m1 ** 3 - 6 * m1 * m2 + 6 * m3
else:
    p_g = None
if p_g is not None:
    c_R2 = (trAg - p_g) / (2 * g)
    print(f"R2 gap-law    c_{g} = {c_R2}")
else:
    c_R2 = None
    print(f"R2 skipped (girth {g} not in {{4,6}})")

# R3 enumeration
if g == 4:
    c_R3 = c4_codegree(G, "c")
    print(f"R3 codegree   c_4 = {c_R3}")
elif g == 6:
    c_R3 = G.subgraph_search_count(graphs.CycleGraph(6)) / 12
    print(f"R3 VF2        c_6 = {c_R3}")
else:
    c_R3 = None

vals = {v for v in [c_R1, c_R2, c_R3] if v is not None}
print(f"\nCENSUS {'AGREES' if len(vals) == 1 else 'MISMATCH!'}  "
      f"[{time.time()-t0:.0f}s]")
