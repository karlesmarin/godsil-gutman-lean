# Double-cover test: the gross code [[144,12,12]] Tanner graph is a 2-lift (double cover) of
# the [[72,12,6]] Tanner graph (Symons-Rajput-Browne, arXiv:2511.13560). We verify, on OUR
# constructed graphs, the Artin-Ihara / Bilu-Linial 2-lift trace identity for the
# non-backtracking operator:
#       tr B^k(cover)  =  tr B^k(base)  +  tr B_s^k(base)
# where B_s is the SIGNED non-backtracking operator of the base, with the signing induced by
# the covering map. This ties Symons et al.'s covering construction to our formalized
# Ihara/Bass + Godsil-Gutman/Bilu-Linial 2-lift (Part I) + gap-law machinery.  Run with sage.

from sage.all import Graph, matrix, identity_matrix, ZZ
import numpy as np
from scipy import sparse as sp
import time

t0 = time.time()


def bb_graph(L, M):
    # Tanner graph of HX = [A | B] for the BB code with A = x^3+y+y^2, B = y^3+x+x^2.
    # Vertices: ('c',aL,aM) checks; ('q0',aL,aM) left qubits; ('q1',aL,aM) right qubits.
    N = L * M

    def shift(n):
        P = matrix(ZZ, n, n, 0)
        for i in range(n):
            P[i, (i + 1) % n] = 1
        return P

    Sl, Sm = shift(L), shift(M)
    Il, Im = identity_matrix(ZZ, L), identity_matrix(ZZ, M)
    x = Sl.tensor_product(Im)
    y = Il.tensor_product(Sm)
    A = x ** 3 + y + y ** 2
    B = y ** 3 + x + x ** 2
    assert max(A.augment(B).list()) <= 1

    def lm(r):
        return (r // M, r % M)

    E = []
    for i in range(N):
        ci = ('c',) + lm(i)
        for j in range(N):
            if A[i, j]:
                E.append((ci, ('q0',) + lm(j)))
            if B[i, j]:
                E.append((ci, ('q1',) + lm(j)))
    return Graph(E, multiedges=False)


Gb = bb_graph(6, 6)    # base  [[72,12,6]]
Gc = bb_graph(12, 6)   # cover [[144,12,12]] (gross)
gb = int(Gb.girth())
print(f"base  [[72,12,6]]   : |V|={Gb.num_verts()} |E|={Gb.num_edges()} girth={gb}")
print(f"cover [[144,12,12]] : |V|={Gc.num_verts()} |E|={Gc.num_edges()} girth={int(Gc.girth())}")


# covering map p(aL) = aL mod 6 ; sheet 0 = aL in 0..5, sheet 1 = aL+6
def s0(v):
    return v


def s1(v):
    side, aL, aM = v
    return (side, (aL + 6) % 12, aM)


sign = {}
exactly_one = True
for (u, v, _) in Gb.edges():
    e0 = Gc.has_edge(s0(u), s0(v))
    e1 = Gc.has_edge(s0(u), s1(v))
    if e0 == e1:                      # a valid 2-cover lifts each base edge to exactly one sheet
        exactly_one = False
    sign[frozenset((u, v))] = 1 if e0 else -1
print(f"\ngross IS a double cover of base (each base edge lifts to one sheet): {exactly_one}")
print(f"|V(cover)| == 2*|V(base)| : {Gc.num_verts() == 2 * Gb.num_verts()}")


def nb_traces(G, kmax, sign=None):
    darts = []
    for u, v in G.edges(labels=False):
        darts.append((u, v)); darts.append((v, u))
    idx = {d: i for i, d in enumerate(darts)}
    md = len(darts)
    rows, cols, vals = [], [], []
    for (a, b) in darts:
        i = idx[(a, b)]
        for c in G.neighbors(b):
            if c != a:
                w = 1 if sign is None else sign[frozenset((b, c))]
                rows.append(i); cols.append(idx[(b, c)]); vals.append(w)
    Bm = sp.csr_matrix((np.array(vals, dtype=np.int64), (rows, cols)), shape=(md, md))
    half = (kmax + 1) // 2
    pw = {1: Bm}
    for j in range(2, half + 1):
        pw[j] = pw[j - 1] @ Bm
    tr = []
    for k in range(1, kmax + 1):
        a = min(k, half); b = k - a
        if b == 0:
            tr.append(int(pw[a].diagonal().sum()))
        else:
            tr.append(int(pw[a].multiply(pw[b].T).sum()))
    return tr


K = gb + 2
trCov = nb_traces(Gc, K)
trBase = nb_traces(Gb, K)
trSign = nb_traces(Gb, K, sign)

print("\n  k :   tr B^k(cover)   tr B^k(base)+tr B_s^k(base)   match")
allok = True
for k in range(K):
    lhs, rhs = trCov[k], trBase[k] + trSign[k]
    ok = (lhs == rhs); allok = allok and ok
    print(f"  {k+1} : {lhs:14d}   {rhs:14d}              {'OK' if ok else 'MISMATCH'}")

print(f"\nArtin-Ihara / 2-lift identity  tr B^k(cover) = tr B^k(base) + tr B_s^k(base): "
      f"{'HOLDS' if allok else 'FAILS'}")
print(f"c_{gb}(base) = {trBase[gb-1] / (2*gb)}   c_{gb}(cover) = {trCov[gb-1] / (2*gb)}")
print(f"[{time.time()-t0:.0f}s]")
