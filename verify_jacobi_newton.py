import sympy as sp

X = sp.symbols('X')
ok = {}

# --- Jacobi: (det M)' = tr(adj M . M') for a polynomial matrix ---
M = sp.Matrix([[1+X, X**2, 2],[0, 1-X, X],[X, 1, 1+X**2]])
detp = sp.diff(M.det(), X)
adj = M.adjugate()
Mp = M.applyfunc(lambda e: sp.diff(e, X))
rhs = sp.trace(adj*Mp)
ok['jacobi_3x3'] = sp.simplify(detp - rhs) == 0

# --- Newton: charpolyRev(M)' = -charpolyRev(M) * sum_k tr(M^{k+1}) X^k  (mod X^N) ---
def check_newton(Mnum, N=8):
    n = Mnum.shape[0]
    cpR = (sp.eye(n) - X*Mnum).det()           # charpolyRev = det(1 - X M)
    lhs = sp.diff(cpR, X)
    # series sum_{k>=0} tr(M^{k+1}) X^k truncated
    S = 0
    P = Mnum
    for k in range(N):
        S += sp.trace(P) * X**k
        P = P*Mnum
    rhs = -cpR*S
    return sp.series(lhs - rhs, X, 0, N).removeO() == 0
M2 = sp.Matrix([[2,1,0],[1,3,1],[0,1,2]])
ok['newton_3x3'] = check_newton(M2)
ok['newton_2x2'] = check_newton(sp.Matrix([[0,2],[3,1]]))

# --- Ihara: tr(B^k) = #closed nb-walks, and spectral via Bass ---
# small graph: triangle K3 (vertices 0,1,2), build Hashimoto B on darts
import itertools
edges = [(0,1),(1,2),(2,0)]
darts = []
for (a,b) in edges:
    darts += [(a,b),(b,a)]
idx = {d:i for i,d in enumerate(darts)}
nB = len(darts)
B = sp.zeros(nB,nB)
for d in darts:
    for e in darts:
        if d[1]==e[0] and e!=(d[1],d[0]):   # head(d)=tail(e), e != reverse(d)
            B[idx[d],idx[e]] = 1
# tr(B^k) for k=1..6
trB = [sp.trace(B**k) for k in range(1,7)]
# count closed nb-walks of length k (rooted at a dart) by brute force
def count_nb(k):
    c=0
    for start in darts:
        # walks of length k: sequences d0..dk with d0=start? closed means dk returns to start dart
        # closed nb walk length k rooted: d0,...,d_{k} with d0=dk=start, consecutive nb-adjacent
        def rec(cur, steps):
            if steps==k:
                return 1 if cur==start else 0
            t=0
            for e in darts:
                if cur[1]==e[0] and e!=(cur[1],cur[0]):
                    t+=rec(e,steps+1)
            return t
        c+=rec(start,0)
    return c
cnt = [count_nb(k) for k in range(1,7)]
ok['ihara_trB_eq_count'] = all(int(trB[i])==cnt[i] for i in range(6))
# Bass spectral: (1-u^2)^|V| det(1-uB) = (1-u^2)^|E| det(1-uA+u^2(D-1))
u=sp.symbols('u')
A=sp.Matrix([[0,1,1],[1,0,1],[1,1,0]]); D=sp.diag(2,2,2)
lhsB=(1-u**2)**3 * (sp.eye(nB)-u*B).det()
rhsB=(1-u**2)**3 * (sp.eye(3)-u*A+u**2*(D-sp.eye(3))).det()
ok['bass_K3'] = sp.simplify(lhsB-rhsB)==0

for k,v in ok.items(): print(f"{k}: {'PASS' if v else 'FAIL'}")
print("trB(K3) k=1..6 =", [int(x) for x in trB])
print("count   k=1..6 =", cnt)
