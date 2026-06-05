import itertools, math
from sage.all import graphs, PolynomialRing, QQ, RR, matrix

R = PolynomialRing(QQ,'x'); x = R.gen()

def matching_poly(G):
    n=G.order(); idx={v:i for i,v in enumerate(G.vertices())}
    edges=[(idx[a],idx[b]) for a,b,_ in G.edges()]; cnt={}
    def rec(s,used,k):
        cnt[k]=cnt.get(k,0)+1
        for i in range(s,len(edges)):
            a,b=edges[i]
            if a not in used and b not in used:
                used.add(a);used.add(b);rec(i+1,used,k+1);used.discard(a);used.discard(b)
    rec(0,set(),0); p=R(0)
    for k,c in cnt.items(): p+=(-1)**k*c*x**(n-2*k)
    return p

def signed_adj(G, signs):
    n=G.order(); idx={v:i for i,v in enumerate(G.vertices())}
    M=[[0]*n for _ in range(n)]
    for (a,b,_),s in zip(G.edges(), signs):
        i,j=idx[a],idx[b]; M[i][j]=s; M[j][i]=s
    return matrix(RR, M)

def analyze(G, name):
    d=max(G.degree()); q=d-1; B=2*math.sqrt(q)
    E=G.num_edges()
    mp=matching_poly(G)
    mp_max=max(float(r) for r,_ in mp.roots(RR))
    bip = G.is_bipartite()
    # average signed charpoly == matching poly ?  (Godsil-Gutman)
    avg=R(0); cnt=0
    # per-signing extremes
    best_max=1e9; both_in_band=0; total=0
    best_both=None
    for signs in itertools.product([1,-1], repeat=E):
        A=signed_adj(G,list(signs))
        cp=A.charpoly(); avg+=R([QQ(c) for c in cp.list()]); cnt+=1
        eigs=[float(e.real()) for e in A.eigenvalues()]
        lmax=max(eigs); lmin=min(eigs)
        best_max=min(best_max, lmax)
        total+=1
        if lmax<=B+1e-9 and lmin>=-B-1e-9:
            both_in_band+=1
            if best_both is None: best_both=(lmax,lmin)
    avg=avg/cnt
    gg_ok = (avg==mp)
    print("%-14s d=%d %s  band=%.4f  E=%d signings=%d"%(name,d,("BIP" if bip else "NON-bip"),B,E,total))
    print("   Godsil-Gutman avg(charpoly_signed)==matchingPoly: %s"%gg_ok)
    print("   matchingPoly max root=%.4f (<=band? %s)"%(mp_max, mp_max<=B+1e-9))
    print("   min over signings of lambda_max = %.4f  (<= band? %s)  [MSS upper end]"%(best_max,best_max<=B+1e-9))
    print("   signings with BOTH ends in band: %d/%d  (exists? %s) %s"%(
        both_in_band,total, both_in_band>0,
        ("" if best_both is None else "e.g. (max=%.3f,min=%.3f)"%best_both)))

for nm,G in [("K4",graphs.CompleteGraph(4)),       # 3-reg, NON-bipartite, small
             ("K_3,3",graphs.CompleteBipartiteGraph(3,3)),  # 3-reg bipartite
             ("Petersen",graphs.PetersenGraph()),  # 3-reg non-bip, 15 edges
             ("Prism",graphs.CycleGraph(3).cartesian_product(graphs.CompleteGraph(2)))]:  # 3-reg
    try:
        analyze(G,nm)
    except Exception as e:
        print(nm,"ERR",e)
