import itertools, math
from sage.all import graphs, PolynomialRing, QQ, RR, matrix

R = PolynomialRing(QQ,'x'); x = R.gen()

def signed_adj(G, signs):
    n=G.order(); idx={v:i for i,v in enumerate(G.vertices())}
    M=[[0]*n for _ in range(n)]
    for (a,b,_),s in zip(G.edges(), signs):
        i,j=idx[a],idx[b]; M[i][j]=s; M[j][i]=s
    return matrix(QQ, M)

# FISSURE PROBE: is E_signings[ charpoly(A_s^2) ] real-rooted with max root <= 4(d-1) = band^2 ?
# If YES -> a two-sided interlacing handle (would control max|lambda|, the non-bipartite obstruction).
# If NO  -> confirms the wall (the linearity magic E[charpoly(A_s)]=mu(G) does NOT survive squaring).
def probe(G,name):
    d=max(G.degree()); q=d-1; E=G.num_edges(); n=G.order()
    bandsq=4.0*q
    avg=R(0); cnt=0
    # also track: is each individual charpoly(A_s^2) the same? and the average's behaviour
    for signs in itertools.product([1,-1], repeat=E):
        A=signed_adj(G,list(signs))
        A2=A*A
        cp=A2.charpoly()
        avg+=cp; cnt+=1
    avg=avg/cnt
    # real-rooted? count real roots with multiplicity vs degree
    rts=avg.roots(RR)
    nreal=sum(m for _,m in rts)
    realrooted = (nreal==avg.degree())
    maxr = max(float(r) for r,_ in rts) if rts else None
    print("%-12s d=%d band^2=4(d-1)=%.3f  deg=%d"%(name,d,bandsq,avg.degree()))
    print("   E[charpoly(A_s^2)] real-rooted? %s  (%d/%d real)"%(realrooted,nreal,avg.degree()))
    print("   max root of E[charpoly(A_s^2)] = %s  (<= band^2? %s)"%(
        (None if maxr is None else round(maxr,4)), (maxr is not None and maxr<=bandsq+1e-9)))
    # compare: square of matching-poly roots? i.e. does E[charpoly(A^2)] = prod(x - mu_i^2)?
    # (mu_i = matching poly roots). Build matching-poly-squared poly.
    print()

for nm,G in [("K4",graphs.CompleteGraph(4)),
             ("K_3,3",graphs.CompleteBipartiteGraph(3,3)),
             ("Prism",graphs.CycleGraph(3).cartesian_product(graphs.CompleteGraph(2))),
             ("Petersen",graphs.PetersenGraph())]:
    probe(G,nm)
