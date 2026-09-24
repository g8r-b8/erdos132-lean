"""Diameter structure of the true examples R_{2m+2}-1 and R_{2m+3}-2 (combinatorial: class = chord index).
Reports: case (A: some diameter non-halving / B1 / B2), run lengths, D(U_h), D(T_h) for each diameter."""
import sys
def analyse(M, holes, m):
    pts=[k for k in range(M) if k not in holes]; n=len(pts); assert n==2*m+1
    cls=lambda i,j: min((pts[j]-pts[i])%M,(pts[i]-pts[j])%M)
    top=max(cls(i,j) for i in range(n) for j in range(i+1,n))
    diam=[(i,j) for i in range(n) for j in range(i+1,n) if cls(i,j)==top]
    span=lambda i,j: min((j-i)%n,(i-j)%n)
    if any(span(i,j)!=m for i,j in diam): return "A", None
    # star cycle order: h_j={j,j+m}; star neighbours of {x,x+m}: {x+m,x+2m},{x-m,x}
    D=set(frozenset(e) for e in diam)
    cyc=[]; x=0
    for _ in range(n): cyc.append(frozenset({x%n,(x+m)%n})); x+=m
    isd=[c in D for c in cyc]
    if all(isd): runs=[n]
    else:
        k=isd.index(False); rot=isd[k:]+isd[:k]; runs=[]; c=0
        for b in rot+[False]:
            if b: c+=1
            elif c: runs.append(c); c=0
    case="B2" if min(runs)>=2 else "B1"
    info=[]
    for e in diam:
        i,j=sorted(e)
        if (j-i)%n==m: T=[(i+t)%n for t in range(m+1)]; U=[(j+t)%n for t in range(m+2)]
        else: T=[(j+t)%n for t in range(m+1)]; U=[(i+t)%n for t in range(m+2)]
        dv=lambda S: len({cls(a,b) for a in S for b in S if a<b})
        info.append((dv(T),dv(U)))
    return case, (runs, sorted(set(info)))
for m in range(int(sys.argv[1]),int(sys.argv[2])+1):
    print(f"m={m}: R_{2*m+2}-1:", analyse(2*m+2,{0},m))
    for h in range(1,m+2):
        print(f"   R_{2*m+3}-2 holes 0,{h} (j={h-1} between):", analyse(2*m+3,{0,h},m))
