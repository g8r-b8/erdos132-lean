"""Sharpened counting lemma, by parity.  For a convex n-set with D distinct distances, k = #distances with
multiplicity in [1,n].  Frequent classes have >= n+1 pairs, so (D-k)(n+1)+k <= N=C(n,2), i.e.
k >= kmin(n,D) := ceil((D(n+1)-N)/n).  Altman: D >= m = floor(n/2).  Check the closed forms
  n=2m+1: kmin = K+1 for D=m+K, 1<=K<=m+1 ;   n=2m: kmin = K+2 for D=m+K, 1<=K<=2m-1.
Also list the multiplicity profiles of the known extremal families and their k."""
from math import comb, ceil
import itertools
def kmin(n,D):
    N=comb(n,2); return max(1,-(-(D*(n+1)-N)//n))
bad=[]
for n in range(5,400):
    m=n//2
    for K in range(1,m+1):
        D=m+K
        if D>comb(n,2): break
        pred=K+1 if n%2 else K+2
        if kmin(n,D)!=pred: bad.append((n,D,kmin(n,D),pred))
print('closed-form check, violations:',bad[:10])
def profile_subset(N,S):
    from collections import Counter
    c=Counter()
    for a,b in itertools.combinations(S,2):
        d=(b-a)%N; c[min(d,N-d)]+=1
    return [c[j] for j in sorted(c)]
for n in (6,7,8,9,10,11,12,13):
    fam={'R_n':(n,range(n)),'R_{n+1}^-':(n+1,range(n)),}
    out=[]
    for name,(N,S) in fam.items():
        p=profile_subset(N,list(S)); out.append('%s D=%d k=%d prof=%s'%(name,len(p),sum(1 for x in p if x<=n),p))
    # all (n+2)-gon minus 2 vertices, up to rotation: remove 0 and g
    for g in range(1,(n+2)//2+1):
        S=[i for i in range(n+2) if i not in (0,g)]; p=profile_subset(n+2,S)
        out.append('R_{n+2}-{0,%d} D=%d k=%d'%(g,len(p),sum(1 for x in p if x<=n)))
    print('n=%d m=%d:'%(n,n//2),'; '.join(out))
