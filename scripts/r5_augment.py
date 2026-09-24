"""R5: greedy augmentation -- try to add points to a structured set that raise the multiplicity of
Delta_j (j = 3,4,..) without creating new distances above Delta_j. Float guidance only."""
import numpy as np, itertools, sys
from r5_profiles import ring, profile
tol=1e-9
def circ_int(p,r,q,s):
    d=np.linalg.norm(q-p)
    if d<1e-12 or d>r+s+1e-12 or d<abs(r-s)-1e-12: return []
    a=(r*r-s*s+d*d)/(2*d); h2=r*r-a*a
    if h2<-1e-12: return []
    h=np.sqrt(max(h2,0)); u=(q-p)/d; w=np.array([-u[1],u[0]]); b=p+a*u
    return [b+h*w,b-h*w] if h>1e-12 else [b]
def top_vals(X,k):
    n,v,m=profile(X); return v[:k],m[:k]
def ok_add(X,c,allowed):
    d=np.linalg.norm(X-c,axis=1)
    if d.min()<1e-6: return False
    big=d[d>allowed[-1]+tol]
    return all(min(abs(x-a) for a in allowed)<tol for x in big)
def augment(X,j,steps=40,seed=0):
    rng=np.random.default_rng(seed)
    X=np.array(X)
    for it in range(steps):
        vals,m=top_vals(X,j); allowed=vals[:j]; r=vals[j-1]
        best=None;bestdeg=1
        n=len(X); pairs=list(itertools.combinations(range(n),2))
        rng.shuffle(pairs)
        for a,b in pairs[:4000]:
            for c in circ_int(X[a],r,X[b],r):
                if not ok_add(X,c,allowed): continue
                deg=int(np.sum(abs(np.linalg.norm(X-c,axis=1)-r)<tol))
                if deg>bestdeg: best,bestdeg=c,deg
        if best is None: break
        X=np.vstack([X,best])
        n,v,m=profile(X)
        print(f" step{it}: added deg{bestdeg}; n={n} top={m[:j+2]}",flush=True)
    return X
if __name__=="__main__":
    m=int(sys.argv[1]); j=int(sys.argv[2])
    X=ring(m)
    n,v,mm=profile(X); print("start",n,mm[:6])
    augment(X,j,steps=int(sys.argv[3]) if len(sys.argv)>3 else 12)
