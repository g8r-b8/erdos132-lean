"""Degenerate regime Delta > 1.94 Delta2: star structure; claim mu(Delta2) <= n+1.
Adversarial construction: y=0, A on C(y,Delta) (arc of angular width <= omega, extremes at chord Delta2),
B = all corners of K = D(y,D2) cap D(a,D2) (all circle-circle intersections lying in K) + extra points on arcs."""
import numpy as np, itertools
rng=np.random.default_rng(7)
def circ_int(c1,c2,R):
    d=np.linalg.norm(c2-c1)
    if d>2*R or d==0: return []
    m=(c1+c2)/2; h=np.sqrt(R*R-d*d/4); e=(c2-c1)/d; nrm=np.array([-e[1],e[0]])
    return [m+h*nrm,m-h*nrm]
worst=-99
for trial in range(300):
    D2=1000.0; lam=rng.uniform(1.941,1.999); Dl=lam*D2
    omega=2*np.arcsin(D2/(2*Dl))
    k=rng.integers(2,40)
    ang=np.sort(rng.uniform(0,omega,k)); ang[0]=0
    if rng.random()<0.5: ang[-1]=omega       # force one A-A Delta2 pair
    A=np.stack([Dl*np.cos(ang),Dl*np.sin(ang)],1); y=np.zeros(2)
    W=np.vstack([y[None],A])
    inK=lambda p: np.all(np.linalg.norm(W-p,axis=1)<=D2*(1+1e-12))
    B=[]
    for i,j in itertools.combinations(range(len(W)),2):
        for p in circ_int(W[i],W[j],D2):
            if inK(p): B.append(p)
    # extra points on arcs: sample on each circle, keep those in K
    for w in W:
        for th in rng.uniform(0,2*np.pi,400):
            p=w+D2*np.array([np.cos(th),np.sin(th)])
            if inK(p): B.append(p)
    B=np.array(B) if B else np.zeros((0,2))
    # dedupe
    if len(B):
        keep=[]
        for p in B:
            if all(np.linalg.norm(p-q)>1e-6 for q in keep): keep.append(p)
        B=np.array(keep)
    X=np.vstack([W,B]); n=len(X)
    Dm=np.linalg.norm(X[:,None]-X[None],axis=2); iu=np.triu_indices(n,1); d=Dm[iu]
    tol=1e-7
    assert d.max()<=Dl*(1+tol)
    bad=np.sum((d>D2*(1+tol))&(d<Dl*(1-tol)))
    assert bad==0, "distance in (D2,Delta)"
    mu2=int(np.sum(np.abs(d-D2)<tol*D2)); muD=int(np.sum(np.abs(d-Dl)<tol*Dl))
    worst=max(worst,mu2-n)
print("max over trials of mu(Delta2)-n =",worst,"(claim <= 1)")
