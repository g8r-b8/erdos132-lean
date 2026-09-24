"""Adversarial scan of the induction step of the double-ladder lemma.
Block a..b = positions 0..W on unit circle, step th. x on circle Gamma(center b-1, radius c(W)).
Record x (strictly convex w.r.t. block sides, on far side of chord(a,b)) such that every |x,j|<=c(W)+eps
is within tol of some c(1..W), and |x,b|>c(W). Expect only x=p (position -1). Floats: sanity only."""
import numpy as np
def run(W,th,N=400000,tol=1e-6):
    P=np.array([[np.cos(k*th),np.sin(k*th)] for k in range(W+1)])
    c=np.array([2*np.sin(k*th/2) for k in range(1,W+1)])
    ctr=P[W-1]; rho=c[W-1]
    phis=np.linspace(0,2*np.pi,N,endpoint=False)
    X=ctr+rho*np.c_[np.cos(phis),np.sin(phis)]
    ok=np.ones(N,bool)
    for j in range(W):   # x must be strictly left of each directed side j->j+1 (ccw polygon)
        e=P[j+1]-P[j]; ok&= (e[0]*(X[:,1]-P[j,1])-e[1]*(X[:,0]-P[j,0]))>1e-9
    e=P[W]-P[0]; ok&= (e[0]*(X[:,1]-P[0,1])-e[1]*(X[:,0]-P[0,0]))<-1e-9   # x on other side of chord(a,b) than interior
    D=np.linalg.norm(X[:,None,:]-P[None,:,:],axis=2)
    ok&= D[:,W]>rho+1e-9
    bad=np.zeros(N,bool)
    for j in range(W):
        small=D[:,j]<=rho+1e-9
        dist=np.min(np.abs(D[:,j,None]-c[None,:]),axis=1)
        bad|= small & (dist>tol)
    good=ok&~bad
    pts=X[good]
    p=np.array([np.cos(-th),np.sin(-th)])
    far=[x for x in pts if np.linalg.norm(x-p)>1e-3]
    return good.sum(), len(far), (far[:3] if far else None)
rng=np.random.default_rng(0)
cnt=0
for W in (2,3,4,5,7,9):
    for _ in range(6):
        th=rng.uniform(0.02, 2*np.pi/(2*W-1)*0.999)
        g,nf,ex=run(W,th)
        if nf: print("W",W,"th",th,"good",g,"FAR",nf,ex); cnt+=1
print("done, anomalies:",cnt)
