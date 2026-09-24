"""At the symmetric seed: find all concyclic 4-subsets and test whether some tangent vector
of the solution set (ker J) changes the concyclicity determinant at first order."""
import sys, numpy as np, itertools, collections
def seed(m):
    n=4*m; k=n//2; t=2*np.pi/n
    R2=(-np.cos(t)+np.sqrt(np.cos(t)**2+3))/2
    P=np.array([[(0.5 if x%2==0 else R2)*np.cos(x*t),(0.5 if x%2==0 else R2)*np.sin(x*t)] for x in range(n)])
    E1=sorted({tuple(sorted((x,(x+k+s)%n))) for x in range(n) for s in (1,-1)}|{tuple(sorted((x,(x+k)%n))) for x in range(0,n,2)})
    ED=sorted({tuple(sorted((x,(x+k)%n))) for x in range(1,n,2)})
    return n,k,P,2*R2,E1,ED
def run(m):
    n,k,P,D,E1,ED=seed(m); E=np.array(E1+ED); isD=np.array([0]*len(E1)+[1]*len(ED))
    d=P[E[:,0]]-P[E[:,1]]; J=np.zeros((len(E),2*n+1)); r=np.arange(len(E))
    J[r,2*E[:,0]]=2*d[:,0];J[r,2*E[:,0]+1]=2*d[:,1];J[r,2*E[:,1]]=-2*d[:,0];J[r,2*E[:,1]+1]=-2*d[:,1];J[r,-1]=np.where(isD==1,-2*D,0)
    U,S,Vt=np.linalg.svd(J); K=Vt[len(E):].T  # kernel basis (2n+1) x dim
    Q=np.array(list(itertools.combinations(range(n),4)))
    def cdet(Pq):
        a=Pq[:,:3]-Pq[:,3:4]; c=(a**2).sum(-1); return np.linalg.det(np.concatenate([a,c[...,None]],-1))
    c0=cdet(P[Q]); cc=np.abs(c0)<1e-12
    Qc=Q[cc]
    # gradient of det wrt the 8 coords by finite differences (central)
    h=1e-6; G=np.zeros((len(Qc),8))
    for i in range(4):
        for j in range(2):
            Pp=P[Qc].copy(); Pp[:,i,j]+=h; Pm=P[Qc].copy(); Pm[:,i,j]-=h
            G[:,2*i+j]=(cdet(Pp)-cdet(Pm))/(2*h)
    idx=np.stack([2*Qc[:,i]+j for i in range(4) for j in range(2)],1)  # coords
    Kq=K[idx]  # nq x 8 x dim
    der=np.einsum('qc,qcd->qd',G,Kq); nd=np.linalg.norm(der,axis=1)
    fail=Qc[nd<1e-7*np.maximum(1,np.linalg.norm(G,axis=1))]
    # classify failures: parities and whether made of antipodal pairs
    typ=collections.Counter()
    for q in fail:
        s=set(q); pairs=sum(1 for x in q if (x+k)%n in s)//2
        par=''.join(str(x%2) for x in sorted(q,key=lambda x:x%2))
        typ[(par,pairs)]+=1
    print(f"n={n}: concyclic quads {cc.sum()} of {len(Q)}; first-order broken {len(Qc)-len(fail)}; NOT broken {len(fail)}; types {dict(typ)}")
    return fail,n,k
if __name__=='__main__':
    for m in map(int,sys.argv[1:]):
        fail,n,k=run(m)
        if len(fail)<=40: print(fail.tolist())
