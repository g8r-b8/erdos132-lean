"""[R3/OS copy of fewdist_search.py with extra far-from-cocircular initialisations (kinds 5-7) and a
cocircularity histogram at the end.]  Numerical search for strictly convex n-gons with exactly D distinct distances.
Alternating scheme: (1) sort the C(n,2) distances, optimal partition into D contiguous groups (DP);
(2) least-squares on coordinates+group centres with that assignment, plus convexity & scale residuals.
Many random restarts.  Converged solutions (resid < tol) are deduplicated by normalized distance profile.
Usage: fewdist_search.py n D restarts seed"""
import numpy as np, sys, itertools, math
from scipy.optimize import least_squares
n=int(sys.argv[1]); D=int(sys.argv[2]); R=int(sys.argv[3]); seed=int(sys.argv[4]) if len(sys.argv)>4 else 0
ONESIDED=len(sys.argv)>5 and sys.argv[5]=="os"
rng=np.random.default_rng(seed)
I,J=np.triu_indices(n,1); NP=len(I)
def dists(x):
    P=x.reshape(n,2); return np.linalg.norm(P[I]-P[J],axis=1)
def best_partition(d):
    o=np.argsort(d); s=d[o]
    cs=np.concatenate([[0],np.cumsum(s)]); cs2=np.concatenate([[0],np.cumsum(s*s)])
    A=np.arange(NP+1)[:,None]; B=np.arange(NP+1)[None,:]
    K=np.maximum(B-A,1)
    C=(cs2[B]-cs2[A])-(cs[B]-cs[A])**2/K
    C=np.where(B>A,C,np.inf)
    f=np.full(NP+1,np.inf); f[0]=0; args=[]
    for g in range(1,D+1):
        M=f[:,None]+C
        a=np.argmin(M,axis=0); f=M[a,np.arange(NP+1)]; args.append(a)
    lab=np.zeros(NP,int); b=NP
    for g in range(D,0,-1):
        a=args[g-1][b]; lab[o[a:b]]=g-1; b=a
    return lab
def cross_res(x,eps=1e-3):
    P=x.reshape(n,2)
    A=P; B=np.roll(P,-1,0); C=np.roll(P,-2,0)
    cr=(B-A)[:,0]*(C-B)[:,1]-(B-A)[:,1]*(C-B)[:,0]
    return np.minimum(cr-eps,0)*10
def run(x):
    for it in range(30):
        d=dists(x); lab=best_partition(d)
        c0=np.array([d[lab==g].mean() for g in range(D)])
        def res(z):
            xx=z[:2*n]; c=z[2*n:]
            dd=dists(xx)
            extra=[]
            if ONESIDED:
                k0=np.where((I==0)&(J==n-1))[0][0]
                extra=np.minimum(dd[k0]-dd,0)*10
            return np.concatenate([dd-c[lab], cross_res(xx), [ (dd.max()-1.0) ], extra])
        def jac(z):
            xx=z[:2*n]; P=xx.reshape(n,2)
            diff=P[I]-P[J]; dd=np.maximum(np.linalg.norm(diff,axis=1),1e-9); u=diff/dd[:,None]
            Jd=np.zeros((NP,2*n))
            ar=np.arange(NP)
            Jd[ar,2*I]=u[:,0]; Jd[ar,2*I+1]=u[:,1]; Jd[ar,2*J]=-u[:,0]; Jd[ar,2*J+1]=-u[:,1]
            rows=[np.hstack([Jd,-np.eye(D)[lab]])]
            A=P; B=np.roll(P,-1,0); C=np.roll(P,-2,0)
            cr=(B-A)[:,0]*(C-B)[:,1]-(B-A)[:,1]*(C-B)[:,0]
            act=(cr-1e-3)<0
            Jc=np.zeros((n,2*n+D))
            for i in range(n):
                if not act[i]: continue
                a,b,cc=i,(i+1)%n,(i+2)%n
                ax,ay=A[i];bx,by=B[i];cx,cy=C[i]
                Jc[i,2*a]+=10*(-(cy-by)); Jc[i,2*a+1]+=10*(cx-bx)
                Jc[i,2*b]+=10*(cy-ay); Jc[i,2*b+1]+=10*(-(cx-ax))
                Jc[i,2*cc]+=10*(-(by-ay)); Jc[i,2*cc+1]+=10*(bx-ax)
            rows.append(Jc)
            km=np.argmax(dd); Js=np.zeros((1,2*n+D)); Js[0,:2*n]=Jd[km]; rows.append(Js)
            if ONESIDED:
                k0=np.where((I==0)&(J==n-1))[0][0]
                act2=(dd[k0]-dd)<0
                Jo=np.zeros((NP,2*n+D))
                Jo[:,:2*n]=10*(Jd[k0][None,:]-Jd)*act2[:,None]
                rows.append(Jo)
            return np.vstack(rows)
        sol=least_squares(res,np.concatenate([x,c0]),jac=jac,xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=500)
        xn=sol.x[:2*n]
        if np.allclose(xn,x,atol=1e-13): x=xn;break
        x=xn
    d=dists(x); lab=best_partition(d)
    r=max(abs(d[lab==g]-d[lab==g].mean()).max() for g in range(D))
    return x,r,lab
def init():
    if ONESIDED:
        kind=rng.integers(3)
        if kind==0:
            th=np.sort(rng.uniform(0,np.pi*rng.uniform(0.3,1.0),n))
            P=np.c_[np.cos(th),np.sin(th)]*(1+rng.normal(0,0.05,(n,1)))
        elif kind==1:  # fan-like
            th=np.sort(rng.uniform(0,np.pi/3,n-1)); P=np.vstack([[0,0],np.c_[np.cos(th),np.sin(th)]])*(1+rng.normal(0,0.05,(n,1)))
        else:
            v=rng.normal(size=(n-1,2)); v=v[np.argsort(np.arctan2(v[:,1],v[:,0]))]
            P=np.vstack([[0,0],np.cumsum(v,0)])
        # order along chain: B_0..B_{n-1} as convex polygon order
        c=P.mean(0); o=np.argsort(np.arctan2(P[:,1]-c[1],P[:,0]-c[0])); P=P[o]
        # rotate labels so that the farthest pair are consecutive in cyclic order (0 and n-1)
        Dm=np.linalg.norm(P[:,None]-P[None],axis=2); i,j=np.unravel_index(np.argmax(Dm),Dm.shape)
        if (j-i)%n==1: P=np.roll(P,-j,0)
        elif (i-j)%n==1: P=np.roll(P,-i,0)
        return P.ravel()
    kind=rng.integers(8)
    if kind==5:   # two concentric circles, alternating radii
        th=np.sort(rng.uniform(0,2*np.pi,n)); rho=rng.uniform(0.85,1.0)
        rad=np.where(np.arange(n)%2==0,1.0,rho)*(1+rng.normal(0,0.01,n))
        P=np.c_[rad*np.cos(th),rad*np.sin(th)]; return P.ravel()
    if kind==6:   # ellipse
        th=np.sort(rng.uniform(0,2*np.pi,n)); e=rng.uniform(0.6,0.95)
        P=np.c_[np.cos(th),e*np.sin(th)]; return P.ravel()
    if kind==7:   # two circular arcs of different radii (lens / egg)
        h=n//2; t1=np.linspace(-1,1,h)*rng.uniform(0.6,1.4); t2=np.linspace(-1,1,n-h+2)[1:-1]*rng.uniform(0.6,1.4)
        R2=rng.uniform(0.5,2.0)
        A=np.c_[np.cos(t1),np.sin(t1)]; A[:,0]-=np.cos(t1[0])
        B=np.c_[-R2*np.cos(t2),R2*np.sin(t2)]; B[:,0]+=R2*np.cos(t2[0])
        P=np.vstack([A,B[::-1]]); P-=P.mean(0)
        c=P.mean(0); o=np.argsort(np.arctan2(P[:,1]-c[1],P[:,0]-c[0])); return P[o].ravel()
    if kind>=3:
        v=rng.normal(size=(n,2)); v-=v.mean(0)
        v=v[np.argsort(np.arctan2(v[:,1],v[:,0]))]; P=np.cumsum(v,0); P-=P.mean(0); P/=np.abs(P).max()
        return P.ravel()
    if kind==0:
        th=np.sort(rng.uniform(0,2*np.pi,n))
    elif kind==1:
        N=n+rng.integers(0,4); sub=np.sort(rng.choice(N,n,replace=False)); th=2*np.pi*sub/N+rng.normal(0,0.05,n)
    else:
        th=np.sort(rng.uniform(0,2*np.pi,n))
    rad=1+rng.normal(0,0.15 if kind==2 else 0.03,n)
    P=np.c_[rad*np.cos(th),rad*np.sin(th)]
    return P.ravel()
def strictly_convex(x,tol=1e-6):
    P=x.reshape(n,2); c=P.mean(0); o=np.argsort(np.arctan2(P[:,1]-c[1],P[:,0]-c[0])); Q=P[o]
    A=Q;B=np.roll(Q,-1,0);C=np.roll(Q,-2,0)
    cr=(B-A)[:,0]*(C-B)[:,1]-(B-A)[:,1]*(C-B)[:,0]
    return cr.min()>tol
def cocirc_count(x):
    P=x.reshape(n,2); best=0
    for a,b,c in itertools.combinations(range(n),3):
        M=np.array([[P[i,0],P[i,1],1] for i in (a,b,c)]); rhs=-np.array([P[i]@P[i] for i in (a,b,c)])
        try: s=np.linalg.solve(M,rhs)
        except: continue
        vals=np.abs(np.einsum('ij,ij->i',P,P)+P@s[:2]+s[2])
        best=max(best,int((vals<1e-6).sum()))
    return best
seen={}
for t in range(R):
    x=init()
    try: x,r,lab=run(x)
    except Exception: continue
    if ONESIDED:
        dd=dists(x); k0=np.where((I==0)&(J==n-1))[0][0]
        if dd.max()>dd[k0]+1e-9: continue
    if r<1e-9 and strictly_convex(x):
        d=dists(x); D_=len(set(np.round(d,7)))
        if D_!=D: continue
        vals=sorted(set(np.round(d/d.max(),6)))
        key=tuple(vals)
        if key in seen: seen[key][0]+=1; continue
        mult=[int((np.abs(d/d.max()-v)<1e-6).sum()) for v in vals]
        cc=cocirc_count(x)
        seen[key]=[1,mult,cc,x]
        rare=sum(1 for mm in mult if mm<=n)
        if ONESIDED:
            P=x.reshape(n,2); sides=np.linalg.norm(np.diff(P,axis=0),axis=1); diag2=np.linalg.norm(P[2:]-P[:-2],axis=1)
            regarc=np.ptp(sides)<1e-6 and np.ptp(diag2)<1e-6
            d0=np.linalg.norm(P-P[0],axis=1)[1:]; dl=np.linalg.norm(P-P[-1],axis=1)[:-1]
            fan0=np.ptp(d0)<1e-6; fanl=np.ptp(dl)<1e-6
            cat='cocirc' if cocirc_count(x)==n else ('fan' if (fan0 or fanl) else 'OTHER')
            print('   OS: cat=%s regular-arc=%s fan0=%s fanlast=%s  sides=%s'%(cat,regarc,fan0,fanl,np.round(sides,4)),flush=True)
            if cat=='OTHER': print('   COORDS',np.round(P,8).tolist(),flush=True)
        print('NEW n=%d D=%d mult(asc)=%s rare=%d maxcocirc=%d vals=%s'%(n,D,mult,rare,cc,[round(v,5) for v in vals]),flush=True)
print('restarts',R,'distinct configs',len(seen))
for k,v in seen.items(): print(v[0],v[1],'cocirc',v[2])
from collections import Counter as _C
print('HIST maxcocirc',sorted(_C(v[2] for v in seen.values()).items()))
np.save('scratch/r3/os/fewdist_n%d_D%d_s%d.npy'%(n,D,seed),np.array([v[3] for v in seen.values()]),allow_pickle=True)
