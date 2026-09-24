"""Pattern-B axis points for generalised arc rigidity (s even).
w=(t,0) on axis of arc midpoint, arc points at angles +-phi_k, phi_k=(2k-1)th/2, R=1.
Need |w u_k| = c(s+1-2k), k=1..s/2. Solve outer eq (k=s/2, value c(1)) for t, scan theta.
Floats: exploration only."""
import numpy as np
def c2(j,th): return 2-2*np.cos(j*th)
for s in (4,6,8,10):
    h=s//2
    thmax=2*np.pi/(2*s-3)
    hits=[]
    ths=np.linspace(1e-4,thmax*(1-1e-9),200001)
    for sign in (+1,-1):
        vals=[]
        for th in ths:
            ph=(s-1)*th/2
            # t^2 - 2 t cos ph + 1 - c2(1) = 0
            B=-2*np.cos(ph); C=1-c2(1,th); D=B*B-4*C
            if D<0: vals.append(np.full(h-1,np.nan)); continue
            t=(-B+sign*np.sqrt(D))/2
            r=[1+t*t-2*t*np.cos((2*k-1)*th/2)-c2(s+1-2*k,th) for k in range(1,h)]
            vals.append(np.array(r))
        V=np.array(vals)
        # common near-zeros of all residuals
        tot=np.nanmax(np.abs(V),axis=1)
        i=np.nanargmin(tot)
        print(f"s={s} sign={sign}: min over theta of max|res| = {tot[i]:.3e} at theta={ths[i]:.6f} (thmax {thmax:.4f})")
