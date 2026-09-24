"""R5: multiplicity profiles (top distances) of known structured sets with mu(Delta2) > n.
Float with tolerance 1e-9 -- guidance only."""
import numpy as np, sys
def profile(X, top=8, tol=1e-9):
    X=np.asarray(X,float); n=len(X)
    D=np.sqrt(((X[:,None]-X[None])**2).sum(-1)); iu=np.triu_indices(n,1); d=np.sort(D[iu])[::-1]
    vals=[];mult=[]
    for x in d:
        if vals and abs(vals[-1]-x)<tol: mult[-1]+=1
        else: vals.append(x); mult.append(1)
    return n, vals, mult
def show(name,X,top=8):
    n,v,m=profile(X)
    rare=[i for i in range(1,len(m)) if m[i]<=n]
    print(f"{name}: n={n} D={len(m)} top mults={m[:top]} min-mult={min(m)} delta-mult={m[-1]} first rare non-diam idx={rare[:3]}")
def ring(m, servers='all', extra=None):
    V=[(np.cos(2*np.pi*j/m),np.sin(2*np.pi*j/m)) for j in range(m)]
    V=np.array(V)
    # Delta2 of the polygon
    if m%2==0: D2=2*np.cos(np.pi/m)
    else: D2=2*np.cos(3*np.pi/(2*m))  # odd: Delta=2cos(pi/2m), next = 2cos(3pi/2m)
    S=[]
    for j in range(m):
        if servers=='alt' and j%2: continue
        th=2*np.pi*(j+.5)/m; u=np.array([np.cos(th),np.sin(th)])
        a=V[j]; # s=-t u with |s-a|=D2 ; |a|=1, a.u = cos(pi/m)
        c=a@u; # |-t u - a|^2 = t^2 + 2 t c + 1 = D2^2
        t=-c+np.sqrt(c*c-1+D2**2); S.append(-t*u)
    return np.vstack([V,np.array(S)]) if S else V
if __name__=="__main__":
    for m in [7,9,11,15,21]:
        show(f"R_{m}",ring(m,servers=None) if False else np.array([(np.cos(2*np.pi*j/m),np.sin(2*np.pi*j/m)) for j in range(m)]))
    for m in [8,10,12,16,20,30]:
        show(f"even ring m={m} all servers",ring(m))
        show(f"even ring m={m} alt servers",ring(m,'alt'))
    for m in [9,11,15,21]:
        show(f"odd ring m={m} all servers",ring(m))
