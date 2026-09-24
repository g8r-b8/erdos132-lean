"""Sanity check for Lemma 'a=2 in B2': P' = R_{2m} or R_{2m+1} minus one vertex (on unit circle).
Find all points w (not on P', P' u {w} strictly convex) whose distances to P' are chord values of P'
except for exactly two P'-adjacent vertices at a common distance X > every chord value.
mpmath 40 digits, sanity only."""
import sys
from mpmath import mp, mpf, cos, sin, pi, sqrt
mp.dps=40; TOL=mpf(10)**-25
def hull_ok(pts):
    # strictly convex in given cyclic order? we sort by angle about centroid
    import math
    cx=sum(p[0] for p in pts)/len(pts); cy=sum(p[1] for p in pts)/len(pts)
    from mpmath import atan2
    q=sorted(pts,key=lambda p: atan2(p[1]-cy,p[0]-cx))
    L=len(q)
    for k in range(L):
        a,b,c=q[k],q[(k+1)%L],q[(k+2)%L]
        if (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]) <= TOL: return False
    return True
def run(m):
    out=[]
    for M in (2*m, 2*m+1):
        V=[(cos(2*pi*k/M), sin(2*pi*k/M)) for k in range(M)]
        Pp = V if M==2*m else V[1:]
        ch=sorted({2*sin(pi*j/M) for j in range(1,M//2+1)})
        d=lambda a,b: sqrt((a[0]-b[0])**2+(a[1]-b[1])**2)
        seen=set()
        for a in range(len(Pp)):
            for b in range(a+1,len(Pp)):
                for r0 in ch:
                    for r1 in ch:
                        A,B=Pp[a],Pp[b]; D=d(A,B)
                        if D>r0+r1+TOL or D<abs(r0-r1)-TOL: continue
                        t=(r0**2-r1**2+D**2)/(2*D); h2=r0**2-t**2; h=sqrt(max(h2,mpf(0)))
                        ex,ey=(B[0]-A[0])/D,(B[1]-A[1])/D
                        for s in (1,-1):
                            w=(A[0]+t*ex-s*h*ey, A[1]+t*ey+s*h*ex)
                            key=(round(float(w[0]),10),round(float(w[1]),10))
                            if key in seen: continue
                            seen.add(key)
                            ds=[d(w,u) for u in Pp]
                            if min(ds)<TOL: continue
                            non=[i for i,v in enumerate(ds) if min(abs(v-c) for c in ch)>TOL]
                            if len(non)!=2: continue
                            i,j=non
                            if abs(ds[i]-ds[j])>TOL or ds[i]<=ch[-1]: continue
                            if not ((j-i)%len(Pp) in (1,len(Pp)-1)): continue
                            if not hull_ok(Pp+[w]): continue
                            out.append((M,key))
    print(f"m={m}: solutions {out}")
for m in range(int(sys.argv[1]),int(sys.argv[2])+1): run(m)
