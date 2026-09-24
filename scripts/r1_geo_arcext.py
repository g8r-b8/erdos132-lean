"""Arc of R_{2m+1}: U = vertices 0..m+1 (m+2 consecutive). Find all points w beyond chord (0,m+1)
(cap side), strictly inside the disk (or on it), with |wu|<=c_m for all u in U, U+{w} strictly convex,
and all |wu| in chords U {x} for a single non-chord x (x may be absent). mpmath 50 digits (sanity only)."""
import sys, itertools
from mpmath import mp, mpf, cos, sin, pi, sqrt, atan2
mp.dps = 50
TOL = mpf(10)**-30
def run(m, verbose=True):
    M = 2*m+1
    P = [(cos(2*pi*k/M), sin(2*pi*k/M)) for k in range(M)]
    U = P[:m+2]
    ch = [2*sin(pi*j/M) for j in range(1, m+1)]
    def d(a,b): return sqrt((a[0]-b[0])**2+(a[1]-b[1])**2)
    def cr(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    def rank(v):
        for j,c in enumerate(ch):
            if abs(v-c) < TOL: return j+1
        return None
    cands = []
    for a in range(m+2):
        for b in range(a+1, m+2):
            for i in range(m):
                for j in range(m):
                    A, B = U[a], U[b]; r0, r1 = ch[i], ch[j]
                    D = d(A,B)
                    if D > r0+r1 or D < abs(r0-r1): continue
                    t = (r0**2 - r1**2 + D**2)/(2*D)
                    h2 = r0**2 - t**2
                    if h2 < 0: h2 = mpf(0)
                    h = sqrt(h2)
                    ex, ey = (B[0]-A[0])/D, (B[1]-A[1])/D
                    for s in (1,-1):
                        w = (A[0]+t*ex - s*h*ey, A[1]+t*ey + s*h*ex)
                        # cap side of chord U[m+1]->U[0]: opposite side from U[1]
                        if cr(U[m+1], U[0], w) * cr(U[m+1], U[0], U[1]) >= -TOL: continue
                        # convexity: w must be outside conv, and U+{w} convex: check w strictly on outer side of
                        # lines U[m]U[m+1] extended? require polygon U0..U_{m+1}, w strictly convex
                        poly = U + [w]
                        ok = True
                        L = len(poly)
                        for k in range(L):
                            if cr(poly[k], poly[(k+1)%L], poly[(k+2)%L]) <= TOL: ok=False;break
                        if not ok: continue
                        ds = [d(w,u) for u in U]
                        if max(ds) > ch[-1] + TOL: continue
                        rk = [rank(v) for v in ds]
                        xs = [v for v,r in zip(ds,rk) if r is None]
                        if xs and max(xs)-min(xs) > TOL: continue
                        key = (round(float(w[0]),12), round(float(w[1]),12))
                        cands.append((key, rk, (float(xs[0]) if xs else None), float(sqrt(w[0]**2+w[1]**2))))
    uniq = {}
    for c in cands: uniq[c[0]] = c
    if verbose:
        print(f"m={m}: {len(uniq)} candidate w")
        for k,c in sorted(uniq.items()):
            print("  w=",k," |w|=%.6f"%c[3]," ranks along U:",c[1]," x=",c[2])
    return uniq
if __name__ == "__main__":
    for m in range(int(sys.argv[1]), int(sys.argv[2])+1): run(m)
