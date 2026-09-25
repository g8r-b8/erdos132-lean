"""Greedy max-contact completion of prescribed A-row + first layer inside a disc of radius R.
Patterns: pairgap (A pairs, gaps 1+eps, apexes), period4 (coordinator), gapless (regular unit polygon, parallel-ish
rungs chosen by greedy), sqrt3 (isolated A at spacing ~sqrt3, 3 rungs by greedy).
Constraint: A-degree <= 3 (every point of the disc at distance 1 from a is in its open inner half-plane).
Reports Def(H) - 2|A|, with per-layer breakdown.  Floats: sanity only (tol 1e-9)."""
import math, cmath, sys, heapq
from collections import defaultdict
TOL = 1e-9
def apex(p, q, side_in=True, s=1.0):
    m = (p+q)/2; d = abs(q-p); h = math.sqrt(max(0.0, s*s-(d/2)**2)); n = -m/abs(m)
    return m + h*n
def pattern(name, R):
    A, B = [], []
    if name == 'pairgap':
        def build(L):
            a1 = 2*math.asin(1/(2*R)); aL = 2*math.asin(L/(2*R))
            P = [R*cmath.exp(-1j*t) for t in (0, a1, a1+aL, 2*a1+aL)]
            C = [apex(P[i], P[i+1]) for i in range(3)]
            return abs(C[1]-C[0]) - 1
        lo, hi = 1.0, 1.2
        for _ in range(200):
            mid = (lo+hi)/2
            if build(mid) < 0: lo = mid
            else: hi = mid
        L = hi; a1 = 2*math.asin(1/(2*R)); aL = 2*math.asin(L/(2*R))
        per = a1 + aL; N = int(2*math.pi/per)
        t = 0.0
        for k in range(N):
            A += [R*cmath.exp(-1j*t), R*cmath.exp(-1j*(t+a1))]; t += per
        # apexes over T-chords and over gap chords (skip the irregular closing gap unless valid)
        for i in range(len(A)):
            p, q = A[i], A[(i+1) % len(A)]
            if abs(q-p) < 2: B.append(apex(p, q))
    elif name == 'period4':
        th = 2*math.asin(1/(2*R))
        P = [R*cmath.exp(-1j*th*k) for k in range(4)]
        a12, a34 = apex(P[0], P[1]), apex(P[2], P[3])
        v = a34 - P[3]
        c1 = P[3] + v*cmath.exp(1j*math.pi/3); c2 = P[3] + v*cmath.exp(-1j*math.pi/3)
        qR = c1 if abs(c1-P[2]) > abs(c2-P[2]) else c2
        u = qR/abs(qR); mir = lambda z: u*u*z.conjugate()
        P2 = [mir(z) for z in reversed(P)]
        Phi = cmath.phase(P2[0]/P[0])       # rotation taking path k to path k+1
        N = int(2*math.pi/abs(Phi))
        for k in range(N):
            r = cmath.exp(1j*Phi*k)
            A += [z*r for z in P]; B += [a12*r, a34*r]
            if k < N-1: B.append(qR*r)
    elif name == 'gapless':
        N = int(math.pi/math.asin(1/(2*R)))
        Rr = 0.5/math.sin(math.pi/N)
        A = [Rr*cmath.exp(2j*math.pi*k/N) for k in range(N)]; R = Rr
    elif name == 'sqrt3':
        N = int(math.pi/math.asin(math.sqrt(3)/(2*R)))
        A = [R*cmath.exp(2j*math.pi*k/N) for k in range(N)]
    return A, B, R
def run(name, R, maxpts=10**6):
    A, B, R = pattern(name, R)
    pts = A + B; nA = len(A)
    grid = defaultdict(list)
    key = lambda z: (math.floor(z.real), math.floor(z.imag))
    def near(z, r=2):
        a, b = key(z)
        for dx in range(-r, r+1):
            for dy in range(-r, r+1):
                yield from grid.get((a+dx, b+dy), ())
    for i, z in enumerate(pts): grid[key(z)].append(i)
    deg = [0]*len(pts)
    for i, z in enumerate(pts):
        for j in near(z):
            if j > i:
                d = abs(pts[j]-z)
                if d < 1-1e-7: print('VIOLATION prescribed', i, j, d); return
                if abs(d-1) < TOL: deg[i] += 1; deg[j] += 1
    if max(deg[:nA]) > 3: print('A-degree >3 in prescribed'); return
    def valid(z):
        if abs(z) >= R - 1e-7: return None
        c = 0
        for j in near(z):
            d = abs(pts[j]-z)
            if d < 1-TOL: return None
            if d < 1+TOL:
                if j < nA and deg[j] >= 3: return None
                c += 1
        return c
    cand = {}
    heap = []
    def addcands(i):
        for j in near(pts[i]):
            if j == i: continue
            d = abs(pts[j]-pts[i])
            if 1e-9 < d < 2-1e-9:
                a = d/2; h = math.sqrt(1-a*a); e = (pts[j]-pts[i])/d; base = pts[i]+a*e
                for z in (base+1j*h*e, base-1j*h*e):
                    k = (round(z.real*1e6), round(z.imag*1e6))
                    if k in cand: continue
                    c = valid(z)
                    if c is not None:
                        cand[k] = z; heapq.heappush(heap, (-c, -abs(z), k))
    for i in range(len(pts)): addcands(i)
    added = 0
    while heap and added < maxpts:
        negc, negr, k = heapq.heappop(heap)
        if k not in cand: continue
        z = cand[k]; c = valid(z)
        if c is None: del cand[k]; continue
        if c != -negc: heapq.heappush(heap, (-c, -abs(z), k)); continue
        del cand[k]
        idx = len(pts); pts.append(z); deg.append(0); grid[key(z)].append(idx)
        for j in near(z):
            if j != idx and abs(abs(pts[j]-z)-1) < TOL: deg[j] += 1; deg[idx] += 1
        addcands(idx); added += 1
    n = len(pts); E = sum(deg)//2
    Def = 3*n - E
    defA = sum(3-deg[i]/2 for i in range(nA)); defB = Def - defA
    print(f'{name:8s} R={R:.2f} |A|={nA} n={n} E={E} Def={Def} Def-2|A|={Def-2*nA}  '
          f'defA={defA} defB={defB}  maxdegA={max(deg[:nA])}  Harborth sqrt(12n-3)={math.sqrt(12*n-3):.1f}')
    return pts, deg, nA
if __name__ == '__main__':
    R = float(sys.argv[1]) if len(sys.argv) > 1 else 20
    for nm in sys.argv[2:] or ['pairgap', 'period4', 'gapless', 'sqrt3']:
        run(nm, R)
