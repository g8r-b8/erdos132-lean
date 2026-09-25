"""R6-B-gap/X adversary: M-fold symmetric greedy max-contact band on a circle of radius R.
Float search (tolerance 1e-9); verification of chosen instances in r6_gap_X_verify.py (60-digit Decimal).

A = points on the circle |z| = R, B = points with R - w <= |z| < R.
Seeds: first-layer A-patterns (list of arc positions in one period) plus optional hand-placed B points.
Greedy: repeatedly add (the orbit of) the candidate point with the most unit contacts (>= minsc),
candidates = intersections of unit circles of existing points (B) and unit circle / Gamma (A, optional).
Output per period: |A|, Def = sum (6-deg)/2, Def-2|A|, row-resolved deficit, Euler checks.
"""
import cmath, math, sys, json

TOL = 1e-9

class Band:
    def __init__(s, R, M, w, allowA=False, minsc=2):
        s.R, s.M, s.w = R, M, w
        s.Th = 2*math.pi/M
        s.rot = [cmath.exp(1j*s.Th*j) for j in range(-3, 4)]
        s.F = []            # fundamental points
        s.allowA = allowA
        s.minsc = minsc
        s.log = []

    def canon(s, z):
        a = cmath.phase(z) % s.Th
        return abs(z)*cmath.exp(1j*a)

    def copies(s):
        return [z*r for r in s.rot for z in s.F]

    def ok(s, z, C=None):
        if C is None: C = s.copies()
        r = abs(z)
        if r > s.R + TOL or r < s.R - s.w - TOL: return False
        for y in C:
            if abs(z-y) < 1-TOL: return False
        for j in (1, 2, -1, -2):
            if abs(z - z*cmath.exp(1j*s.Th*j)) < 1-TOL: return False
        return True

    def score(s, z, C):
        return sum(1 for y in C if abs(abs(z-y)-1) < TOL)

    def add(s, z):
        s.F.append(s.canon(z))

    def candidates(s):
        C = s.copies()
        out = []
        for p in s.F:
            for q in C:
                d = abs(p-q)
                if d < 1e-12 or d > 2+TOL: continue
                m = (p+q)/2
                h2 = 1 - (d/2)**2
                h = math.sqrt(max(h2, 0))
                u = (q-p)/d*1j
                for z in ((m+h*u, m-h*u) if h > 1e-12 else (m,)):
                    if abs(z) < s.R - TOL: out.append(z)
            if s.allowA:  # unit circle around p meets Gamma
                r = abs(p)
                if r < 1e-9: continue
                c = (s.R**2 + r**2 - 1)/(2*s.R*r)
                if abs(c) <= 1:
                    a = math.acos(c); ph = cmath.phase(p)
                    for sg in (1, -1): out.append(s.R*cmath.exp(1j*(ph+sg*a)))
        return out, C

    def greedy(s, maxit=100000):
        it = 0
        while it < maxit:
            it += 1
            cand, C = s.candidates()
            best = None
            seen = []
            for z in cand:
                zc = s.canon(z)
                if any(abs(zc-y) < 1e-7 for y in seen): continue
                seen.append(zc)
                if not s.ok(zc, C): continue
                sc = s.score(zc, C)
                if sc < s.minsc: continue
                key = (sc, abs(zc), -cmath.phase(zc))
                if best is None or key > best[0]: best = (key, zc)
            if best is None: break
            s.add(best[1]); s.log.append(best[0][0])
        return s

    def stats(s, nbins=None):
        C = s.copies()
        deg = [sum(1 for y in C if abs(abs(z-y)-1) < TOL) for z in s.F]
        near = [(abs(z-y)) for z in s.F for y in C if 1e-12 < abs(abs(z-y)-1) < 1e-6]
        mind = min(abs(z-y) for z in s.F for y in C if abs(z-y) > 1e-12)
        A = [i for i, z in enumerate(s.F) if abs(abs(z)-s.R) < TOL]
        Def = sum(6-d for d in deg)/2
        depth = [s.R-abs(z) for z in s.F]
        rows = {}
        for i, z in enumerate(s.F):
            b = round(depth[i]/(math.sqrt(3)/2)*2)/2  # half-row bins
            rows.setdefault(b, [0, 0.0]); rows[b][0] += 1; rows[b][1] += (6-deg[i])/2
        # local measure: exclude points within 1.5 of the inner band edge
        dmax = max(depth)
        loc = sum((6-deg[i])/2 for i in range(len(s.F)) if depth[i] <= dmax-1.5)
        Adeg = sorted(deg[i] for i in A)
        return dict(nF=len(s.F), A=len(A), Def=Def, DefMinus2A=Def-2*len(A), Deflocal=loc,
                    locMinus2A=loc-2*len(A), mind=mind, nearmiss=len(near), Adeg=Adeg,
                    rows={k: rows[k] for k in sorted(rows)}, dmax=dmax,
                    totalDefMinus2A=s.M*(Def-2*len(A)), euler_floor=-(2*math.pi*dmax+6))

def arcpts(R, positions):
    """points on Gamma at arc-angle positions (radians)"""
    return [R*cmath.exp(1j*t) for t in positions]

def chord_angle(R, d=1.0):
    return 2*math.asin(d/(2*R))

def pattern(R, M, N, gapmode='min', extra=0.0):
    """one period = one T-path of N unit chords-points + gap. Returns angles.
    Period angle fixed = 2pi/M; the gap is whatever remains (must be >= chord(1))."""
    th = chord_angle(R)
    return [k*th for k in range(N)]

if __name__ == '__main__':
    R = float(sys.argv[1]); M = int(sys.argv[2]); w = float(sys.argv[3]); N = int(sys.argv[4])
    allowA = len(sys.argv) > 5 and sys.argv[5] == 'A'
    b = Band(R, M, w, allowA=allowA)
    th = chord_angle(R)
    gap = 2*math.pi/M - (N-1)*th
    print('period angle', b.Th, 'path', N, 'gap chord', 2*R*math.sin(gap/2))
    for z in arcpts(R, [k*th for k in range(N)]): b.add(z)
    b.greedy()
    st = b.stats()
    print(json.dumps(st, indent=1, default=str))
