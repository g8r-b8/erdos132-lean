"""R6-B-gap/X: non-symmetric greedy max-contact completion inside a convex K (disk of radius R, or lens),
restricted to a band of depth w below the boundary (w = inf: whole K).  Spatial hash, lazy max-heap.
Seeds: a first layer on the boundary (A-points and explicit rung ends).  Float, TOL = 1e-9.
Reports Def = sum(6-deg)/2 = 3n - E, |A|, Def-2|A|, the Euler floor for bands, and a row profile."""
import math, cmath, heapq, random, sys, json

TOL = 1e-9

class Region:
    """disk: K = {|z| <= R}.  lens: K = D(c1,R) cap D(c2,R), c1 = -i(R - w/2), c2 = +i(R - w/2)."""
    def __init__(s, kind, R, width=None):
        s.kind, s.R = kind, R
        if kind == 'lens':
            s.c = [complex(0, -(R - width/2)), complex(0, R - width/2)]
    def depth(s, z):          # distance to boundary (>= 0 inside)
        if s.kind == 'disk': return s.R - abs(z)
        return min(s.R - abs(z - c) for c in s.c)
    def on_boundary(s, z):
        return abs(s.depth(z)) < TOL

class Packing:
    def __init__(s, region, wband=float('inf'), minsc=2, allowA=False, seed=0):
        s.K, s.w, s.minsc, s.allowA = region, wband, minsc, allowA
        s.pts = []; s.grid = {}
        s.heap = []; s.rng = random.Random(seed)
    def cell(s, z): return (math.floor(z.real), math.floor(z.imag))
    def near(s, z, r=2.0):
        cx, cy = s.cell(z); k = int(math.ceil(r))
        for i in range(cx-k, cx+k+1):
            for j in range(cy-k, cy+k+1):
                for idx in s.grid.get((i, j), ()):
                    if abs(s.pts[idx]-z) <= r + 1e-12: yield idx
    def valid(s, z):
        d = s.K.depth(z)
        if d < -TOL or d > s.w + TOL: return False
        if d < TOL and not s.allowA_now: return False
        for i in s.near(z, 1.0):
            if abs(s.pts[i]-z) < 1-TOL: return False
        return True
    def score(s, z):
        return sum(1 for i in s.near(z, 1.0+1e-6) if abs(abs(s.pts[i]-z)-1) < TOL)
    def add(s, z, gen=True):
        idx = len(s.pts); s.pts.append(z)
        s.grid.setdefault(s.cell(z), []).append(idx)
        if gen: s.gen(idx)
        return idx
    def gen(s, idx):
        p = s.pts[idx]
        for j in list(s.near(p, 2.0)):
            if j == idx: continue
            q = s.pts[j]; d = abs(p-q)
            if d > 2+TOL or d < 1e-12: continue
            m = (p+q)/2; h = math.sqrt(max(0.0, 1-(d/2)**2)); u = (q-p)/d*1j
            for z in ((m+h*u, m-h*u) if h > 1e-9 else (m,)):
                s.push(z)
        if s.allowA:
            for z in s.boundary_hits(p): s.push(z)
    def boundary_hits(s, p):
        out = []
        cs = [0j] if s.K.kind == 'disk' else s.K.c
        for c in cs:
            r = abs(p-c)
            if r < 1e-9: continue
            cc = (s.K.R**2 + r**2 - 1)/(2*s.K.R*r)
            if abs(cc) <= 1:
                a = math.acos(cc); ph = cmath.phase(p-c)
                for sg in (1, -1):
                    z = c + s.K.R*cmath.exp(1j*(ph+sg*a))
                    if s.K.depth(z) > -TOL: out.append(z)
        return out
    def push(s, z):
        d = s.K.depth(z)
        if d < -TOL or d > s.w + TOL: return
        sc = s.score(z)
        if sc < s.minsc: return
        heapq.heappush(s.heap, (-sc, -s.key2(z), s.rng.random(), z.real, z.imag))
    def key2(s, z):   # tie-break: outermost first (smallest depth)
        return -s.K.depth(z)
    def run(s, maxadd=10**7):
        s.allowA_now = s.allowA
        added = 0
        while s.heap and added < maxadd:
            negsc, _, _, x, y = heapq.heappop(s.heap)
            z = complex(x, y)
            if not s.valid(z): continue
            sc = s.score(z)
            if sc < s.minsc: continue
            if sc != -negsc:
                heapq.heappush(s.heap, (-sc, -s.key2(z), s.rng.random(), x, y)); continue
            s.add(z); added += 1
        return added
    def stats(s, rowh=math.sqrt(3)/2):
        n = len(s.pts); E = 0; deg = [0]*n; near = 0; mind = 9
        for i, p in enumerate(s.pts):
            for j in s.near(p, 1.0+1e-6):
                if j <= i: continue
                d = abs(p - s.pts[j]); mind = min(mind, d)
                if abs(d-1) < TOL: E += 1; deg[i] += 1; deg[j] += 1
                elif abs(d-1) < 1e-6: near += 1
        A = [i for i in range(n) if s.K.on_boundary(s.pts[i])]
        Def = 3*n - E
        dep = [s.K.depth(p) for p in s.pts]
        dmax = max(dep)
        prof = {}
        for i in range(n):
            b = int(dep[i]/rowh + 0.5)
            prof.setdefault(b, [0, 0.0]); prof[b][0] += 1; prof[b][1] += (6-deg[i])/2
        Adeg = {}
        for i in A: Adeg[deg[i]] = Adeg.get(deg[i], 0) + 1
        return dict(n=n, E=E, A=len(A), Def=Def, DefMinus2A=Def-2*len(A), mind=round(mind, 12), nearmiss=near,
                    Adeg=Adeg, dmax=dmax, prof=prof, deg=deg)

def seed_disk_pattern(P, R, N, start=0.0):
    """repeat the tri(N) first layer (from r6_gap_X_seeds.tri_path) around the circle by rotation;
    uses the exact local period; the last gap absorbs the remainder (one defect)."""
    from r6_gap_X_seeds import tri_path
    Pp, B, qR, per = tri_path(R, N)
    k = int(2*math.pi // per)
    for j in range(k):
        rot = cmath.exp(-1j*per*j)
        for z in Pp + B + [qR]:
            zz = z*rot
            if all(abs(zz - P.pts[i]) > 1-1e-9 for i in P.near(zz, 1.0)):
                P.add(zz, gen=False)
    for i in range(len(P.pts)): P.gen(i)
    return k

if __name__ == '__main__':
    R = float(sys.argv[1]); N = int(sys.argv[2]); w = float(sys.argv[3])
    P = Packing(Region('disk', R), wband=w)
    k = seed_disk_pattern(P, R, N)
    P.run()
    st = P.stats(); st.pop('deg')
    st['R'] = R; st['N'] = N; st['w'] = w; st['paths'] = k
    st['euler_floor_band'] = -(2*math.pi*st['dmax'] + 6)
    print(json.dumps(st, default=str))
