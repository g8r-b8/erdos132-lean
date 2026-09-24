"""Greedy search (float, exploratory) for sets with no 4 concyclic, distances <=1 or =D,
maximising t = #{hull vertices of core degree 3 in the Delta2-graph}.  Usage: seed trials steps"""
import random, math, itertools, sys
TOL = 1e-9
def ci(p, q, r1, r2):
    d = math.dist(p, q)
    if d < 1e-12 or d > r1+r2 or d < abs(r1-r2): return []
    a = (r1*r1-r2*r2+d*d)/(2*d); h2 = r1*r1-a*a
    if h2 < 0: return []
    h = math.sqrt(h2); ex, ey = (q[0]-p[0])/d, (q[1]-p[1])/d
    mx, my = p[0]+a*ex, p[1]+a*ey
    return [(mx-h*ey, my+h*ex), (mx+h*ey, my-h*ex)]
def ccdet(a, b, c, d):
    m = [[p[0]-d[0], p[1]-d[1], (p[0]-d[0])**2+(p[1]-d[1])**2] for p in (a, b, c)]
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
def ok_add(X, p, D):
    for q in X:
        d = math.dist(p, q)
        if d < 1e-3: return False
        if abs(d-1) < TOL or abs(d-D) < TOL: continue
        if d > 1-1e-6: return False
    for tri in itertools.combinations(X, 3):
        if abs(ccdet(*tri, p)) < 1e-7: return False
    return True
def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def hull(P):
    idx = sorted(range(len(P)), key=lambda i: P[i]); lo, up = [], []
    for i in idx:
        while len(lo) >= 2 and cross(P[lo[-2]], P[lo[-1]], P[i]) <= 1e-12: lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up) >= 2 and cross(P[up[-2]], P[up[-1]], P[i]) <= 1e-12: up.pop()
        up.append(i)
    return set(lo[:-1]+up[:-1])
def stats(X):
    n = len(X); adj = {i: [j for j in range(n) if j != i and abs(math.dist(X[i], X[j])-1) < TOL] for i in range(n)}
    core = set(range(n)); ch = True
    while ch:
        ch = False
        for v in list(core):
            if sum(u in core for u in adj[v]) < 2: core.discard(v); ch = True
    H = hull(X); dc = {v: sum(u in core for u in adj[v]) for v in core}
    t = sum(1 for v in core if v in H and dc[v] == 3)
    mu = sum(len(a) for a in adj.values())//2
    return t, mu, core, H, adj
def run(D, steps, rng):
    X = [(0.0, 0.0), (D, 0.0)]; X += ci(X[0], X[1], 1, 1)[:1]
    for _ in range(steps):
        cands = []
        for i, j in itertools.combinations(range(len(X)), 2):
            for r1, r2 in ((1, 1), (1, D), (D, 1)):
                for p in ci(X[i], X[j], r1, r2):
                    if ok_add(X, p, D): cands.append(p)
        for i in range(len(X)):
            for _k in range(25):
                th = rng.uniform(0, 2*math.pi)
                for r in (1.0, D):
                    p = (X[i][0]+r*math.cos(th), X[i][1]+r*math.sin(th))
                    if ok_add(X, p, D): cands.append(p)
        if not cands: break
        sc = []
        for p in cands:
            t, mu, *_ = stats(X+[p]); sc.append((t, mu - len(X) - 1 + rng.random()*0.5, p))
        sc.sort(reverse=True); X.append(sc[0][2])
    return X
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); trials = int(sys.argv[2]); steps = int(sys.argv[3])
    best = (-1,)
    for tr in range(trials):
        D = rng.uniform(1.02, 1.95); X = run(D, steps, rng)
        ds = sorted({round(math.dist(a, b), 7) for a, b in itertools.combinations(X, 2)})
        if abs(ds[-2]-1) > 1e-6 or abs(ds[-1]-D) > 1e-6: continue
        t, mu, core, H, adj = stats(X)
        print(f"trial {tr} D={D:.4f} n={len(X)} mu={mu} t={t} |H|={len(H)} core={len(core)}", flush=True)
        if t > best[0]: best = (t, D, X)
    print('BEST t', best[0], 'D', best[1]); print(best[2])
