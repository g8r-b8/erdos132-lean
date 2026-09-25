"""Check of the aspect-ratio lemma: X with all pairwise distances <= c*r (c = 1.94),
K = cap_{x in X} D(x, r).  Claim (proved in X_report.md, Lemma F): diam(K)/minwidth(K) <= 100 (crude);
here we search adversarially for the largest ratio. Float, polygonal approximation of the disks (2000-gons)."""
import math, random
def clip(poly, c, r, m=2000):
    # intersect convex polygon with disk (approximated by circumscribed-ish m-gon: use halfplanes tangent)
    for k in range(m):
        a = 2*math.pi*k/m; ux, uy = math.cos(a), math.sin(a)
        b = ux*c[0] + uy*c[1] + r
        out = []
        n = len(poly)
        for i in range(n):
            P = poly[i]; Q = poly[(i+1) % n]
            fp = ux*P[0]+uy*P[1]-b; fq = ux*Q[0]+uy*Q[1]-b
            if fp <= 0: out.append(P)
            if (fp < 0) != (fq < 0) and fp != fq:
                t = fp/(fp-fq); out.append((P[0]+t*(Q[0]-P[0]), P[1]+t*(Q[1]-P[1])))
        poly = out
        if not poly: return []
    return poly
def ratio(poly):
    diam = max(math.dist(p, q) for p in poly for q in poly)
    wmin = 1e18
    for k in range(720):
        a = math.pi*k/720; ux, uy = math.cos(a), math.sin(a)
        pr = [ux*p[0]+uy*p[1] for p in poly]
        wmin = min(wmin, max(pr)-min(pr))
    return diam, wmin
rng = random.Random(1)
r = 1.0; c = 1.94
best = (0, None)
def trial(X):
    if any(math.dist(p, q) > c*r + 1e-12 for p in X for q in X): return None
    poly = [(-3, -3), (3, -3), (3, 3), (-3, 3)]
    for x in X:
        poly = clip(poly, x, r, m=720)
        if not poly: return None
    d, w = ratio(poly)
    return d/w if w > 1e-9 else None
# adversarial families: two antipodal-ish centres at distance c*r plus k random extra centres
for it in range(300):
    k = rng.choice([0, 1, 2, 3, 5])
    th = rng.uniform(0, math.pi)
    X = [(0.97*r, 0), (-0.97*r, 0)]
    for _ in range(k):
        X.append((rng.uniform(-0.97, 0.97)*r, rng.uniform(-0.6, 0.6)*r))
    q = trial(X)
    if q and q > best[0]: best = (q, X); print(round(q, 3), len(X), flush=True)
print('max ratio found', best[0])
