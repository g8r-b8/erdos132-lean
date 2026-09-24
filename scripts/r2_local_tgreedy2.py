"""Variant of r2_local_tgreedy: diverse seeds, score = (t, #hull vertices with deg_G>=3, mu-n)."""
import random, math, itertools, sys
from r2_local_tgreedy import ci, ok_add, stats, TOL
def score(X):
    t, mu, core, H, adj = stats(X)
    h3 = sum(1 for v in H if len(adj[v]) >= 3)
    return (t, h3, mu-len(X))
def seed(D, rng):
    k = rng.choice([0, 1, 2])
    if k == 0:
        X = [(0.0, 0.0), (D, 0.0)]; X += ci(X[0], X[1], 1, 1)[:1]
    elif k == 1:  # Reuleaux triangle of width D
        X = [(0.0, 0.0), (D, 0.0), (D/2, D*math.sqrt(3)/2)]
    else:  # Delta-pair plus a point at distance D from one end, 1 from the other
        X = [(0.0, 0.0), (D, 0.0)]; X += ci(X[0], X[1], D, 1)[:1]
    return X
def run(D, steps, rng, eps):
    X = seed(D, rng)
    for _ in range(steps):
        cands = []
        for i, j in itertools.combinations(range(len(X)), 2):
            for r1, r2 in ((1, 1), (1, D), (D, 1), (D, D)):
                for p in ci(X[i], X[j], r1, r2):
                    if ok_add(X, p, D): cands.append(p)
        for i in range(len(X)):
            for _k in range(15):
                th = rng.uniform(0, 2*math.pi)
                for r in (1.0, D):
                    p = (X[i][0]+r*math.cos(th), X[i][1]+r*math.sin(th))
                    if ok_add(X, p, D): cands.append(p)
        if not cands: break
        if rng.random() < eps: X.append(rng.choice(cands)); continue
        sc = sorted(((score(X+[p]), rng.random(), p) for p in cands), reverse=True)
        X.append(sc[0][2])
    return X
if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); trials = int(sys.argv[2]); steps = int(sys.argv[3])
    hist = {}; best = (-1,)
    for tr in range(trials):
        D = rng.uniform(1.01, 1.95); X = run(D, steps, rng, 0.15)
        ds = sorted({round(math.dist(a, b), 7) for a, b in itertools.combinations(X, 2)})
        if len(ds) < 2 or abs(ds[-2]-1) > 1e-6 or abs(ds[-1]-D) > 1e-6: continue
        t = stats(X)[0]; hist[t] = hist.get(t, 0)+1
        if t > best[0]: best = (t, D, X)
    print('hist', hist); print('BEST', best[0], best[1]); print(best[2])
