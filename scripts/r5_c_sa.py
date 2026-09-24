"""R5/C: simulated annealing over n-subsets of a point pool, objectives on the TOP distances.

Pools:  tri R   -> Eisenstein lattice a + b w (|.|^2 = a^2+ab+b^2 <= R^2), exact integer norms
        sq R    -> Gaussian lattice (exact)
        cyc N d -> Z[zeta_N] points with <= d roots of unity (norms rounded to 1e-9; any record
                   must be re-checked exactly with r5_c_exact.py)
Objectives (mu_j = multiplicity of the j-th largest distance of the SUBSET):
   s23   : min(mu2, mu3) - n
   sum23 : mu2 + mu3 - 5n/2
   s234  : min(mu2, mu3, mu4) - n
   sum234: mu2 + mu3 + mu4 - 3n
   top3  : mu1 + mu2 + mu3 - 3n
Usage: python3 r5_c_sa.py kind param n obj iters seed [d]
"""
import sys, math, cmath, random
import numpy as np


def pool(kind, R, d=2):
    if kind == 'tri':
        P = [(a, b) for a in range(-R - 2, R + 3) for b in range(-R - 2, R + 3) if a * a + a * b + b * b <= R * R]
        xy = [(a + b / 2, b * math.sqrt(3) / 2) for a, b in P]
        def q(i, j):
            da, db = P[i][0] - P[j][0], P[i][1] - P[j][1]
            return da * da + da * db + db * db
        return xy, q
    if kind == 'sq':
        P = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1) if a * a + b * b <= R * R]
        def q(i, j):
            da, db = P[i][0] - P[j][0], P[i][1] - P[j][1]
            return da * da + db * db
        return [(float(a), float(b)) for a, b in P], q
    if kind == 'cyc':
        N = R
        z = [cmath.exp(2j * math.pi * a / N) for a in range(N)]
        pts = {0j}
        layer = [0j]
        for _ in range(d):
            layer = [p + w for p in layer for w in z]
            pts.update(layer)
        uniq = {}
        for p in pts:
            uniq[(round(p.real, 8), round(p.imag, 8))] = p
        xy = [(p.real, p.imag) for p in uniq.values()]
        def q(i, j):
            return round((xy[i][0] - xy[j][0]) ** 2 + (xy[i][1] - xy[j][1]) ** 2, 9)
        return xy, q
    raise ValueError(kind)


def class_matrix(xy, q):
    m = len(xy)
    vals = {}
    Q = [[None] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            v = q(i, j)
            Q[i][j] = Q[j][i] = v
            vals[v] = 1
    order = sorted(vals, reverse=True)  # class 0 = largest
    idx = {v: k for k, v in enumerate(order)}
    C = np.full((m, m), -1, dtype=np.int32)
    for i in range(m):
        for j in range(m):
            if i != j:
                C[i, j] = idx[Q[i][j]]
    return C, order


def score(cnt, n, obj):
    nz = np.flatnonzero(cnt)
    if len(nz) < 4:
        return -1e9, None
    mu = cnt[nz[:5]]
    m1, m2, m3, m4 = mu[0], mu[1], mu[2], mu[3]
    if obj == 's23':
        s = min(m2, m3) - n
    elif obj == 'sum23':
        s = m2 + m3 - 2.5 * n
    elif obj == 's234':
        s = min(m2, m3, m4) - n
    elif obj == 'sum234':
        s = m2 + m3 + m4 - 3 * n
    elif obj == 'top3':
        s = m1 + m2 + m3 - 3 * n
    else:
        raise ValueError(obj)
    # small tie-breaker towards larger top multiplicities
    return s + 1e-3 * (m2 + m3 + m4), list(map(int, mu))


def anneal(C, n, obj, iters, seed, T0=2.0):
    rng = random.Random(seed)
    m = C.shape[0]
    ncls = C.max() + 1
    S = rng.sample(range(m), n)
    inS = np.zeros(m, bool); inS[S] = True
    cnt = np.zeros(ncls, np.int64)
    for a in range(n):
        for b in range(a + 1, n):
            cnt[C[S[a], S[b]]] += 1
    cur, mu = score(cnt, n, obj)
    best = (cur, mu, sorted(S))
    Sarr = list(S)
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        k = rng.randrange(n)
        u = Sarr[k]
        v = rng.randrange(m)
        if inS[v]:
            continue
        others = [w for w in Sarr if w != u]
        ou = C[u, others]; ov = C[v, others]
        np.subtract.at(cnt, ou, 1); np.add.at(cnt, ov, 1)
        new, nmu = score(cnt, n, obj)
        if new >= cur or rng.random() < math.exp((new - cur) / T):
            Sarr[k] = v; inS[u] = False; inS[v] = True; cur, mu = new, nmu
            if cur > best[0]:
                best = (cur, mu, sorted(Sarr))
        else:
            np.add.at(cnt, ou, 1); np.subtract.at(cnt, ov, 1)
    return best


if __name__ == "__main__":
    kind = sys.argv[1]; R = int(sys.argv[2]); n = int(sys.argv[3]); obj = sys.argv[4]
    iters = int(sys.argv[5]); seed = int(sys.argv[6]); d = int(sys.argv[7]) if len(sys.argv) > 7 else 2
    xy, q = pool(kind, R, d)
    C, order = class_matrix(xy, q)
    b = anneal(C, n, obj, iters, seed)
    print(f"{kind} {R} d={d} pool={len(xy)} n={n} obj={obj} seed={seed}: best={b[0]:.3f} top mults={b[1]}")
    print("   subset:", [tuple(round(c, 6) for c in xy[i]) for i in b[2]])
