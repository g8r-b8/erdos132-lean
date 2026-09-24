"""R5/C common helpers: top-k distance graphs, convex layers (strict extreme points),
depth statistics.  Floating point with tolerance -- GUIDANCE ONLY; exact checks live in
r5_c_exact.py.
"""
import numpy as np
from collections import Counter, defaultdict

TOL = 1e-9


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull_vertices(P, idx):
    """strict extreme points of P[idx] (collinear boundary points excluded)"""
    idx = sorted(idx, key=lambda i: (round(P[i][0], 9), round(P[i][1], 9)))
    if len(idx) <= 2:
        return set(idx)
    lo, up = [], []
    for i in idx:
        while len(lo) >= 2 and cross(P[lo[-2]], P[lo[-1]], P[i]) <= 1e-9:
            lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up) >= 2 and cross(P[up[-2]], P[up[-1]], P[i]) <= 1e-9:
            up.pop()
        up.append(i)
    return set(lo[:-1] + up[:-1])


def depths(P):
    rem = list(range(len(P)))
    d = {}
    k = 1
    while rem:
        L = hull_vertices(P, rem)
        for i in L:
            d[i] = k
        rem = [i for i in rem if i not in L]
        k += 1
    return d


def dist_classes(P, tol=TOL):
    """returns list of (value, [pairs]) in decreasing order of distance"""
    P = np.asarray(P, float)
    n = len(P)
    D = np.sqrt(((P[:, None] - P[None]) ** 2).sum(-1))
    iu = np.triu_indices(n, 1)
    order = np.argsort(-D[iu])
    vals = []
    for o in order:
        i, j = iu[0][o], iu[1][o]
        x = D[i, j]
        if vals and abs(vals[-1][0] - x) < tol:
            vals[-1][1].append((i, j))
        else:
            vals.append([x, [(i, j)]])
    return vals


def mults(P):
    return [len(c[1]) for c in dist_classes(P)]


def report(name, P, K=5, verbose=True):
    P = np.asarray(P, float)
    n = len(P)
    cl = dist_classes(P)
    d = depths(P)
    lay = Counter(d.values())
    out = {'n': n, 'mults': [len(c[1]) for c in cl[:K + 2]], 'layers': dict(sorted(lay.items()))}
    for j in range(min(K, len(cl))):
        ds = Counter(tuple(sorted((d[a], d[b]))) for a, b in cl[j][1])
        deg = Counter()
        for a, b in cl[j][1]:
            deg[a] += 1
            deg[b] += 1
        bylayer = defaultdict(Counter)
        for v in range(n):
            bylayer[d[v]][deg[v]] += 1
        out[f'D{j+1}'] = {'mult': len(cl[j][1]), 'depthpairs': dict(ds),
                          'deg_by_layer': {k: dict(sorted(v.items())) for k, v in sorted(bylayer.items())}}
    if verbose:
        print(f"== {name}: n={n} mults={out['mults']} layers={out['layers']}")
        for j in range(min(K, len(cl))):
            o = out[f'D{j+1}']
            print(f"   D{j+1}: mu={o['mult']} depth-pairs={o['depthpairs']} deg-by-layer={o['deg_by_layer']}")
    return out


def reg(m, r=1.0, phase=0.0):
    return np.array([(r * np.cos(2 * np.pi * j / m + phase), r * np.sin(2 * np.pi * j / m + phase)) for j in range(m)])


def ring(m, servers='all'):
    """regular m-gon + CDL servers at distance Delta2 from both endpoints of an edge (as r5_profiles)"""
    V = reg(m)
    D2 = 2 * np.cos(np.pi / m) if m % 2 == 0 else 2 * np.cos(3 * np.pi / (2 * m))
    S = []
    for j in range(m):
        if servers == 'alt' and j % 2:
            continue
        th = 2 * np.pi * (j + .5) / m
        u = np.array([np.cos(th), np.sin(th)])
        a = V[j]
        c = a @ u
        t = -c + np.sqrt(c * c - 1 + D2 ** 2)
        S.append(-t * u)
    return np.vstack([V, np.array(S)]) if S else V
