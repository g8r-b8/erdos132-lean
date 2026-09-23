"""Referee check of the degenerate regime (Delta > 1.94 Delta2 => mu(Delta2) <= n+1), independent of degen_check.py.
Adversarial: y at origin, A on C(y,Delta) with the extreme pair at chord exactly Delta2 (so e(A)=1),
B = every pairwise intersection point of W-circles C(w,Delta2) (w in {y} u A) that lies in K, i.e. all
corners, plus random boundary points. Then brute-force all distances; keep only sets with no distance in
(Delta2, Delta) and Delta2 really the 2nd largest distance.
Also: random search for two disjoint diametral pairs with Delta > 1.94 Delta2 (should be impossible).
"""
import numpy as np
from math import *
rng = np.random.default_rng(11)
def circ_int(c1, c2, r):
    d = np.linalg.norm(c2-c1)
    if d > 2*r or d == 0: return []
    m = (c1+c2)/2; h = sqrt(max(0, r*r - d*d/4)); e = (c2-c1)/d; p = np.array([-e[1], e[0]])
    return [m + h*p, m - h*p]
worst = -99; tested = 0
for trial in range(3000):
    D2 = 1.0; D = rng.uniform(1.941, 3.0)*D2
    ang = 2*asin(D2/(2*D))  # angular span giving chord D2
    k = rng.integers(2, 7)
    angs = np.concatenate([[0, ang], rng.uniform(0, ang, k-2)])
    A = [D*np.array([cos(a), sin(a)]) for a in angs]
    W = [np.zeros(2)] + A
    inK = lambda x: all(np.linalg.norm(x-w) <= D2 + 1e-9 for w in W)
    B = []
    for i in range(len(W)):
        for j in range(i+1, len(W)):
            for x in circ_int(W[i], W[j], D2):
                if inK(x): B.append(x)
    # random extra points on boundary arcs
    for _ in range(rng.integers(0, 6)):
        w = W[rng.integers(len(W))]; th = rng.uniform(0, 2*pi); x = w + D2*np.array([cos(th), sin(th)])
        if inK(x): B.append(x)
    X = np.array(W + B)
    # dedupe
    keep = []
    for x in X:
        if all(np.linalg.norm(x-y) > 1e-7 for y in keep): keep.append(x)
    X = np.array(keep); n = len(X)
    if n < 4: continue
    Dm = np.linalg.norm(X[:, None]-X[None], axis=2)[np.triu_indices(n, 1)]
    if Dm.max() > D + 1e-9: continue
    if np.any((Dm > D2 + 1e-9) & (Dm < D - 1e-9)): continue
    mu = np.sum(np.abs(Dm - D2) < 1e-9); tested += 1
    worst = max(worst, mu - n)
print("degenerate adversarial sets tested:", tested, " max mu(Delta2) - n =", worst, "(claim <= 1)")
# disjoint diametral pairs with ratio > 1.94 via random optimisation
best = 0
for trial in range(200000):
    P = rng.normal(size=(4, 2))
    d = lambda i, j: np.linalg.norm(P[i]-P[j])
    # force pairs (0,1),(2,3) equal to the max
    ds = {(i, j): d(i, j) for i in range(4) for j in range(i+1, 4)}
    D = max(ds.values())
    if abs(ds[(0, 1)] - D) > 1e-9 or abs(ds[(2, 3)] - D) > 1e-9:
        # rescale pair (2,3) to length of (0,1) and see
        m = (P[2]+P[3])/2; v = (P[3]-P[2]); v = v/np.linalg.norm(v)*ds[(0, 1)]/2
        P[2], P[3] = m - v, m + v
        ds = {(i, j): d(i, j) for i in range(4) for j in range(i+1, 4)}
        D = max(ds.values())
        if abs(ds[(0, 1)] - D) > 1e-9 or abs(ds[(2, 3)] - D) > 1e-9: continue
    others = sorted([x for k2, x in ds.items() if x < D - 1e-9])
    if not others: continue
    best = max(best, D/others[-1])
print("max Delta/Delta2 among random 4-sets with two disjoint diametral pairs:", best, "(must be <= 1/(2 sin 15deg) =", 1/(2*sin(radians(15))), ")")
