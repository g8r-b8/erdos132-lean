"""R5/C: exhaustive one/two-step augmentation of structured sets.
Candidate new points = intersections of circles (centre in X, radius among the top-K distances
of X).  A candidate is admissible if it creates no distance > Delta_K other than the existing
Delta_1..Delta_K values (so the ranking of the top K distances is preserved, although new
distances strictly between may appear -- we reject those too).  Float guidance only.
Usage: python3 r5_c_augment.py <m> <K> [steps]
"""
import sys, itertools
import numpy as np
from r5_c_common import ring, reg, dist_classes, report, TOL


def circ_int(p, r, q, s):
    d = np.linalg.norm(q - p)
    if d < 1e-12 or d > r + s + 1e-12 or d < abs(r - s) - 1e-12:
        return []
    a = (r * r - s * s + d * d) / (2 * d)
    h2 = r * r - a * a
    h = np.sqrt(max(h2, 0.0))
    u = (q - p) / d
    w = np.array([-u[1], u[0]])
    b = p + a * u
    return [b + h * w, b - h * w] if h > 1e-9 else [b]


def candidates(X, K):
    cl = dist_classes(X)
    vals = [c[0] for c in cl[:K]]
    n = len(X)
    seen = []
    out = []
    for a, b in itertools.combinations(range(n), 2):
        for r in vals:
            for s in vals:
                for c in circ_int(X[a], r, X[b], s):
                    d = np.linalg.norm(X - c, axis=1)
                    if d.min() < 1e-6:
                        continue
                    big = d[d > vals[-1] + TOL]
                    if not all(min(abs(x - v) for v in vals) < TOL for x in big):
                        continue
                    if any(np.linalg.norm(c - z) < 1e-7 for z in seen):
                        continue
                    seen.append(c)
                    gain = [int(np.sum(abs(d - v) < TOL)) for v in vals]
                    out.append((c, gain))
    return out, vals


if __name__ == "__main__":
    m = int(sys.argv[1]); K = int(sys.argv[2])
    X = ring(m)
    print("base", [len(c[1]) for c in dist_classes(X)[:K + 2]])
    cands, vals = candidates(X, K)
    print(len(cands), "admissible candidates")
    from collections import Counter
    C = Counter(tuple(g) for _, g in cands)
    for g, k in sorted(C.items(), key=lambda t: -sum(t[0][1:])):
        print("gain per D1..DK", g, "x", k)
