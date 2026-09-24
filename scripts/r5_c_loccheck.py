"""R5/C: exact adversarial check of the Localisation lemma (strong form) and the Delta_3 depth-type
structure, on random subsets of small integer grids (many collinear / cocircular coincidences).

Checked, for every x of depth d >= 2 and every y != x (both layer conventions: 'strict' = extreme
points only; 'bdry' = all points on the hull boundary):
  (L)  some z in L_{d-1} lies in H_x(y) = {z : (z-x).(x-y) >= 0}, z != x, and |zy| > |xy|;
  (S)  every Delta_j pair has depth sum <= j+1;
  (T22) Delta_3 pair with both depths 2: every z != x in H_x(y) lies in L_1 and |zy| = Delta_2;
  (T13) Delta_3 pair (x in L_3, y in L_1): every z != x of depth >= 2 in H_x(y) has depth 2 and
        |zy| = Delta_2, and there is at least one such z.
Everything is exact integer arithmetic.
Usage: python3 r5_c_loccheck.py trials
"""
import sys, random, itertools


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull(pts, idx, conv):
    idx = sorted(set(idx), key=lambda i: pts[i])
    if len(idx) <= 2:
        return set(idx)
    # collinear?
    if all(cross(pts[idx[0]], pts[idx[1]], pts[i]) == 0 for i in idx):
        return set(idx) if conv == 'bdry' else {idx[0], idx[-1]}
    strict = (conv == 'strict')
    lo, up = [], []
    for i in idx:
        while len(lo) >= 2 and (cross(pts[lo[-2]], pts[lo[-1]], pts[i]) <= 0 if strict else cross(pts[lo[-2]], pts[lo[-1]], pts[i]) < 0):
            lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up) >= 2 and (cross(pts[up[-2]], pts[up[-1]], pts[i]) <= 0 if strict else cross(pts[up[-2]], pts[up[-1]], pts[i]) < 0):
            up.pop()
        up.append(i)
    return set(lo[:-1] + up[:-1])


def depths(pts, conv):
    rem = list(range(len(pts))); d = {}; k = 1
    while rem:
        L = hull(pts, rem, conv)
        for i in L:
            d[i] = k
        rem = [i for i in rem if i not in L]; k += 1
    return d


def sq(a, b):
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2


def check(pts, conv, stats):
    n = len(pts)
    d = depths(pts, conv)
    vals = sorted({sq(pts[i], pts[j]) for i in range(n) for j in range(i + 1, n)}, reverse=True)
    rank = {v: r + 1 for r, v in enumerate(vals)}
    for x in range(n):
        if d[x] < 2:
            continue
        for y in range(n):
            if y == x:
                continue
            X, Y = pts[x], pts[y]
            H = [z for z in range(n) if z != x and (pts[z][0] - X[0]) * (X[0] - Y[0]) + (pts[z][1] - X[1]) * (X[1] - Y[1]) >= 0]
            assert all(sq(pts[z], Y) > sq(X, Y) for z in H), ('L-ineq', pts, x, y)
            assert any(d[z] == d[x] - 1 for z in H), ('L-witness', conv, pts, x, y)
            stats['L'] += 1
    for i in range(n):
        for j in range(i + 1, n):
            r = rank[sq(pts[i], pts[j])]
            assert d[i] + d[j] <= r + 1, ('S', conv, pts, i, j, r)
            stats['S'] += 1
            if r == 3 and len(vals) >= 3:
                D2 = vals[1]
                for x, y in ((i, j), (j, i)):
                    X, Y = pts[x], pts[y]
                    H = [z for z in range(n) if z != x and (pts[z][0] - X[0]) * (X[0] - Y[0]) + (pts[z][1] - X[1]) * (X[1] - Y[1]) >= 0]
                    if d[x] == 2 and d[y] == 2:
                        assert H and all(d[z] == 1 and sq(pts[z], Y) == D2 for z in H), ('T22', conv, pts, x, y)
                        stats['T22'] += 1
                    if d[x] == 3 and d[y] == 1:
                        deep = [z for z in H if d[z] >= 2]
                        assert deep and all(d[z] == 2 and sq(pts[z], Y) == D2 for z in deep), ('T13', conv, pts, x, y)
                        stats['T13'] += 1


if __name__ == "__main__":
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(7)
    from collections import Counter
    stats = Counter()
    for t in range(T):
        G = rng.choice([3, 4, 5, 6, 8])
        n = rng.randint(5, min(14, (G + 1) ** 2))
        pts = rng.sample([(a, b) for a in range(G + 1) for b in range(G + 1)], n)
        for conv in ('strict', 'bdry'):
            check(pts, conv, stats)
    print("all checks passed:", dict(stats))
