"""Angle B3: sanity checks that the constraints (T),(Q),(X) of b3_enum.py are satisfied by genuine convex
configurations with many repeated distances (so the enumeration is not vacuously over-pruned).

1. Every n-subset of V(R_N), N = n..2n+2, colour = rank of chord index (exact: chord lengths 2 sin(j pi/N) are
   strictly increasing in j <= N/2, so ranks are computed from integer indices, no floating point).
   (For n > 7 only N <= n+4, to keep the run short.)
2. Random strictly convex n-gons in general position (floating point is used only to rank distances that differ
   by > 1e-9; any near-tie sample is discarded).
3. The enumerator with F=0, D=3, n=7 must contain the colouring of R_7.
"""
import itertools, random, math, sys
from b3_enum import setup, ok, enumerate_colourings, profile_generic, dihedral_images

def check(n, col_of_pair):
    pairs, e, order, cons = setup(n)
    c = [col_of_pair(i, j) for i, j in pairs]
    D = max(c)
    bad = [k for step in cons for k in step if not ok(k, c, D)]
    return bad

def regular_subsets(n):
    tested = 0
    for N in range(n, (2 * n + 3) if n <= 7 else n + 5):
        for S in itertools.combinations(range(N), n):
            if S[0] != 0:
                continue
            idx = lambda i, j: min((S[j] - S[i]) % N, (S[i] - S[j]) % N)
            vals = sorted({idx(i, j) for i in range(n) for j in range(i + 1, n)})
            rk = {v: r + 1 for r, v in enumerate(vals)}
            bad = check(n, lambda i, j: rk[idx(i, j)])
            assert not bad, (N, S, bad[:3])
            tested += 1
    return tested

def random_convex(n, trials=3000, seed=1):
    rng = random.Random(seed); tested = 0
    while tested < trials:
        ang = sorted(rng.uniform(0, 2 * math.pi) for _ in range(n))
        rad = [1 + 0.3 * rng.random() for _ in range(n)]
        P = [(r * math.cos(a), r * math.sin(a)) for r, a in zip(rad, ang)]
        # strict convexity
        conv = all(((P[(i+1)%n][0]-P[i][0])*(P[(i+2)%n][1]-P[i][1]) - (P[(i+1)%n][1]-P[i][1])*(P[(i+2)%n][0]-P[i][0])) > 1e-6 for i in range(n))
        if not conv:
            continue
        d = {(i, j): math.dist(P[i], P[j]) for i in range(n) for j in range(i + 1, n)}
        v = sorted(d.values())
        if min(b - a for a, b in zip(v, v[1:])) < 1e-9:
            continue
        rk = {x: r + 1 for r, x in enumerate(v)}
        assert not check(n, lambda i, j: rk[d[(i, j)]])
        tested += 1
    return tested

if __name__ == '__main__':
    for n in (7, 11) if len(sys.argv) < 2 else map(int, sys.argv[1:]):
        print(f"n={n}: regular-polygon subsets OK: {regular_subsets(n)}; random convex OK: {random_convex(n, 500 if n > 7 else 3000)}")
    okf, prune = profile_generic(7, 3, 0)
    pairs, res, _ = enumerate_colourings(7, 3, okf, prune)
    r7 = tuple(min((j - i) % 7, (i - j) % 7) for i, j in pairs)
    print("n=7 D=3 F=0 colourings:", len(res), "; contains R_7:", r7 in res)
    for r in res: print('  ', ''.join(map(str, r)))
