"""R5/C: local exhaustive test of the Delta_3 middle-neighbour lemma (Lemma F3).

Configuration: p = 0 extreme, b a Delta_3-neighbour of p, A = p's Delta_3-neighbours strictly on
one side (the side NOT strictly containing r), C = those strictly on the other side, r != p a
further Delta_3-neighbour of b, r not strictly on A's side.  All of p's neighbours lie in an open
half-plane (angular span < 180).  "Admissible": the squared distances among
{p} u A u {b} u C u {r} that exceed Delta_3^2 take at most TWO distinct values (Delta_2, Delta),
both > Delta_3^2 (all others <= Delta_3^2).

Lemma F3 (proved) says: no admissible configuration with |A| >= 3 and |C| >= 2.
We count admissible configurations for (|A|,|C|) = (3,2) [must be 0: sanity check of the proof]
and (2,2), (2,1), (3,1) [open / controls].

Pools (exact): Z[w] vectors of norm N (a^2+ab+b^2 = N), Z[i] vectors of norm N; roots of unity
(float, rounding 1e-9).
Usage: python3 r5_c_local.py
"""
import itertools, math
from collections import Counter


def tri_units(N):
    V = [(a, b) for a in range(-40, 41) for b in range(-40, 41) if a * a + a * b + b * b == N]
    xy = lambda v: (v[0] + v[1] / 2, v[1] * math.sqrt(3) / 2)
    q = lambda u, v: (u[0] - v[0]) ** 2 + (u[0] - v[0]) * (u[1] - v[1]) + (u[1] - v[1]) ** 2
    add = lambda u, v: (u[0] + v[0], u[1] + v[1])
    return V, xy, q, add


def sq_units(N):
    V = [(a, b) for a in range(-40, 41) for b in range(-40, 41) if a * a + b * b == N]
    xy = lambda v: (float(v[0]), float(v[1]))
    q = lambda u, v: (u[0] - v[0]) ** 2 + (u[1] - v[1]) ** 2
    add = lambda u, v: (u[0] + v[0], u[1] + v[1])
    return V, xy, q, add


def roots(M):
    V = [(round(math.cos(2 * math.pi * k / M), 12), round(math.sin(2 * math.pi * k / M), 12)) for k in range(M)]
    xy = lambda v: v
    q = lambda u, v: round((u[0] - v[0]) ** 2 + (u[1] - v[1]) ** 2, 9)
    add = lambda u, v: (u[0] + v[0], u[1] + v[1])
    return V, xy, q, add


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]


def ang(u):
    return math.atan2(u[1], u[0])


def run(pool, N, sizes):
    V, xy, q, add = pool
    zero = (0, 0) if not isinstance(V[0][0], float) else (0.0, 0.0)
    hits = Counter()
    examples = {}
    for b in V:
        bx = xy(b)
        # rotate so b is at angle 0; side of v: sign of cross(b, v)
        below = [v for v in V if cross(bx, xy(v)) < -1e-9]
        above = [v for v in V if cross(bx, xy(v)) > 1e-9]
        rs = []
        for u in V:
            r = add(b, u)
            if q(r, zero) == 0:
                continue
            if cross(bx, xy(r)) < -1e-9:  # r strictly below -> A must be 'above'; by symmetry we
                continue                  # only treat r not strictly below, A = below
            rs.append(r)
        def rel(v):  # signed angle from b
            a = ang(xy(v)) - ang(bx)
            return (a + math.pi) % (2 * math.pi) - math.pi
        for (na, nc) in sizes:
            for A in itertools.combinations(below, na):
                for Cc in itertools.combinations(above, nc):
                    angs = [rel(v) for v in A + Cc] + [0.0]
                    if max(angs) - min(angs) >= math.pi - 1e-9:
                        continue
                    S = [zero] + list(A) + [b] + list(Cc)
                    big = set()
                    ok = True
                    for s, t in itertools.combinations(S, 2):
                        d = q(s, t)
                        if d > N:
                            big.add(d)
                    if len(big) > 2:
                        continue
                    for r in rs:
                        bb = set(big)
                        good = True
                        for s in S:
                            if s == b or s == zero:
                                continue
                            d = q(r, s)
                            if d == 0:
                                good = False; break
                            if d > N:
                                bb.add(d)
                                if len(bb) > 2:
                                    good = False; break
                        if good and q(r, zero) > N:  # |rp| > Delta_3 allowed only as a big value
                            bb.add(q(r, zero))
                            good = len(bb) <= 2
                        if good:
                            hits[(na, nc)] += 1
                            examples.setdefault((na, nc), (b, A, Cc, r, sorted(bb)))
    return hits, examples


if __name__ == "__main__":
    sizes = [(3, 2), (2, 2), (3, 1), (2, 1)]
    jobs = [("Z[w] N=49", tri_units(49), 49), ("Z[w] N=91", tri_units(91), 91),
            ("Z[w] N=147", tri_units(147), 147), ("Z[i] N=25", sq_units(25), 25),
            ("Z[i] N=65", sq_units(65), 65), ("Z[i] N=325", sq_units(325), 325)]
    for M in range(5, 31):
        jobs.append((f"roots M={M}", roots(M), 1.0))
    tot = Counter()
    for name, pool, N in jobs:
        h, ex = run(pool, N, sizes)
        tot.update(h)
        print(name, "units:", len(pool[0]), "hits:", dict(h))
        for k, e in ex.items():
            if k in [(3, 2), (2, 2)]:
                print("    example", k, e)
    print("TOTAL", dict(tot))
