"""Exhaustive search for the LOCAL configuration forbidden by Lemma F of VERIFY_A1c.md.

Lemma F (4-neighbour form).  Delta2 = 1.  a1, a2, w, c are Delta2-neighbours of p lying in
an open half-plane at p; a1, a2 are strictly on one side of line pw, c strictly on the
other; r != p, |rw| = 1, r not strictly on the a-side.  Then {p,a1,a2,w,c,r} cannot have
all pairwise distances in [0,1] u {Delta} for a single Delta > 1.

All such configurations have p = 0 and a1, a2, w, c, r - w unit vectors, so we search
over a finite set C of unit vectors (up to scale):
  * exact:  lattice points of norm R2 in Z[omega] ('tri') or Z[i] ('sq'), all R2 <= R2MAX;
  * float:  N-th roots of unity, 5 <= N <= NMAX (squared distances rounded to 1e-9),
            w fixed to 1 by rotation symmetry.
Control mode ('ctl' as last arg) drops a2 and c (configurations p, a1, w, r with r on the
far side); such configurations exist (e.g. regular-hexagon pieces), so hits MUST appear.
This shows the search is live.
usage: python3 va1c_local.py tri R2MAX [ctl] | sq R2MAX [ctl] | cyc NMAX [ctl]
"""
import sys, math, itertools
from va1_common import qform


def run(C, d2, side, E, name, fix_w, control):
    """C: unit vectors (lattice or float coords); d2: exact squared distance;
    side(a,b): sign of cross(a,b) w.r.t. p = 0; E: map to Euclidean coords (angles only)."""
    one = d2((0, 0), C[0])
    zero = (0, 0)
    hits = examined = 0
    for w in (C[:1] if fix_w else C):
        for u in C:
            r = (w[0] + u[0], w[1] + u[1])
            if d2(r, zero) == 0:
                continue
            sr = side(w, r)
            for s_a in ([-sr] if sr != 0 else [1, -1]):
                A = [a for a in C if side(w, a) == s_a]
                if control:     # drop a2 and c: configurations p, a1, w, r
                    tuples = [(a1,) for a1 in A]
                else:
                    Cc = [c for c in C if side(w, c) == -s_a]
                    tuples = [(a1, a2, c) for a1, a2 in itertools.combinations(A, 2) for c in Cc]
                for T in tuples:
                    nb = list(T) + [w]
                    angs = sorted(math.atan2(E(v)[1], E(v)[0]) % (2 * math.pi) for v in nb)
                    k = len(angs)
                    gaps = [(angs[(i + 1) % k] - angs[i]) % (2 * math.pi) for i in range(k)]
                    if max(gaps) <= math.pi + 1e-9:        # not in an open half-plane
                        continue
                    examined += 1
                    pts = [zero, w, r] + list(T)
                    big = {d2(pts[i], pts[j]) for i in range(len(pts)) for j in range(i + 1, len(pts))}
                    if len({s for s in big if s > one}) <= 1:
                        hits += 1
    print(f'{name}: |C|={len(C)} examined={examined} hits={hits}')
    return examined, hits


def lattice(kind, R2MAX, control):
    tot = th = 0
    E = (lambda v: (v[0] + v[1] / 2, v[1] * math.sqrt(3) / 2)) if kind == 'tri' else (lambda v: v)
    d2 = lambda p, q: qform(kind, p[0] - q[0], p[1] - q[1])

    def side(a, b):  # orientation in (a,b) coords = Euclidean orientation (basis det > 0)
        x = a[0] * b[1] - a[1] * b[0]
        return (x > 0) - (x < 0)
    for R2 in range(1, R2MAX + 1):
        R = math.isqrt(4 * R2) + 2
        C = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1) if qform(kind, a, b) == R2]
        if len(C) < 3:
            continue
        e, h = run(C, d2, side, E, f'{kind} R2={R2}', False, control)
        tot += e; th += h
    print('TOTAL examined', tot, 'hits', th)


def cyclo(NMAX, control):
    tot = th = 0
    d2 = lambda p, q: round((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2, 9)

    def side(a, b):
        x = a[0] * b[1] - a[1] * b[0]
        return 0 if abs(x) < 1e-9 else (1 if x > 0 else -1)
    for N in range(5, NMAX + 1):
        C = [(math.cos(2 * math.pi * k / N), math.sin(2 * math.pi * k / N)) for k in range(N)]
        e, h = run(C, d2, side, lambda v: v, f'cyc N={N}', True, control)
        tot += e; th += h
    print('TOTAL examined', tot, 'hits', th)


if __name__ == '__main__':
    control = sys.argv[-1] == 'ctl'
    if sys.argv[1] == 'cyc':
        cyclo(int(sys.argv[2]), control)
    else:
        lattice(sys.argv[1], int(sys.argv[2]), control)
