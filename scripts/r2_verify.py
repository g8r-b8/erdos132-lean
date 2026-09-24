"""R2 verifier: given a planar point set (high precision), report the C1 quantities.

Usage: python3 r2_verify.py points.txt [digits]
points.txt: one point per line, "x y" (decimal strings, as many digits as available).

Reports n, Δ, Δ₂, μ(Δ), μ(Δ₂), hull vertices, degrees in the Δ₂-graph G and its 2-core G',
t = #hull vertices of G'-degree 3, the gap between Δ₂ and the next distance, and the minimum
normalised concyclicity determinant over all 4-subsets (and min |orientation| over triples).
Equality classes use tolerance 10^(-digits/2); a certificate needs the equalities to be ~1e-40
while all margins are >> that. Exploratory verification, not a proof of exactness.
"""
import sys, itertools
from mpmath import mp, mpf, sqrt, fabs


def load(path):
    P = []
    for line in open(path):
        s = line.split()
        if len(s) >= 2:
            P.append((mpf(s[0]), mpf(s[1])))
    return P


def d2(a, b):
    return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2


def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def hull_vertices(P):
    """Strict extreme points (collinear boundary points excluded)."""
    n = len(P); H = []
    for i in range(n):
        # i is extreme iff some direction has P[i] as unique maximiser; test via angular gap
        import math
        angs = sorted(float(mp.atan2(P[j][1] - P[i][1], P[j][0] - P[i][0])) for j in range(n) if j != i)
        gaps = [angs[k + 1] - angs[k] for k in range(len(angs) - 1)] + [angs[0] + 2 * math.pi - angs[-1]]
        if max(gaps) > math.pi + 1e-12:
            H.append(i)
    return H


def core(n, E):
    adj = {i: set() for i in range(n)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    alive = set(i for i in range(n) if adj[i])
    changed = True
    while changed:
        changed = False
        for v in list(alive):
            if len(adj[v] & alive) < 2:
                alive.discard(v); changed = True
    return alive, adj


def analyse(P, tol):
    n = len(P)
    D = {(i, j): d2(P[i], P[j]) for i, j in itertools.combinations(range(n), 2)}
    vals = sorted(D.values(), reverse=True)
    Dmax = vals[0]
    d2nd = next(v for v in vals if Dmax - v > tol)
    E1 = [k for k, v in D.items() if fabs(v - d2nd) <= tol]
    ED = [k for k, v in D.items() if fabs(v - Dmax) <= tol]
    rest = [v for v in vals if v < d2nd - tol]
    gap = (d2nd - rest[0]) / d2nd if rest else mpf(1)
    H = set(hull_vertices(P))
    alive, adj = core(n, E1)
    degc = {v: len(adj[v] & alive) for v in alive}
    t = sum(1 for v in alive if v in H and degc[v] == 3)
    # concyclicity: normalised lifted determinant
    s = sqrt(d2nd)
    minc = None; argc = None
    for q in itertools.combinations(range(n), 4):
        a = P[q[3]]
        M = [[(P[i][0] - a[0]) / s, (P[i][1] - a[1]) / s, d2(P[i], a) / d2nd] for i in q[:3]]
        det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
               + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
        if minc is None or fabs(det) < minc:
            minc = fabs(det); argc = q
    mino = min(fabs(orient(P[a], P[b], P[c])) / d2nd for a, b, c in itertools.combinations(range(n), 3))
    maxerr = max([fabs(D[k] - d2nd) for k in E1] + [fabs(D[k] - Dmax) for k in ED])
    return dict(n=n, Delta=sqrt(Dmax / d2nd), mu2=len(E1), muD=len(ED), hull=sorted(H),
                degG={i: len(adj[i]) for i in range(n)}, core=sorted(alive), t=t,
                excess=len(E1) - n, gap=gap, min_concyclic=minc, argmin_concyclic=argc,
                min_orient=mino, max_eq_err=maxerr)


if __name__ == "__main__":
    digits = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    mp.dps = digits
    P = load(sys.argv[1])
    r = analyse(P, mpf(10) ** (-(digits // 2)))
    for k, v in r.items():
        if isinstance(v, type(mpf(1))):
            v = mp.nstr(v, 8)
        print(f"{k}: {v}")
