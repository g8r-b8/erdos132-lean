"""R6 / Theorem N3: exact-geometry (60-digit Decimal) examples of the heavy configurations.

(a) Fan chain (R4's chord-midpoint fan, blocks on every other chord of length 2 of C(w,R)): y has v = 10 when the
    z's count as S; its lower points a+- have exactly one S-neighbour (v <= 7) and distinct owners; t = 0.866...
(b) Cap chain: consecutive chords of length sqrt3 of C(w,R); z (outer) and y (inner) are the two points at distance 1
    from both chord ends, b = 2y - z, c+- at the exact hexagon slots +-120; caps on every other chord. Then y has deg 6, m 3 (v = 9), b has no S-neighbour,
    c's have at most one; t = |zw| - R = 0.5 + O(1/R) (pinned, Lemma Pin).
(c) Charging identity on both local models: sum over the R-points of v <= 8 * #R (so the average is <= 8).
S is taken to be the K-row points p (on C(w,R)) together with all z's (worst case for v).
"""
from decimal import Decimal as D, getcontext
getcontext().prec = 60
R = D(10)**4
EPS = D(10)**-40


def sub(a, b): return (a[0]-b[0], a[1]-b[1])
def add(a, b): return (a[0]+b[0], a[1]+b[1])
def mul(a, k): return (a[0]*k, a[1]*k)
def nrm(a): return (a[0]*a[0] + a[1]*a[1]).sqrt()
def rot(p, c, s): return (p[0]*c - p[1]*s, p[0]*s + p[1]*c)


def two_unit_points(p, q):
    """the two points at distance 1 from p and q: (outer, inner) w.r.t. the origin w"""
    m = mul(add(p, q), D(1)/2); d = sub(q, p); L = nrm(d)
    e = mul(d, 1/L); nperp = (-e[1], e[0]); hgt = (1 - L*L/4).sqrt()
    a, b = add(m, mul(nperp, hgt)), add(m, mul(nperp, -hgt))
    return (a, b) if nrm(a) > nrm(b) else (b, a)


def neighbours(pts, k):
    return [j for j in pts if j != k and abs(nrm(sub(pts[j], pts[k])) - 1) < EPS]


def check_min(pts):
    ks = list(pts)
    return min(nrm(sub(pts[a], pts[b])) for i, a in enumerate(ks) for b in ks[i+1:])


def chord_rot(L):  # rotation by the central angle of a chord of length L on C(0,R)
    sh = L / (2*R); ch = (1 - sh*sh).sqrt()
    return ch*ch - sh*sh, 2*sh*ch


# ---------------- (a) fan chain
pts = {}
c2, s2 = chord_rot(D(2)); c1, s1 = chord_rot(D(1))
P = [(R, D(0))]
for i in range(9):       # pattern: chord 2 (fan), chord 1 (plain T-edge), chord 2, ...
    cc, ss = (c2, s2) if i % 2 == 0 else (c1, s1)
    P.append(rot(P[-1], cc, ss))
for i, p in enumerate(P): pts[('p', i)] = p
r3 = D(3).sqrt()/2
for i in range(0, 9, 2):
    pm, pp = P[i], P[i+1]
    y = mul(add(pm, pp), D(1)/2); n = mul(y, 1/nrm(y)); e = mul(sub(pp, pm), D(1)/2)
    pts[('y', i)] = y
    pts[('z', i, 0)] = add(add(y, mul(e, D(-1)/2)), mul(n, r3)); pts[('z', i, 1)] = add(add(y, mul(e, D(1)/2)), mul(n, r3))
    pts[('a', i, 0)] = add(add(y, mul(e, D(-1)/2)), mul(n, -r3)); pts[('a', i, 1)] = add(add(y, mul(e, D(1)/2)), mul(n, -r3))
assert check_min(pts) > 1 - EPS
t_fan = nrm(pts[('z', 0, 0)]) - R
S = {k for k in pts if k[0] in 'pz'}
vals = {}
for k in pts:
    if k[0] in 'ya':
        nb = neighbours(pts, k); m = sum(1 for j in nb if j in S); vals[k] = (len(nb), m)
for k, (d, m) in vals.items():
    if k[0] == 'y': assert (d, m) == (6, 4)
    else: assert m == 1 and d + m <= 7
owners = {}
for k in vals:
    if k[0] == 'y':
        for j in neighbours(pts, k):
            if j[0] == 'a': owners.setdefault(j, []).append(k)
assert all(len(o) == 1 for o in owners.values())
Rset = [k for k in vals]
tot = sum(d + m for d, m in vals.values())
assert tot <= 8 * len(Rset)
print(f"(a) fan chain: t = {t_fan:.12f}; y: (deg,m) = (6,4); lower points: m = 1; owners unique; "
      f"sum v = {tot} <= 8*#R = {8*len(Rset)}")
# the exception identity for p and z (Lemma 3.2(c)): (z-p).u_p = -tau exactly when |zp| = 1
tau = t_fan - (1 - t_fan*t_fan)/(2*R)
p, z = pts[('p', 0)], pts[('z', 0, 0)]
up = mul(p, -1/nrm(p))
assert abs(nrm(sub(z, p)) - 1) < EPS and abs((z[0]-p[0])*up[0] + (z[1]-p[1])*up[1] + tau) < EPS
print(f"    Lemma 3.2(c) at p-z: (z-p).u_p = -tau = {-tau:.12f} (so the fan pins t near sqrt(3)/2)")

# ---------------- (b) cap chain
# Adjacent caps cannot share their lower points: on a circle of radius R the two hexagon positions differ by O(1/R)
# and come out at distance 0.99985 < 1 from the neighbouring b. So caps sit on every other chord (sqrt3, 1.01, sqrt3, ...; spacer 1.01 since the c's under a chord of length 1 would be 0.9997 apart).
pts = {}
cq, sq = chord_rot(D(3).sqrt()); c1, s1 = chord_rot(D("1.01"))
P = [(R, D(0))]
for i in range(15):
    cc, ss = (cq, sq) if i % 2 == 0 else (c1, s1)
    P.append(rot(P[-1], cc, ss))
for i, p in enumerate(P): pts[('p', i)] = p
for i in range(0, 15, 2):
    z, y = two_unit_points(P[i], P[i+1])
    pts[('z', i)] = z; pts[('y', i)] = y
    pts[('b', i)] = sub(mul(y, D(2)), z)                     # slot 180
    pts[('c', i, 0)] = add(y, sub(P[i], z))                  # slots +-120 (exact hexagon: v(-60) - v(0) = v(-120))
    pts[('c', i, 1)] = add(y, sub(P[i+1], z))
mind = check_min(pts)
assert mind > 1 - EPS
t_cap = nrm(pts[('z', 4)]) - R
S = {k for k in pts if k[0] in 'pz'}
vals = {}
for k in pts:
    if k[0] in 'ybc':
        nb = neighbours(pts, k); m = sum(1 for j in nb if j in S); vals[k] = (len(nb), m)
for i in range(0, 15, 2):
    assert vals[('y', i)] == (6, 3), vals[('y', i)]
    assert vals[('b', i)][1] == 0
for k, (d, m) in vals.items():
    if k[0] == 'c': assert m <= 1
# D-point degree <= 3 (all of X in an open half-plane at z): here z's neighbours are p-, p+, y
for i in range(0, 15, 2): assert len(neighbours(pts, ('z', i))) == 3
tot = sum(d + m for d, m in vals.values())
assert tot <= 8 * len(vals)
print(f"(b) cap chain: t = {t_cap:.12f} (pinned near 1/2); y: (6,3) v=9; b: m=0; c: m<=1; "
      f"sum v = {tot} <= 8*#R = {8*len(vals)} (per cap 9 + 6 + 7 + 7 = 29 <= 32)")
print("all example checks passed")
