"""R6 referee: 60-digit Decimal one-centre examples of a FAN (template r4_nb_exact.py part 4) and a CAP.
One centre w = 0, R = 1e4; K = D(w,R) locally. K-row points on C(w,R) (partner w); D-points z on C(w,R+t)
(diametral partner w, so Lemma 3.2(a)/(b) hold by construction).  We treat every z as in S (worst case for v(y)).
Checks: min distance >= 1; v(y) = deg + m; Lemma Pin value of t; receivers' v; D-point degree <= 3;
Lemma 3.2(b) for every (K-row p, point q): q normal for p or |q - w| = Delta."""
from decimal import Decimal as D, getcontext
getcontext().prec = 60
R = D(10) ** 4
EPS = D(10) ** -40
r3 = D(3).sqrt() / 2


def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def mul(a, k): return (a[0] * k, a[1] * k)
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def nrm(a): return dot(a, a).sqrt()
def unit(a): return mul(a, 1 / nrm(a))


def circ(theta):
    """point of C(0,R) at angle theta (Decimal radians) measured from +z axis, via Taylor series."""
    x, s, c, k, term = theta, D(0), D(0), 0, D(1)
    # sin, cos by series
    s = D(0); c = D(0); t = D(1); n = 0
    while True:
        if n % 4 == 0: c += t
        elif n % 4 == 1: s += t
        elif n % 4 == 2: c -= t
        else: s -= t
        n += 1; t = t * x / n
        if abs(t) < D(10) ** -58: break
    return (R * s, R * c)


def build(kind, nblocks=4):
    """kind 'fan': chords of length 2, y = midpoint, z = y +- e/2 + (sqrt3/2)n, a = y +- e/2 - (sqrt3/2)n.
       kind 'cap': chords of length sqrt3, y = midpoint - n/2, z = y + n, lower = y + rot(+-120), b = y - n.
       Blocks on every other chord (the dense version does not close exactly: curvature makes two
       would-be-shared points 1 - O(1/R) apart)."""
    chord = D(2) if kind == 'fan' else 2 * r3
    half = 2 * (chord / (2 * R))  # angle of chord ~ 2 asin(c/2R); compute asin by series
    x = chord / (2 * R); a = x; term = x; k = 1
    while True:
        term = term * x * x * (2 * k - 1) ** 2 / ((2 * k) * (2 * k + 1)); a += term; k += 1
        if abs(term) < D(10) ** -58: break
    ang = 2 * a
    pts = {}; roles = {}
    for i in range(0, 2 * nblocks, 2):
        pm, pp = circ(ang * i), circ(ang * (i + 1))
        mid = mul(add(pm, pp), D(1) / 2); n = unit(mid); e = unit(sub(pp, pm))
        pts[('p', i)] = pm; pts[('p', i + 1)] = pp
        if kind == 'fan':
            y = mid
            pts[('y', i)] = y
            pts[('z', i, -1)] = add(add(y, mul(e, D(-1) / 2)), mul(n, r3))
            pts[('z', i, 1)] = add(add(y, mul(e, D(1) / 2)), mul(n, r3))
            pts[('a', i, -1)] = add(add(y, mul(e, D(-1) / 2)), mul(n, -r3))
            pts[('a', i, 1)] = add(add(y, mul(e, D(1) / 2)), mul(n, -r3))
        else:
            y = sub(mid, mul(n, D(1) / 2))
            pts[('y', i)] = y
            pts[('z', i)] = add(y, n)
            pts[('l', i, -1)] = add(add(y, mul(e, -r3)), mul(n, D(-1) / 2))
            pts[('l', i, 1)] = add(add(y, mul(e, r3)), mul(n, D(-1) / 2))
            pts[('b', i)] = sub(y, n)
    return pts


def analyse(kind):
    pts = build(kind)
    keys = list(pts)
    t = nrm(pts[[k for k in keys if k[0] == 'z'][0]]) - R
    Delta = R + t
    tau = t - (1 - t * t) / (2 * R)
    mind = min(nrm(sub(pts[a], pts[b])) for i, a in enumerate(keys) for b in keys[i + 1:])
    assert mind > 1 - EPS, mind
    for k in keys:
        r = nrm(pts[k])
        if k[0] == 'p': assert abs(r - R) < EPS
        elif k[0] == 'z': assert abs(r - Delta) < EPS
        else: assert r < R
    S = {k for k in keys if k[0] in 'pz'}
    nb = {k: [j for j in keys if j != k and abs(nrm(sub(pts[j], pts[k])) - 1) < EPS] for k in keys}
    # Lemma 3.2(b) for every K-row p (u_p = -p/R) and every q: normal or |q - w| = Delta
    for p in [k for k in keys if k[0] == 'p']:
        u = mul(pts[p], -1 / R)
        for q in keys:
            if q == p: continue
            d = sub(pts[q], pts[p])
            normal = dot(d, u) >= dot(d, d) / (2 * R) - EPS
            exc = abs(nrm(pts[q]) - Delta) < EPS
            assert normal or exc
    # D-point degree <= 3 and open half-plane (u_z = -z/|z|)
    for z in [k for k in keys if k[0] == 'z']:
        assert len(nb[z]) <= 3
        u = unit(mul(pts[z], -1))
        assert all(dot(sub(pts[q], pts[z]), u) > 0 for q in keys if q != z)
    print(f"--- {kind}: t = {t:.12f}, tau = {tau:.12f}, min dist - 1 = {mind - 1:.2e}")
    for k in keys:
        if k[0] in 'pz': continue
        m = sum(1 for j in nb[k] if j in S)
        print(f"   {str(k):14s} deg {len(nb[k])} m {m} v {len(nb[k]) + m}  (local config only)")
    return t, pts, nb, S


t_fan, P, NB, S = analyse('fan')
assert D('0.74') < t_fan < D('0.99')
y = P[('y', 0)]
for k in [('y', 0)]:
    assert len(NB[k]) == 6 and sum(1 for j in NB[k] if j in S) == 4
# receivers a: m_a <= 1
for k in P:
    if k[0] == 'a':
        assert sum(1 for j in NB[k] if j in S) <= 1
t_cap, P, NB, S = analyse('cap')
assert D('0.44') < t_cap < D('0.56')
assert len(NB[('y', 0)]) == 6 and sum(1 for j in NB[('y', 0)] if j in S) == 3
for k in P:
    if k[0] == 'b':
        assert sum(1 for j in NB[k] if j in S) == 0
print(f"fan: t = {float(t_fan):.6f} in Pin range [0.74,0.99]; y: deg 6 m 4 (v=10); receivers a: m_a <= 1")
print(f"cap: t = {float(t_cap):.6f} in Pin range [0.44,0.56]; y: deg 6 m 3 (v=9); receiver b: m_b = 0")
print("ALL ASSERTIONS PASSED")
