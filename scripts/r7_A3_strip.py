"""R7 / A3 referee: EXACT verification of B2's single-centre hexagonal strip (resonance-window obstruction).

w = 0, v_j = R e(j a), z_j = Delta e((j+1/2) a), a = alpha_2 = 2 asin(1/(2R)).
Closed forms (proved here symbolically, p := sqrt(4R^2 - 1), relation p^2 = 4R^2 - 1):
   cos(a/2) = p/(2R), sin(a/2) = 1/(2R),
   Delta = (p + sqrt3)/2                         (from |z_0 v_0| = 1),
   tau   = (sqrt3 p - 1)/(4R) = cos(pi/6 + a/2)  (so tau - sqrt3/2 = -1/(4R) + O(R^-2)),
   s_tau = sin(theta_0) = Delta/(2R),  d := 2 s_tau - 1 = t/R  exactly  (R d = t < 1 < 5: inside the window),
   (z_0 - v_0).u_{v_0} = -tau  (rung = exception, Lemma 3.2c),
   |z_0 v_0| = |z_0 v_1| = |v_0 v_1| = 1,  |z_0 z_1| = Delta/R > 1.
All other pair distances in a window: rigorous interval arithmetic (mpmath.iv, 60 digits) on the exact
algebraic numbers.  Counts per period: 1 T-edge + 2 rungs vs 2 points of S (if the z's are in S): e - s = 1 per
K-point, and every interior v_j has Delta_2-degree 1 (its only partner is w): e(S) - s = |Q'| - O(1).
"""
import sympy as sp
from mpmath import iv, mp

R = sp.symbols('R', positive=True)
p = sp.symbols('p', positive=True)          # p = sqrt(4R^2-1)
r3 = sp.sqrt(3)


def red(expr):
    """reduce a polynomial expression in p modulo p^2 = 4R^2 - 1 (exact)."""
    e = sp.expand(expr)
    e = sp.Poly(e, p)
    q = sp.Poly(p ** 2 - (4 * R ** 2 - 1), p)
    return sp.simplify(e.rem(q).as_expr())


c2 = p / (2 * R)       # cos(a/2)
s2 = 1 / (2 * R)       # sin(a/2)
Dl = (p + r3) / 2
t = Dl - R
tau = t - (1 - t ** 2) / (2 * R)

# |z0 - v0|^2 = R^2 + Delta^2 - 2 R Delta cos(a/2)
assert red(R ** 2 + Dl ** 2 - 2 * R * Dl * c2 - 1) == 0
# tau closed form and = cos(pi/6 + a/2)
tau_cf = (r3 * p - 1) / (4 * R)
assert red(tau - tau_cf) == 0
assert red(tau_cf - (r3 / 2 * c2 - sp.Rational(1, 2) * s2)) == 0
# s_tau = Delta/(2R): (Delta/2R)^2 + tau^2 = 1
assert red((Dl / (2 * R)) ** 2 + tau_cf ** 2 - 1) == 0
# exception identity: u_{v0} = (-1, 0), z0 - v0 = (Delta c2 - R, Delta s2)
assert red(-(Dl * c2 - R) + tau_cf) == 0
# |v0 v1| = 2R sin(a/2) = 1 ; |z0 z1| = 2 Delta sin(a/2) = Delta/R
assert sp.simplify(2 * R * s2 - 1) == 0
print('symbolic identities OK: Delta=(p+sqrt3)/2, tau=(sqrt3 p-1)/(4R)=cos(pi/6+a/2), s=Delta/(2R), d=t/R, exception')

# --- rigorous numeric window checks for concrete R ---
iv.dps = 60
mp.dps = 60


def cpow(re, im, n):
    a, b = iv.mpf(1), iv.mpf(0)
    for _ in range(n):
        a, b = a * re - b * im, a * im + b * re
    return a, b


for Rv in [10 ** 4, 10 ** 5, 10 ** 6]:
    Ri = iv.mpf(Rv)
    pv = iv.sqrt(4 * Ri ** 2 - 1)
    D = (pv + iv.sqrt(3)) / 2
    wre, wim = pv / (2 * Ri), 1 / (2 * Ri)        # omega = e(a/2)
    N = 14
    pts = []
    for j in range(N):
        x, y = cpow(wre, wim, 2 * j)
        pts.append(('v', j, Ri * x, Ri * y))
    for j in range(N - 1):
        x, y = cpow(wre, wim, 2 * j + 1)
        pts.append(('z', j, D * x, D * y))
    pts.append(('w', 0, iv.mpf(0), iv.mpf(0)))
    unit, atR, atD = set(), set(), set()
    Dv = D
    for i in range(len(pts)):
        for k in range(i + 1, len(pts)):
            P, Q = pts[i], pts[k]
            d2 = (P[2] - Q[2]) ** 2 + (P[3] - Q[3]) ** 2
            key = (P[:2], Q[:2])
            if 1 in d2:                  # interval contains 1: must be an exactly-unit pair (proved symbolically)
                unit.add(key)
            else:
                assert d2.a > 1, key     # rigorous: > 1
            if Ri ** 2 in d2 or (d2.a < Ri ** 2 < d2.b):
                atR.add(key)
            if (Dv ** 2).a <= d2.b and d2.a <= (Dv ** 2).b:
                atD.add(key)
            # no distance strictly between R and Delta (up to enclosure width)
            if d2.a > Ri ** 2 and d2.b < (Dv ** 2).a:
                raise AssertionError(('distance in (R, Delta)', key))
    exp_unit = set()
    for j in range(N - 1):
        exp_unit |= {(('v', j), ('v', j + 1)), (('v', j), ('z', j)), (('v', j + 1), ('z', j))}
    assert unit == exp_unit, unit ^ exp_unit
    assert atR == {(('v', j), ('w', 0)) for j in range(N)}
    assert atD == {(('z', j), ('w', 0)) for j in range(N - 1)}
    tv = D - Ri
    tauv = (iv.sqrt(3) * pv - 1) / (4 * Ri)
    s3 = iv.sqrt(3) / 2
    assert (s3 - iv.mpf('0.02')).b < tauv.a and tauv.b < (s3 + iv.mpf('0.03')).a   # Region III
    Rd = tv                                                                       # R d = t exactly
    assert Rd.b < 1
    # rung goodness angle a/2 < beta; T-edge elevation a = 1/(2R) in (0, beta)
    assert (1 / (2 * Ri)).b < 0.01
    zz = D / Ri
    assert zz.a > 1
    # counts per window: T-edges N-1, rungs 2(N-1); s = N + (N-1) (z's assumed in S via far partners); Q' = V
    e = (N - 1) + 2 * (N - 1)
    s = N + (N - 1)
    print('R=%d: unit pairs exactly T-edges+rungs; only w-v at distance R, only w-z at Delta; '
          'tau - sqrt3/2 = %s (x R = %s); R d = t = %s; |z z+1| - 1 = %s; window e - s = %d, |Q\'| = %d'
          % (Rv, mp.nstr((tauv - s3).mid, 8), mp.nstr(((tauv - s3) * Ri).mid, 10), mp.nstr(Rd.mid, 10),
             mp.nstr((zz - 1).mid, 6), e - s, N))
print('strip: all exact/rigorous checks pass')
