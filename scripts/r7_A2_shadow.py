"""R7-A2: checks for the strengthening 'Theorem II-sharp' (Region II: U = O(1) unless alpha2 - alpha1 = 2 phi).

Shadow lemma (analytic): if v in C(w,R), z in C(w,Delta) with angular offset |o| < phi, then
|z - v|^2 = R^2 + Delta^2 - 2 R Delta cos o < R^2 + Delta^2 - 2 R Delta cos phi = 1 (rung length).
Rational bounds used (R >= 1e4, t <= 1, eps := alpha2 - alpha1):
  alpha2 >= 1/R,  alpha2 <= 1/R + 1/(23 R^3),  alpha1 >= 1/(R+1)  =>  eps <= 1/R^2;
  2 phi <= 0.8881 alpha1 < 0.8881 alpha2   (r7_A2_constants.py §2).
(i)  l >= 1 impossible: l alpha2 + k eps >= alpha2 > 2 phi.
(ii) l <= -2 impossible: k eps >= 2 alpha2 - 2phi >= 1.1119/R => k >= 1.1119 R, but k alpha1 <= pi/3 => k <= 1.0472 (R+1).
(iii) l = -1: k >= 0.1119 R, arc angle j alpha2 >= (0.1119 R - 1)/R >= 0.1118 => at most floor(2 pi/0.1118) = 56 gaps.
(iv) numerics: tau*(R) (root of alpha2 - alpha1 = 2 phi) for R = 1e4, 1e5, 1e6; R^2 (1 - tau*) -> 1/8.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, atan, sqrt

PI_HI = F(355, 113) + F(1, 10**6)
Rm = F(10**4)
c = F(8881, 10000)
# (ii)
assert (2 - c) * 1 > F(10472, 10000) * (1 + 1 / Rm) * 1  # 1.1119 R > 1.0472 (R+1)
# (iii)
ang = (F(1119, 10000) * Rm - 1) / Rm
assert ang >= F(1118, 10000)
n = 2 * PI_HI / F(1118, 10000)
assert 56 < n < 57
print('(i)-(iii) rational: l>=1 and l<=-2 impossible; l=-1 opposite-sign unbroken gaps <= 56: OK')

mp.dps = 60
def tau_star(R):
    def g(tau):
        t = -R + sqrt(R * R + 1 + 2 * R * tau)
        a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * (R + t)))
        return a2 - a1 - 2 * atan(sqrt(1 - tau * tau) / (R + tau))
    lo, hi = 1 - mpf(1) / R, 1 - mpf(10) ** -40
    assert g(lo) < 0 < g(hi)
    for _ in range(250):
        m = (lo + hi) / 2
        if g(m) < 0: lo = m
        else: hi = m
    return lo
for R in [mpf(10) ** 4, mpf(10) ** 5, mpf(10) ** 6]:
    ts = tau_star(R)
    print('R=%s: 1 - tau* = %s, R^2 (1 - tau*) = %s' % (mp.nstr(R, 3), mp.nstr(1 - ts, 12), mp.nstr(R * R * (1 - ts), 15)))
print('shadow checks pass')
