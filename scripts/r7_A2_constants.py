"""R7-A2 referee: exact / rigorous checks of the constants used by B2's Region II argument.

1. L0 identity (sympy): (R+tau)^2 + (1-tau^2) = (R+t)^2 with tau = t - (1-t^2)/(2R).
2. 2*phi < alpha_1 on all of Region II, all R >= 1e4, by a rational certificate:
   phi <= tan phi = s/(R+tau),  alpha_1 >= 1/Delta,  t - tau = (1-t^2)/(2R) in [0, 1/(2R)]  (t <= 1)
   => 2phi/alpha_1 <= 2 s (1 + 1/(2R^2)),  s^2 <= 1 - tau_min^2,  tau_min = sqrt3/2 + 3/100.
   4 s^2 <= 1 - 0.12 sqrt3 - 0.0036 < 1 - 0.12*1.732 - 0.0036  (sqrt3 > 1.732).
3. CONS(a): same-sign unbroken gap => arc angle >= 1/(t + 1/(23R)) >= 1/(1 + 1/(23e4));
   disjoint arcs on dK, per(K) <= 2 pi R => count <= floor(2 pi (1 + 1/230000)) = 6  (B2 says 7: fine).
   Also: same-sign gaps are impossible when 1/(t + 1/(23R)) > pi/3, i.e. t < 3/pi - 1/(23R) ~ 0.95493.
4. CONS(b): rungs B shared by two unbroken gaps: <= 2*6 (a gap in the pair is same-sign) + 12 (sigma_A = sigma_C:
   arcs [v_A,v_C) of angle >= ~1, each boundary point in <= 2 of them) = 24.
5. LP certificate for theta = kappa = 1/2 (Fractions).
Uses pi upper bound 355/113 + 1e-6 > pi (rational).  All asserts must pass.
"""
from fractions import Fraction as F
import sympy as sp

# 1
t, R = sp.symbols('t R', positive=True)
tau = t - (1 - t**2) / (2 * R)
assert sp.simplify((R + tau)**2 + (1 - tau**2) - (R + t)**2) == 0
print('1. L0 identity |z-w|^2 = Delta^2: OK (sympy)')

# 2
sqrt3_lo = F(1732, 1000)
assert sqrt3_lo**2 < 3
four_s2_hi = 1 - F(12, 100) * sqrt3_lo - F(36, 10000)
Rmin = F(10**4)
ratio_sq_hi = four_s2_hi * (1 + 1 / (2 * Rmin**2))**2
assert ratio_sq_hi < 1
# 0.8881^2
assert ratio_sq_hi < F(8881, 10000)**2
print('2. Region II: (2phi/alpha1)^2 <= %s < 0.8881^2 < 1: OK' % float(ratio_sq_hi))
# also check the monotonicity premise: t <= 1 in Region II with rungs (tau <= 1 <=> t <= 1), t>=tau:
tt = sp.symbols('tt')
# tau(t) increasing in t for t>0: d tau/dt = 1 + t/R > 0
assert sp.simplify(sp.diff(tau, t) - (1 + t / R)) == 0

# 3
PI_HI = F(355, 113) + F(1, 10**6)
PI_LO = F(355, 113) - F(1, 10**6)
ang_lo = 1 / (1 + 1 / (23 * Rmin))
cnt = PI_HI * 2 / ang_lo
assert 6 < cnt < 7
print('3. CONS(a): same-sign unbroken gaps <= floor(%.6f) = 6 (B2: 7, conservative): OK' % float(cnt))
# threshold: same-sign impossible if 1/(t+1/(23R)) > pi/3  <=>  t < 3/pi - 1/(23R)
thr = 3 / PI_HI - 1 / (23 * Rmin)
print('   same-sign unbroken gaps impossible for t < %.6f (rational lower bound)' % float(thr))
assert F(954, 1000) < thr

# 4
cnt2 = 2 * PI_HI * 2 / ang_lo
assert 12 < cnt2 < 13
print('4. CONS(b): triples with sigma_A = sigma_C <= 12; shared rungs <= 2*6 + 12 = 24: OK')

# 5 LP
def lp_value(c):
    lam = max(F(1, 2), (c - 1) / (c + F(1, 2)))
    qc = -F(1, 2) * lam + F(1, 2) * (1 - lam)
    sc = F(3, 2) * lam + (1 - lam)
    rc = (1 - lam) * c
    assert qc <= 0
    return max(sc, rc)
for c, want in [(F(4), F(4, 3)), (F(7, 2), F(21, 16)), (F(3), F(9, 7)), (F(5, 2), F(5, 4)), (F(2), F(5, 4))]:
    v = lp_value(c)
    assert v == want, (c, v, want)
    if c >= F(5, 2):
        assert v == 3 * c / (2 * c + 1)
print('5. LP (theta=kappa=1/2): value max{5/4, 3c/(2c+1)}: c=4->4/3, 7/2->21/16, 3->9/7: OK')
print('ALL CONSTANT CHECKS PASS')
