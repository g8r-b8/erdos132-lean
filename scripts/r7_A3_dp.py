"""R7 / A3 referee: Lemma DP and Corollary DP (B2 report, section 'Lemma DP').

Lemma DP. w = 0, z_1 = Delta e(-a), z_i = Delta e(0), z_N = Delta e(b), a, b in (0, pi), m = min(a, b).
If |y - z_i| = R, |y - z_1| <= Delta, |y - z_N| <= Delta, |y| <= Delta, then (y = A e_0 + B e_0^perp,
c0 = Delta^2 - R^2 = 2Rt + t^2):
   A = (rho^2 + c0)/(2 Delta) >= c0/(2 Delta) > 0,
   B >= -(c0/(2 Delta)) cot b,   B <= (c0/(2 Delta)) cot a        [referee's sharpened step 2]
   => |B| <= (c0/(2 Delta)) cot m <= t / sin m   (cot decreasing on (0, pi); B >= 0 automatically if b >= pi/2),
   A = Delta - sqrt(Delta^2 - c0 - B^2) <= (c0 + B^2)/Delta,  rho <= A + |B| <= t/sin m + 2t + t^2/(Delta sin^2 m).
B2's step 2 used only A >= 0 and got B >= -c0/(2 Delta sin b), which is <= t/sin m only if sin b >= sin m
(true when a + b <= pi/3, which always holds for points of X on C(w, Delta)).

Test: EXTREMAL (not random) partners: the feasible set of y on C(z_i, R) is an arc in the angle omega at z_i,
|y| increases with |omega|, so max |y| and extreme B are attained at arc endpoints, which we compute by
bisection in 50-digit arithmetic, for random and adversarial (a, b, R, t), including b > pi/2.
Corollary DP counting inequality: exact (Fractions) proof that 3x^2 - 28x - 100 > 0 for x >= 13.
"""
import random
from fractions import Fraction as F
from mpmath import mp, mpf, cos, sin, sqrt, pi, cot

mp.dps = 50
random.seed(7132)


def feasible(om, R, Dl, z1, zN):
    y = (Dl - R * cos(om), -R * sin(om))      # y = z_i + R e(pi + om)
    ok = ((y[0] - z1[0]) ** 2 + (y[1] - z1[1]) ** 2 <= Dl ** 2 and
          (y[0] - zN[0]) ** 2 + (y[1] - zN[1]) ** 2 <= Dl ** 2 and
          y[0] ** 2 + y[1] ** 2 <= Dl ** 2)
    return ok, y


def extremes(R, t, a, b):
    Dl = R + t
    z1 = (Dl * cos(-a), Dl * sin(-a))
    zN = (Dl * cos(b), Dl * sin(b))
    ok0, _ = feasible(mpf(0), R, Dl, z1, zN)
    if not ok0:
        return None
    out = []
    for sgn in (1, -1):
        lo, hi = mpf(0), mpf(pi) / 2         # omega beyond pi/2 gives |y| > Delta (infeasible)
        assert not feasible(sgn * hi, R, Dl, z1, zN)[0]
        for _ in range(170):
            mid = (lo + hi) / 2
            if feasible(sgn * mid, R, Dl, z1, zN)[0]:
                lo = mid
            else:
                hi = mid
        out.append(feasible(sgn * lo, R, Dl, z1, zN)[1])
    return out


worst_rho, worst_B, n = mpf(0), mpf(0), 0
cases = []
for _ in range(3000):
    R = mpf(10) ** random.uniform(4, 9)
    t = mpf(random.uniform(0.01, 1.0))
    mode = random.random()
    if mode < 0.5:        # physical: a + b <= pi/3
        a = mpf(pi) / 3 * mpf(10) ** random.uniform(-7, 0)
        b = (mpf(pi) / 3 - a) * mpf(random.uniform(0.001, 1))
    else:                 # literal statement: a, b anywhere in (0, pi)
        a = mpf(pi) * mpf(random.uniform(1e-6, 0.999999))
        b = mpf(pi) * mpf(random.uniform(1e-6, 0.999999))
    if a <= 0 or b <= 0:
        continue
    cases.append((R, t, a, b))
# adversarial hand-picked: tiny angles near 1/Delta, the equal-angle case, b near pi
for R in [mpf(10) ** 4, mpf(10) ** 7]:
    for t in [mpf('0.05'), mpf('0.866'), mpf(1)]:
        Dl = R + t
        for (a, b) in [(1 / Dl, 1 / Dl), (5 / Dl, mpf(pi) / 3 - 5 / Dl), (mpf(pi) / 6, mpf(pi) / 6),
                       (mpf('0.3'), mpf(pi) - mpf('1e-3')), (mpf(pi) - mpf('1e-3'), mpf('0.3'))]:
            cases.append((R, t, a, b))

for (R, t, a, b) in cases:
    ex = extremes(R, t, a, b)
    if ex is None:
        continue
    Dl = R + t
    m = min(a, b)
    c0 = 2 * R * t + t * t
    boundB = c0 / (2 * Dl) * max(cot(m), mpf(0)) if m < pi / 2 else mpf(0)
    boundB_B2 = t / sin(m)
    bound = t / sin(m) + 2 * t + t * t / (Dl * sin(m) ** 2)
    for y in ex:
        rho = sqrt(y[0] ** 2 + y[1] ** 2)
        B = y[1]
        # sharpened B-bound (tolerance for the 170-step bisection)
        assert abs(B) <= boundB * (1 + mpf(10) ** -30) + mpf(10) ** -40, (R, t, a, b, B, boundB)
        assert abs(B) <= boundB_B2 * (1 + mpf(10) ** -30)
        assert rho <= bound * (1 + mpf(10) ** -30), (R, t, a, b, rho, bound)
        worst_rho = max(worst_rho, rho / bound)
        if boundB > 0:
            worst_B = max(worst_B, abs(B) / boundB)
        n += 1
print('Lemma DP: %d extremal partners (arc endpoints) tested, incl. a,b anywhere in (0,pi); all satisfy '
      '|B| <= (c0/2Delta) cot m and rho <= t/sin m + 2t + t^2/(Delta sin^2 m)' % n)
print('   worst |B| / ((c0/2Delta) cot m) = %s   (sharp: ~1 at the extremal endpoint)' % mp.nstr(worst_B, 8))
print('   worst rho / bound = %s' % mp.nstr(worst_rho, 8))

# ---- Corollary DP counting, exact ----
# N >= 10 Delta^(2/3), x := Delta^(1/3) >= 10^(4/3) > 21.5:  LHS = N/2 - 2 >= 5x^2 - 2,
# RHS = 2 (10 Delta/N + 7)^2 <= 2 (x + 7)^2.  LHS > RHS  <=  3x^2 - 28x - 100 > 0.
def h(x):
    return 3 * x * x - 28 * x - 100


assert h(F(12)) < 0 < h(F(13))  # root ~12.09; h increasing beyond 14/3
# h is increasing for x > 14/3, so h(x) > 0 for all x >= 13, in particular x >= 21.5 (Delta >= 1e4)
assert F(21, 1) ** 3 < 10 ** 4          # so x = Delta^(1/3) > 21 for Delta >= 1e4
# side conditions used: sin m >= (3 sqrt3/(2 pi)) m for m <= pi/3 (concavity), 3sqrt3/(2pi) > 0.8269,
# so sin m >= 0.8269 N/(4 Delta) >= 0.2 N/Delta ; t^2/(Delta sin^2 m) <= 25 Delta/N^2 <= 0.25 Delta^(-1/3) < 1
assert (3 * mpf(3) ** 0.5 / (2 * pi)) > mpf('0.8269') and mpf('0.8269') / 4 > mpf('0.2')
print('Corollary DP counting: 3x^2 - 28x - 100 > 0 for x >= 13 (exact) => N < 10 Delta^(2/3) for all Delta >= 1e4')
print('all r7_A3_dp checks pass')
