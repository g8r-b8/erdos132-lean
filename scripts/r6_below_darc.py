"""Adversarial check of Lemma DP (D-arc partner lemma), B2_report.md.

w = 0, z_1 = Delta e(-a), z_i = Delta e(0), z_N = Delta e(b), Delta = R + t.
If y satisfies |y - z_i| = R, |y - z_1| <= Delta, |y - z_N| <= Delta, |y| <= Delta, then
   |B| <= t*/sin m,  t* = (2Rt + t^2)/(2 Delta) < t,   m = min(a, b),
   |y| <= t/sin m + 2t + t^2/(Delta sin^2 m).
Sampling (mpmath, 30 digits) over random R, t, a, b and y on C(z_i, R), biased towards the feasible arc.
Also checks the counting consequence N < 10 Delta^(2/3) numerically for the extremal inequality.
"""
import random
from mpmath import mp, mpf, cos, sin, sqrt, pi

mp.dps = 30
random.seed(132)


def trial():
    R = mpf(10) ** random.uniform(4, 7)
    t = mpf(random.uniform(0.05, 1.0))
    Dl = R + t
    a = mpf(10) ** random.uniform(-6, 0) * pi / 3
    b = mpf(10) ** random.uniform(-6, 0) * pi / 3
    z1 = (Dl * cos(-a), Dl * sin(-a))
    zN = (Dl * cos(b), Dl * sin(b))
    zi = (Dl, mpf(0))
    m = min(a, b)
    bound = t / sin(m) + 2 * t + t * t / (Dl * sin(m) ** 2)
    tstar = (2 * R * t + t * t) / (2 * Dl)
    hits = 0
    for _ in range(200):
        # angle of y around z_i, measured from the direction towards w (= pi)
        om = pi + mpf(random.choice([-1, 1])) * mpf(10) ** random.uniform(-9, 0) * pi
        y = (zi[0] + R * cos(om), zi[1] + R * sin(om))
        d1 = sqrt((y[0] - z1[0]) ** 2 + (y[1] - z1[1]) ** 2)
        dN = sqrt((y[0] - zN[0]) ** 2 + (y[1] - zN[1]) ** 2)
        rho = sqrt(y[0] ** 2 + y[1] ** 2)
        if d1 <= Dl and dN <= Dl and rho <= Dl:
            hits += 1
            assert abs(y[1]) <= tstar / sin(m) * (1 + mpf(10) ** -20), (R, t, a, b, om)
            assert rho <= bound, (R, t, a, b, om, rho, bound)
    return hits


if __name__ == "__main__":
    tot = 0
    for k in range(400):
        tot += trial()
    print('feasible partner samples tested:', tot, '-- all satisfy Lemma DP bounds')
    # counting consequence: N/2 - 2 <= 2 (2 rho + 1)^2 with rho <= 5 Delta/N + 3 fails for N >= 10 Delta^(2/3)
    for e in range(4, 13):
        Dl = mpf(10) ** e
        N = 10 * Dl ** (mpf(2) / 3)
        lhs = N / 2 - 2
        rhs = 2 * (2 * (5 * Dl / N + 3) + 1) ** 2
        assert lhs > rhs, e
    print('counting inequality N < 10 Delta^(2/3) verified for Delta = 1e4..1e12 (monotone beyond)')
