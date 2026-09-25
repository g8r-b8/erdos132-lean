"""REF_C (R7): Shadow obstruction for inward (l = +1) arc gaps with k >= 1.
Exact argument: rung (v_A, z_A) has theta(z_A) = theta(v_A) + phi (L0), |v_A z_A| = 1.  For v on C(w,R), z on C(w,Delta),
|z - v|^2 = R^2 + Delta^2 - 2 R Delta cos(o) is strictly increasing in |o| on [0, pi] and equals 1 at o = phi.
l = +1, k >= 1  =>  j = k + 1 >= 2, so the walk point v_1 = R e(theta_A + alpha2) is in X, and
2 phi = alpha2 + k (alpha2 - alpha1) > alpha2  =>  |o(v_1, z_A)| = |alpha2 - phi| < phi  =>  |v_1 z_A| < 1.  Contradiction.
Numerical illustration at the exact resonances (80 digits)."""
from mpmath import mp, mpf, sqrt, asin, cos, findroot
mp.dps = 80
def params(R, tau):
    t = -R + sqrt(R * R + 1 + 2 * R * tau); D = R + t; s = sqrt(1 - tau * tau)
    return t, D, s, 2 * asin(1 / (2 * R)), 2 * asin(1 / (2 * D)), asin(s / D)
for R in [mpf(10) ** 4, mpf(10) ** 6, mpf(10) ** 9]:
    for k in [1, 2, 3]:
        f = lambda tau: (lambda p: 2 * p[5] - (p[3] + k * (p[3] - p[4])))(params(R, tau))
        tau = mp.re(findroot(f, sqrt(3) / 2, tol=mpf(10) ** -70))
        t, D, s, a2, a1, phi = params(R, tau)
        dA = sqrt(R * R + D * D - 2 * R * D * cos(phi))          # rung, = 1
        d1 = sqrt(R * R + D * D - 2 * R * D * cos(a2 - phi))     # v_1 to z_A
        assert abs(dA - 1) < mpf(10) ** -50 and d1 < 1
        print('R=%.0e k=%d: |v_A z_A| = %s, |v_1 z_A| = 1 - %s' % (float(R), k, mp.nstr(dA, 20), mp.nstr(1 - d1, 6)))
print('r7_refC_shadow: PASS (no l=+1, k>=1 arc gap is metrically possible)')
