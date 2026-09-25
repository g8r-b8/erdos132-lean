"""Resonance lemma check (mpmath 40 digits; sanity for the analytic proof in B2_report.md, Lemma RES).

Unbroken consecutive rung pair (A,B) on one centre w: K-arc v_A -> v_B of j = k + l steps alpha_2,
D-arc z_A -> z_B of k steps alpha_1, signs sigma_A != sigma_B  =>  (k+l) a2 - k a1 = +-2 phi,
phi = atan(s/(R+tau)), s = sqrt(1-tau^2), t from tau via tau = t - (1-t^2)/(2R).
Claim: every solution with tau in [sqrt3/2 - 2 beta, 1] has R*dist(2s, Z) <= k + 3.
Also: Region II (tau >= sqrt3/2 + 3 beta) has 2 phi < alpha_1  (used for closed-arc disjointness),
and alpha_2 - alpha_1 <= 1.0001 t/(R Delta).
"""
from mpmath import mp, mpf, asin, atan, sqrt, findroot, nint

mp.dps = 40
beta = mpf(1) / 100
s3 = sqrt(3) / 2


def t_of_tau(tau, R):
    # tau = t - (1-t^2)/(2R)  <=>  t^2 + 2R t - (1 + 2R tau) = 0
    return -R + sqrt(R * R + 1 + 2 * R * tau)


def quantities(tau, R):
    t = t_of_tau(tau, R)
    Dl = R + t
    a2 = 2 * asin(1 / (2 * R))
    a1 = 2 * asin(1 / (2 * Dl))
    s = sqrt(1 - tau * tau)
    phi = atan(s / (R + tau))
    return t, Dl, a1, a2, s, phi


def check(R, K=60):
    worst = mpf(0)
    nsol = 0
    lo, hi = s3 - 2 * beta, mpf(1) - mpf(10) ** -30
    for k in range(0, K + 1):
        for l in (-1, 0, 1, 2):
            if k + l < 0:
                continue
            for sg in (1, -1):
                def g(tau):
                    t, Dl, a1, a2, s, phi = quantities(tau, R)
                    return (k + l) * a2 - k * a1 - sg * 2 * phi
                # scan for sign changes
                N = 400
                xs = [lo + (hi - lo) * i / N for i in range(N + 1)]
                vals = [g(x) for x in xs]
                for i in range(N):
                    if vals[i] == 0 or vals[i] * vals[i + 1] < 0:
                        a, b = xs[i], xs[i + 1]
                        for _ in range(120):
                            m = (a + b) / 2
                            if g(a) * g(m) <= 0:
                                b = m
                            else:
                                a = m
                        tau = (a + b) / 2
                        s = sqrt(1 - tau * tau)
                        dist = abs(2 * s - nint(2 * s))
                        ratio = R * dist / (k + 3)
                        worst = max(worst, ratio)
                        nsol += 1
                        assert R * dist <= k + 3, (k, l, sg, tau, R * dist)
    return nsol, worst


def region2_phi(R):
    worst = mpf(0)
    lo = s3 + 3 * beta
    for i in range(0, 2001):
        tau = lo + (1 - lo) * i / 2000
        t, Dl, a1, a2, s, phi = quantities(tau, R)
        assert 2 * phi < a1
        assert a2 - a1 <= mpf('1.0001') * t / (R * Dl)
        worst = max(worst, 2 * phi / a1)
    return worst


if __name__ == "__main__":
    for R in [mpf(10) ** 4, mpf(3) * 10 ** 4]:
        n, w = check(R, K=40)
        print('R=%s: %d resonant solutions found, max R*dist(2s,Z)/(k+3) = %s' % (mp.nstr(R, 3), n, mp.nstr(w, 6)))
        print('   Region II: max 2phi/alpha1 = %s (< 1)' % mp.nstr(region2_phi(R), 6))
    print('resonance checks pass')
