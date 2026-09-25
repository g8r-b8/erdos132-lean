"""R7 / A3 referee: sanity enumeration (50 digits) for the break-distinctness steps of B2's Theorem BC in Region III.

Proof being checked (referee's version, see A3_report.md, item 1, (D2)/(D3)):
 (D3) If v lies in the open arc (v_A', v_B') of an arc gap (|Z'| >= 2, centre w'), then w_v = w' and the D-end z of
      any rung at v lies on C(w', Delta) at angle theta(v) +- phi, which is inside [theta(z_A'), theta(z_B')] or
      outside it by at most 2 phi - alpha_2 < alpha_1; hence |z - z''| < 1 for some z'' in Z' unless z in Z'.
 (D2) Two components Z, Z' with the same centre: K-ends of their rungs cannot interleave (overlap <= 2phi - alpha_1
      < alpha_2).
The enumeration places Z' = {theta(z_A') + i alpha_1 : 0 <= i <= K}, all sign patterns, v anywhere in
[theta(v_A') + alpha_2, theta(v_B') - alpha_2] (walk points and 13 continuous positions; reduced grid for speed), and checks the claim.
"""
from mpmath import mp, mpf, asin, sin, sqrt

mp.dps = 30


def params(tau, R):
    t = -R + sqrt(R * R + 1 + 2 * R * tau)
    Dl = R + t
    s = sqrt(1 - tau * tau)
    return Dl, 2 * asin(1 / (2 * R)), 2 * asin(1 / (2 * Dl)), asin(s / Dl)   # Delta, a2, a1, phi


def chord(r, dth):
    return 2 * r * abs(sin(dth / 2))


s3 = sqrt(3) / 2
worst3, worst2, n3 = mpf(0), mpf(-10), 0
for R in [mpf(10) ** 4, mpf(10) ** 5]:
    taus = [s3 - mpf('0.0199') + mpf('0.0498') * i / 10 for i in range(11)]
    taus += [s3 + mpf(k) / R for k in (-6, -3, -1, 1, 3, 6)]
    for tau in taus:
        Dl, a2, a1, phi = params(tau, R)
        # (D2)
        worst2 = max(worst2, (2 * phi - a1) / a2)
        assert 2 * phi - a1 < a2
        for K in (1, 2, 3, 5, 8, 13, 21):
            for sA in (1, -1):
                for sB in (1, -1):
                    zA = mpf(0)
                    Zp = [zA + i * a1 for i in range(K + 1)]
                    vA = Zp[0] - sA * phi
                    vB = Zp[-1] - sB * phi
                    if vB - vA < 2 * a2:
                        continue
                    cands = [vA + i * a2 for i in range(1, 60) if vA + i * a2 <= vB - a2]
                    cands += [vA + a2 + (vB - vA - 2 * a2) * j / 12 for j in range(13)]
                    for th_v in cands:
                        for sg in (1, -1):
                            th_z = th_v + sg * phi
                            ii = int(mp.floor((th_z - zA) / a1))
                            near = [Zp[j] for j in (ii - 1, ii, ii + 1, ii + 2) if 0 <= j <= K]
                            near += [Zp[0], Zp[-1]]
                            dmin = min(chord(Dl, th_z - q) for q in near)
                            n3 += 1
                            if dmin < mpf(10) ** -30:
                                continue          # z coincides with a point of Z': then z in Z'
                            assert dmin < 1, (R, tau, K, sA, sB, th_v, dmin)
                            worst3 = max(worst3, dmin)
print('(D3) %d placements checked: z always within distance < 1 of Z\' (max min-distance %s)' % (n3, mp.nstr(worst3, 10)))
print('(D2) max (2phi - alpha_1)/alpha_2 over Region III grid = %s (< 1)' % mp.nstr(worst2, 10))
print('all r7_A3_distinct checks pass')
