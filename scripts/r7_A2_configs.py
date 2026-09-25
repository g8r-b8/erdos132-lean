"""R7-A2 referee: adversarial exact (60-digit mpmath) single-centre configurations in Region II.

Model: w = 0, R = Delta_2 = 1e4, K-row points on C(0,R), D-row points on C(0,Delta), Delta = R + t,
tau = t - (1-t^2)/(2R) solved (bisection to 1e-55) so that the (★) resonance of Lemma CONS holds exactly.
For each configuration we compute ALL unit pairs among nearby points (angular window 4/R, which contains every pair
at distance <= 1.5 by the chord bound), the minimum distance, and classify unit pairs:
  KK / DD (T-edge test: a,b in (0,beta) with u_v = -v/R, u_z = -z/Delta), KD rung test (z-v).u_v = -tau exactly.
Config A: tau ~ 1 - 1/(8R^2), l = 0, k = j = 1, alternating sigma = +,-  (near-radial strip, Theta(R) unbroken gaps).
          Check: e - s = U - 1 on the window and |Q'| = 2U  => Theorem II is locally SHARP (theta = 1/2).
Config B: tau near sqrt3/2 + 3beta, l = -1 (j = k-1), k = 1300, sigma_A = -1, sigma_B = +1: one long opposite-sign
          unbroken gap. Check it is realisable (min dist >= 1) and the closed arc carries j+1 Q'-candidates.
Config C: same-sign unbroken gap at t ~ 0.99 (j alpha2 = (j+1) alpha1, j = 10100): expected NOT realisable
          (a D-point passes radially over a K-point at distance ~ t < 1) -> CONS(a) is vacuous for t < 1 - O(1/R^2).
Config A2: config A with k = 2 (j = k = 2): expected NOT realisable (intermediate D-point in a rung's shadow).
"""
from mpmath import mp, mpf, asin, atan, sqrt, cos, sin, pi

mp.dps = 60
beta = mpf(1) / 100
R = mpf(10) ** 4
TOL = mpf(10) ** -40


def t_of_tau(tau):
    return -R + sqrt(R * R + 1 + 2 * R * tau)


def q(tau):
    t = t_of_tau(tau)
    Dl = R + t
    a2 = 2 * asin(1 / (2 * R))
    a1 = 2 * asin(1 / (2 * Dl))
    s = sqrt(1 - tau * tau)
    phi = atan(s / (R + tau))
    return dict(t=t, Dl=Dl, a1=a1, a2=a2, s=s, phi=phi, tau=tau)


def bisect(g, lo, hi, it=220):
    glo = g(lo)
    ghi = g(hi)
    assert glo * ghi < 0, (glo, ghi)
    for _ in range(it):
        m = (lo + hi) / 2
        gm = g(m)
        if gm * glo <= 0:
            hi = m
        else:
            lo, glo = m, gm
    return (lo + hi) / 2


def analyse(name, Q, Kang, Dang, rungs_expected):
    Dl = Q['Dl']
    pts = [('K', i, a, R) for i, a in enumerate(Kang)] + [('D', i, a, Dl) for i, a in enumerate(Dang)]
    pts.sort(key=lambda p: p[2])
    xy = [(p[3] * cos(p[2]), p[3] * sin(p[2])) for p in pts]
    win = 4 / R
    mind = mpf(10)
    minpair = None
    unit = []
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            if pts[j][2] - pts[i][2] > win:
                break
            dd = sqrt((xy[i][0] - xy[j][0]) ** 2 + (xy[i][1] - xy[j][1]) ** 2)
            if dd < mind:
                mind, minpair = dd, (pts[i][:2], pts[j][:2])
            if abs(dd - 1) < TOL:
                unit.append((i, j))
    nKK = nDD = nR = nKDT = 0
    rungs = set()
    for i, j in unit:
        a, b = pts[i], pts[j]
        if a[0] == b[0]:
            # T-edge test with u = -p/|p|
            ua = (-xy[i][0] / a[3], -xy[i][1] / a[3]); ub = (-xy[j][0] / b[3], -xy[j][1] / b[3])
            e = (xy[j][0] - xy[i][0], xy[j][1] - xy[i][1])
            A = e[0] * ua[0] + e[1] * ua[1]; B = -(e[0] * ub[0] + e[1] * ub[1])
            assert 0 < A < beta and 0 < B < beta, (name, a[:2], b[:2])
            if a[0] == 'K':
                nKK += 1
            else:
                nDD += 1
        else:
            if a[0] == 'D':
                i, j, a, b = j, i, b, a
            v, z = xy[i], xy[j]
            u = (-v[0] / R, -v[1] / R)
            dot = (z[0] - v[0]) * u[0] + (z[1] - v[1]) * u[1]
            if abs(dot + Q['tau']) < TOL:
                nR += 1
                rungs.add((a[1], b[1]))
            else:
                nKDT += 1
    return dict(mind=mind, minpair=minpair, nKK=nKK, nDD=nDD, nR=nR, nKDT=nKDT, rungs=rungs,
                ok_rungs=(rungs == set(rungs_expected)))


def config_A(k=1, M=8):
    # (★) with sigma_A=+1, sigma_B=-1, j=k:  k(a2 - a1) = 2 phi
    g = lambda tau: (lambda Q: k * (Q['a2'] - Q['a1']) - 2 * Q['phi'])(q(tau))
    tau = bisect(g, 1 - mpf(10) ** -4, 1 - mpf(10) ** -30)
    Q = q(tau)
    Kang, Dang, rex = [], [], []
    per = 2 * k  # K-points per pair block: v_A .. v_B is k steps; next block starts 1 step later
    for m in range(M):
        base = m * (k + 1) * Q['a2']
        ks = [base + i * Q['a2'] for i in range(k + 1)]
        iA = len(Kang); Kang += ks
        dA = len(Dang)
        Dang += [base + Q['phi'] + i * Q['a1'] for i in range(k + 1)]
        rex += [(iA, dA), (iA + k, dA + k)]
    return Q, analyse('A(k=%d)' % k, Q, Kang, Dang, rex), M, len(Kang), len(Dang)


def config_B(k=1300):
    # sigma_A=-1, sigma_B=+1: j a2 = k a1 - 2 phi with j = k-1
    j = k - 1
    g = lambda tau: (lambda Q: j * Q['a2'] - k * Q['a1'] + 2 * Q['phi'])(q(tau))
    s3 = sqrt(3) / 2
    tau = bisect(g, s3 + 3 * beta, 1 - mpf(10) ** -12)
    Q = q(tau)
    Kang = [i * Q['a2'] for i in range(j + 1)]
    Dang = [-Q['phi'] + m * Q['a1'] for m in range(k + 1)]
    return Q, analyse('B', Q, Kang, Dang, [(0, 0), (j, k)]), j, k


def config_C(j=10100):
    g = lambda tau: (lambda Q: j * Q['a2'] - (j + 1) * Q['a1'])(q(tau))
    tau = bisect(g, mpf('0.9'), 1 - mpf(10) ** -12)
    Q = q(tau)
    Kang = [i * Q['a2'] for i in range(j + 1)]
    Dang = [Q['phi'] + m * Q['a1'] for m in range(j + 2)]
    return Q, analyse('C', Q, Kang, Dang, [(0, 0), (j, j + 1)]), j


if __name__ == '__main__':
    s3 = sqrt(3) / 2
    Q, r, M, nK, nD = config_A(k=1)
    U = M  # one unbroken gap per block
    e = r['nKK'] + r['nDD'] + r['nR'] + r['nKDT']
    s = nK + nD
    print('Config A (k=1): 1-tau = %s, t = %s, min dist - 1 = %s' % (mp.nstr(1 - Q['tau'], 6), mp.nstr(Q['t'], 20), mp.nstr(r['mind'] - 1, 6)))
    print('   unit pairs: KK=%d DD=%d rungs=%d other KD=%d; rungs as expected: %s' % (r['nKK'], r['nDD'], r['nR'], r['nKDT'], r['ok_rungs']))
    print('   window: s=%d e=%d e-s=%d, U=%d, |Q\'| (all K-points, single partner w) = %d = 2U' % (s, e, e - s, U, nK))
    assert r['mind'] > 1 - TOL and r['ok_rungs'] and r['nKDT'] == 0 and e - s == U - 1 and nK == 2 * U
    assert s3 + 3 * beta <= Q['tau'] <= 1
    Q, r, M, nK, nD = config_A(k=2, M=3)
    print('Config A2 (k=2): min dist = %s at %s  -> realisable: %s' % (mp.nstr(r['mind'], 12), r['minpair'], r['mind'] > 1 - TOL))
    assert r["mind"] < 1 - mpf(10) ** -12
    Q, r, j, k = config_B()
    print('Config B (l=-1,k=%d,j=%d): tau - (sqrt3/2+3beta) = %s, 2s = %s, min dist - 1 = %s' % (
        k, j, mp.nstr(Q['tau'] - s3 - 3 * beta, 6), mp.nstr(2 * Q['s'], 8), mp.nstr(r['mind'] - 1, 6)))
    print('   unit pairs: KK=%d DD=%d rungs=%d other KD=%d; rungs as expected: %s; arc angle = %s rad; Q\'-candidates in closed arc = %d' % (
        r['nKK'], r['nDD'], r['nR'], r['nKDT'], r['ok_rungs'], mp.nstr(j * Q['a2'], 6), j + 1))
    assert r['mind'] > 1 - TOL and r['ok_rungs'] and r['nKDT'] == 0 and r['nKK'] == j and r['nDD'] == k
    Q, r, j = config_C()
    print('Config C (same-sign, j=%d): t = %s, arc angle = %s (< pi/3 = %s); min dist = %s at %s -> realisable: %s' % (
        j, mp.nstr(Q['t'], 10), mp.nstr(j * Q['a2'], 8), mp.nstr(pi / 3, 8), mp.nstr(r['mind'], 10), r['minpair'], r['mind'] > 1 - TOL))
    assert r['mind'] < 1 - mpf(10) ** -3
    print('ALL CONFIG CHECKS PASS')
