"""Rigorous certification (Krawczyk interval Newton, mpmath.iv) of a member of the
r2_convex_fam family, followed by interval checks of every required property:
  * all 5n/4 Delta2-edges have length exactly 1, all n/4 Delta-edges have length exactly D
    (exact zero of the square system inside the certified box),
  * D > 1 and every other distance < 1  (so Delta = D, Delta2 = 1, mu(Delta2) = 5n/4),
  * strict convex position in the cyclic order a_0..a_{n-1},
  * no four points concyclic (every 3x3 concyclicity determinant bounded away from 0).
usage: python r2_convex_certify.py m seed eps
"""
import sys, random, itertools
import mpmath as mp
from mpmath import iv
import r2_convex_fam as fam

def main(m, sd, eps):
    mp.mp.dps = 60; iv.dps = 60
    n = 4 * m
    P, D = fam.seed_config(m)
    E1, ED = fam.edges(m)
    rng = random.Random(sd)
    P = [(x + eps * rng.uniform(-1, 1), y + eps * rng.uniform(-1, 1)) for (x, y) in P]
    D = D + eps * rng.uniform(-1, 1)
    P, D, res = fam.gauss_newton(P, D, E1, ED, iters=100, tol=mp.mpf(10) ** (-55))
    z = []
    for (x, y) in P:
        z += [x, y]
    z.append(D)
    N = len(z); neq = len(E1) + len(ED)
    J = fam.jac(P, D, E1, ED)
    # choose free columns by greedy pivoting (Gaussian elimination with column pivoting)
    Jc = J.copy(); free = []
    rows = list(range(neq)); cols = list(range(N))
    A = [[Jc[r, c] for c in range(N)] for r in range(neq)]
    used = set()
    for r in range(neq):
        best = None; bv = mp.mpf(0)
        for c in range(N):
            if c in used: continue
            if abs(A[r][c]) > bv:
                bv = abs(A[r][c]); best = c
        assert bv > mp.mpf(10) ** (-20), 'rank deficiency'
        used.add(best); free.append(best)
        for r2 in range(r + 1, neq):
            f = A[r2][best] / A[r][best]
            if f != 0:
                A[r2] = [A[r2][c] - f * A[r][c] for c in range(N)]
    fixed = [c for c in range(N) if c not in used]
    # exact (point) values: round z to 55 digits decimal strings -> exact mp numbers
    zt = [mp.mpf(mp.nstr(v, 55)) for v in z]
    def F_iv(zz):
        out = []
        for (i, j) in E1:
            out.append((zz[2 * i] - zz[2 * j]) ** 2 + (zz[2 * i + 1] - zz[2 * j + 1]) ** 2 - 1)
        for (i, j) in ED:
            out.append((zz[2 * i] - zz[2 * j]) ** 2 + (zz[2 * i + 1] - zz[2 * j + 1]) ** 2 - zz[N - 1] ** 2)
        return out
    def J_iv(zz):
        M = [[iv.mpf(0)] * len(free) for _ in range(neq)]
        pos = {c: t for t, c in enumerate(free)}
        allE = [(e, False) for e in E1] + [(e, True) for e in ED]
        for r, ((i, j), isD) in enumerate(allE):
            dx = zz[2 * i] - zz[2 * j]; dy = zz[2 * i + 1] - zz[2 * j + 1]
            for c, val in ((2 * i, 2 * dx), (2 * i + 1, 2 * dy), (2 * j, -2 * dx), (2 * j + 1, -2 * dy)):
                if c in pos: M[r][pos[c]] = val
            if isD and (N - 1) in pos:
                M[r][pos[N - 1]] = -2 * zz[N - 1]
        return iv.matrix(M)
    zpt = [iv.mpf(v) for v in zt]
    Fx = iv.matrix(F_iv(zpt))
    Jmid = mp.matrix([[J[r, c] for c in free] for r in range(neq)])
    Y = mp.inverse(Jmid)
    Yiv = iv.matrix([[iv.mpf(Y[r, c]) for c in range(neq)] for r in range(neq)])
    rad = mp.mpf(10) ** (-40)
    X = list(zpt)
    for c in free:
        X[c] = iv.mpf([zt[c] - rad, zt[c] + rad])
    JX = J_iv(X)
    I = iv.matrix(neq);
    for t in range(neq): I[t, t] = iv.mpf(1)
    dX = iv.matrix([iv.mpf([-rad, rad]) for _ in free])
    xt = iv.matrix([zpt[c] for c in free])
    K = xt - Yiv * Fx + (I - Yiv * JX) * dX
    ok = True
    for t, c in enumerate(free):
        lo = zt[c] - rad; hi = zt[c] + rad
        if not (K[t].a > lo and K[t].b < hi):
            ok = False
    print('n=%d: Krawczyk K subset int(X): %s  (radius 1e-40, %d free vars, %d fixed)' % (n, ok, len(free), len(fixed)))
    if not ok:
        return
    # interval checks on the box X
    pts = [(X[2 * i], X[2 * i + 1]) for i in range(n)]
    Dv = X[N - 1]
    S1 = set(E1); SD = set(ED)
    maxo = None; bad = 0
    for i, j in itertools.combinations(range(n), 2):
        d2 = (pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2
        if (i, j) in S1 or (i, j) in SD:
            continue
        if not (d2.b < 1): bad += 1
        maxo = d2.b if maxo is None or d2.b > maxo else maxo
    print('  D in [%s, %s]  (D > 1: %s)' % (mp.nstr(mp.mpf(Dv.a), 12), mp.nstr(mp.mpf(Dv.b), 12), Dv.a > 1))
    print('  non-edge squared distances: max upper bound %s ; violations of <1: %d' % (mp.nstr(mp.mpf(maxo), 12), bad))
    mt = None
    for i in range(n):
        o, a, b = pts[i - 1], pts[i], pts[(i + 1) % n]
        cr = (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        mt = cr.a if mt is None or cr.a < mt else mt
    ms = None
    for i in range(n):
        a, b = pts[i], pts[(i + 1) % n]
        for q in range(n):
            if q in (i, (i + 1) % n): continue
            cr = (b[0] - a[0]) * (pts[q][1] - a[1]) - (b[1] - a[1]) * (pts[q][0] - a[0])
            ms = cr.a if ms is None or cr.a < ms else ms
    print('  convexity: min turn lower bound %s ; min (unnormalised) side test lower bound %s' % (mp.nstr(mp.mpf(mt), 6), mp.nstr(mp.mpf(ms), 6)))
    mind = None; arg = None; zero = 0
    for q in itertools.combinations(range(n), 4):
        p4 = pts[q[3]]
        rws = []
        for t in range(3):
            dx = pts[q[t]][0] - p4[0]; dy = pts[q[t]][1] - p4[1]
            rws.append((dx, dy, dx * dx + dy * dy))
        (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) = rws
        det = a1 * (b2 * c3 - b3 * c2) - b1 * (a2 * c3 - a3 * c2) + c1 * (a2 * b3 - a3 * b2)
        lo = det.a if det.a > 0 else (-det.b if det.b < 0 else mp.mpf(0))
        if lo == 0: zero += 1
        if mind is None or lo < mind:
            mind = lo; arg = q
    print('  concyclicity: min |det| lower bound over all %d quadruples = %s at %s ; quadruples not certified: %d' % (
        len(list(itertools.combinations(range(n), 4))), mp.nstr(mp.mpf(mind), 6), arg, zero))
    print('  mu(Delta2) = %d = n + %d ; mu(Delta) = %d' % (len(E1), len(E1) - n, len(ED)))
    with open('certified_n%d.txt' % n, 'w') as f:
        f.write('# n=%d seed=%d eps=%s ; points a_0..a_{n-1} (55 digits), then D\n' % (n, sd, eps))
        for i in range(n):
            f.write('%s %s\n' % (mp.nstr(zt[2 * i], 55), mp.nstr(zt[2 * i + 1], 55)))
        f.write('D %s\n' % mp.nstr(zt[N - 1], 55))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]))
