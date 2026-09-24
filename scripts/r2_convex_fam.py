"""Candidate counterexample family to the convex case of Conjecture C1.
n = 4m points a_0..a_{n-1} (cyclic order), k = n/2, theta = 2 pi / n.
Symmetric seed: even a_{2y} = (1/2) e(2y theta), odd a_{2y+1} = R2 e((2y+1) theta),
R2 = (-cos t + sqrt(cos^2 t + 3))/2.  Delta2 = 1 edges: a_x a_{x+k+-1} (n of them) and
even antipodal pairs a_{2y} a_{2y+k} (n/4); Delta = 2 R2 edges: odd antipodal (n/4).
mu(Delta2) = 5n/4.  The seed is concyclic; we perturb along the solution variety
(Newton / Gauss-Newton projection) to destroy all concyclic quadruples.

usage: python r2_convex_fam.py m seed eps [dps]
"""
import sys, random, itertools
import mpmath as mp

def seed_config(m):
    n = 4 * m; k = n // 2
    t = 2 * mp.pi / n
    R2 = (-mp.cos(t) + mp.sqrt(mp.cos(t) ** 2 + 3)) / 2
    P = []
    for x in range(n):
        r = mp.mpf(1) / 2 if x % 2 == 0 else R2
        P.append((r * mp.cos(x * t), r * mp.sin(x * t)))
    D = 2 * R2
    return P, D

def edges(m):
    n = 4 * m; k = n // 2
    E1 = set()
    for x in range(n):
        for y in ((x + k + 1) % n, (x + k - 1) % n):
            E1.add((min(x, y), max(x, y)))
    for x in range(0, n, 2):
        y = (x + k) % n
        E1.add((min(x, y), max(x, y)))
    ED = set()
    for x in range(1, n, 2):
        y = (x + k) % n
        ED.add((min(x, y), max(x, y)))
    return sorted(E1), sorted(ED)

def residual(P, D, E1, ED):
    F = []
    for (i, j) in E1:
        F.append((P[i][0] - P[j][0]) ** 2 + (P[i][1] - P[j][1]) ** 2 - 1)
    for (i, j) in ED:
        F.append((P[i][0] - P[j][0]) ** 2 + (P[i][1] - P[j][1]) ** 2 - D ** 2)
    # gauge: fix a_0 x,y and a_1 direction (3 eqs)
    return F

def jac(P, D, E1, ED):
    n = len(P); N = 2 * n + 1
    rows = []
    for (i, j) in E1:
        r = [mp.mpf(0)] * N
        dx = P[i][0] - P[j][0]; dy = P[i][1] - P[j][1]
        r[2 * i] = 2 * dx; r[2 * i + 1] = 2 * dy; r[2 * j] = -2 * dx; r[2 * j + 1] = -2 * dy
        rows.append(r)
    for (i, j) in ED:
        r = [mp.mpf(0)] * N
        dx = P[i][0] - P[j][0]; dy = P[i][1] - P[j][1]
        r[2 * i] = 2 * dx; r[2 * i + 1] = 2 * dy; r[2 * j] = -2 * dx; r[2 * j + 1] = -2 * dy
        r[2 * n] = -2 * D
        rows.append(r)
    return mp.matrix(rows)

def gauss_newton(P, D, E1, ED, iters=60, tol=None):
    n = len(P)
    for it in range(iters):
        F = mp.matrix(residual(P, D, E1, ED))
        nr = mp.norm(F)
        if tol is not None and nr < tol:
            break
        J = jac(P, D, E1, ED)
        # minimum-norm step: dz = -J^T (J J^T)^{-1} F
        JJt = J * J.T
        y = mp.lu_solve(JJt, F)
        dz = -(J.T * y)
        P = [(P[i][0] + dz[2 * i], P[i][1] + dz[2 * i + 1]) for i in range(n)]
        D = D + dz[2 * n]
    return P, D, mp.norm(mp.matrix(residual(P, D, E1, ED)))

def analyse(P, D, E1, ED):
    n = len(P)
    S1 = set(E1); SD = set(ED)
    d = {}
    worst_eq = mp.mpf(0); max_other = mp.mpf(-1); max_all = mp.mpf(0)
    for i, j in itertools.combinations(range(n), 2):
        dd = mp.sqrt((P[i][0] - P[j][0]) ** 2 + (P[i][1] - P[j][1]) ** 2)
        d[i, j] = dd
        if (i, j) in S1:
            worst_eq = max(worst_eq, abs(dd - 1))
        elif (i, j) in SD:
            worst_eq = max(worst_eq, abs(dd - D))
        else:
            max_other = max(max_other, dd)
    # convexity: cyclic order a_0..a_{n-1} counterclockwise, strict turns and all points left of each edge
    min_turn = mp.inf
    for i in range(n):
        o, a, b = P[i - 1], P[i], P[(i + 1) % n]
        cr = (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
        min_turn = min(min_turn, cr)
    min_side = mp.inf
    for i in range(n):
        a, b = P[i], P[(i + 1) % n]
        L = mp.sqrt((b[0] - a[0]) ** 2 + (b[1] - a[1]) ** 2)
        for q in range(n):
            if q in (i, (i + 1) % n):
                continue
            cr = ((b[0] - a[0]) * (P[q][1] - a[1]) - (b[1] - a[1]) * (P[q][0] - a[0])) / L
            min_side = min(min_side, cr)
    # concyclicity: normalised det  (divide by product of the 6 pairwise distances^(1/...)?)
    # use |det[[x,y,x^2+y^2,1]]| / (prod of pairwise distances)^(1/2) which is scale-invariant (deg 4 vs deg 3)
    min_cc = mp.inf; arg = None
    for q in itertools.combinations(range(n), 4):
        M = mp.matrix([[P[i][0], P[i][1], P[i][0] ** 2 + P[i][1] ** 2, 1] for i in q])
        det = abs(mp.det(M))
        pr = mp.mpf(1)
        for a_, b_ in itertools.combinations(q, 2):
            pr *= d[a_, b_]
        val = det / mp.sqrt(pr)
        if val < min_cc:
            min_cc = val; arg = q
    mu2 = sum(1 for v in d.values() if abs(v - 1) < mp.mpf(10) ** (-30))
    muD = sum(1 for v in d.values() if abs(v - D) < mp.mpf(10) ** (-30))
    return dict(worst_eq=worst_eq, max_other=max_other, D=D, min_turn=min_turn,
                min_side=min_side, min_cc=min_cc, cc_arg=arg, mu2=mu2, muD=muD, n=n)

if __name__ == '__main__':
    m = int(sys.argv[1]); sd = int(sys.argv[2]); eps = float(sys.argv[3])
    mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    P, D = seed_config(m)
    E1, ED = edges(m)
    n = 4 * m
    J = jac(P, D, E1, ED)
    # numeric rank via SVD in float
    sv = mp.svd_r(J, compute_uv=False)
    svl = [sv[i] for i in range(len(sv))]
    print('n=%d  #eq=%d  #unknowns=%d  rank=%d  smallest sv=%s' % (n, J.rows, J.cols, sum(1 for x in svl if x > mp.mpf(10)**(-mp.mp.dps//2)), mp.nstr(min(svl), 5)))
    a0 = analyse(P, D, E1, ED)
    print('seed: mu2=%d muD=%d D=%s max_other=%s min_cc=%s' % (a0['mu2'], a0['muD'], mp.nstr(D, 12), mp.nstr(a0['max_other'], 12), mp.nstr(a0['min_cc'], 5)))
    rng = random.Random(sd)
    P = [(x + eps * rng.uniform(-1, 1), y + eps * rng.uniform(-1, 1)) for (x, y) in P]
    D = D + eps * rng.uniform(-1, 1)
    P, D, res = gauss_newton(P, D, E1, ED, iters=100, tol=mp.mpf(10) ** (-(mp.mp.dps - 5)))
    a = analyse(P, D, E1, ED)
    for key in ('n', 'mu2', 'muD', 'D', 'worst_eq', 'max_other', 'min_turn', 'min_side', 'min_cc', 'cc_arg'):
        v = a[key]
        print(key, mp.nstr(v, 15) if isinstance(v, mp.mpf) else v)
    print('mu2 - n =', a['mu2'] - n)
    import pickle
    pickle.dump({'P': [(str(x), str(y)) for x, y in P], 'D': str(D), 'E1': E1, 'ED': ED},
                open('fam_m%d_s%d.pkl' % (m, sd), 'wb'))
