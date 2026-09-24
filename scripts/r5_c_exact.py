"""R5/C exact verification of the family F(m, K):
    V_j = e(2 pi j/m)                    (regular odd m-gon, radius 1)
    S_j = -t   e(2 pi (j+1/2)/m)          (servers: |S_j V_j| = |S_j V_{j+1}| = Delta_2 of R_m)
    P_j = -rho e(2 pi (j+1/2)/m), j in K  (depth-3 points: |P_j V_j| = |P_j V_{j+1}| = Delta_3)
t, rho > 0 solve t^2 + 2t cos(pi/m) + 1 = Delta_2^2 and rho^2 + 2 rho cos(pi/m) + 1 = Delta_3^2,
where Delta_3 is the third largest distance of the odd ring V u S.

Every pair distance is an 'orbit function' f_{XY}(k) (X, Y in {V,S,P}, k = offset mod m).
We (1) compute all 6m orbit values symbolically (sympy), (2) group them at 60 digits,
(3) prove every within-group equality EXACTLY via sympy.minimal_polynomial(diff) == x,
(4) check between-group separation > 1e-40 at 60 digits (rigorous: sympy evalf with
    certified precision; gaps are ~1e-2), and (5) count multiplicities of any subset K
    combinatorially.  Output: exact multiplicity profile of F(m, K).
Usage: .venv/bin/python r5_c_exact.py m k   (K = {0, ..., k-1})
"""
import sys
import sympy as sp

x = sp.Symbol('x')


def build(m):
    pi = sp.pi
    c = sp.cos(pi / m)
    D2sq = (2 * sp.cos(3 * pi / (2 * m))) ** 2
    t = -c + sp.sqrt(c ** 2 - 1 + D2sq)

    def e_ang(j, half):  # angle of type point
        return 2 * pi * (sp.Rational(j) + (sp.Rational(1, 2) if half else 0)) / m

    def sq(a, al, b, be):
        return sp.expand(a ** 2 + b ** 2 - 2 * a * b * sp.cos(al - be))
    # Delta_3 of ring V u S: find numerically among orbit values, keep symbolic
    ring_vals = []
    for k in range(m):
        ring_vals.append(sq(1, 0, 1, e_ang(k, False)))
        ring_vals.append(sq(1, 0, -t, e_ang(k, True)))
        ring_vals.append(sq(-t, e_ang(0, True), -t, e_ang(k, True)))
    ring_vals = [v for v in ring_vals if sp.N(v, 30) > 1e-20]
    uniq = []
    for v in sorted(ring_vals, key=lambda v: -sp.N(v, 60)):
        if not uniq or abs(sp.N(uniq[-1] - v, 60)) > 1e-40:
            uniq.append(v)
    D3sq = uniq[2]
    rho = -c + sp.sqrt(c ** 2 - 1 + D3sq)
    rad = {'V': sp.Integer(1), 'S': -t, 'P': -rho}
    half = {'V': False, 'S': True, 'P': True}
    f = {}
    for X in 'VSP':
        for Y in 'VSP':
            for k in range(m):
                if X == Y and k == 0:
                    continue
                f[(X, Y, k)] = sq(rad[X], e_ang(0, half[X]), rad[Y], e_ang(k, half[Y]))
    return f, t, rho


def classes(f):
    items = sorted(f.items(), key=lambda kv: -sp.N(kv[1], 60))
    groups = []
    for key, v in items:
        nv = sp.N(v, 60)
        if groups and abs(groups[-1][0] - nv) < sp.Float('1e-40'):
            groups[-1][1].append((key, v))
        else:
            groups.append([nv, [(key, v)]])
    # certify
    for g in groups:
        rep = g[1][0][1]
        for key, v in g[1][1:]:
            mp = sp.minimal_polynomial(sp.nsimplify(0) + v - rep, x)
            assert mp == x, (key, mp)
    gaps = [groups[i][0] - groups[i + 1][0] for i in range(len(groups) - 1)]
    assert min(gaps) > sp.Float("1e-20")
    assert groups[-1][0] > sp.Float("1e-20")  # no coincident points
    return groups, min(gaps)


def profile(m, K, groups):
    Kset = set(K)
    pts = [('V', j) for j in range(m)] + [('S', j) for j in range(m)] + [('P', j) for j in K]
    gid = {}
    for i, g in enumerate(groups):
        for key, v in g[1]:
            gid[key] = i
    cnt = [0] * len(groups)
    for a in range(len(pts)):
        for b in range(a + 1, len(pts)):
            (X, i), (Y, j) = pts[a], pts[b]
            cnt[gid[(X, Y, (j - i) % m)]] += 1
    return len(pts), [c for c in cnt if c > 0], [float(groups[i][0]) for i in range(len(groups)) if cnt[i] > 0]


if __name__ == "__main__":
    m = int(sys.argv[1]); k = int(sys.argv[2])
    f, t, rho = build(m)
    groups, gap = classes(f)
    print(f"m={m}: {len(f)} orbit values, {len(groups)} exact classes, all equalities certified "
          f"(minimal_polynomial == x); min gap between classes {float(gap):.3e}")
    print(f"   t = {sp.N(t, 20)}, rho = {sp.N(rho, 20)}")
    for kk in sorted(set([0, 1, k, (m - 1) // 2, m])):
        n, mu, vals = profile(m, list(range(kk)), groups)
        print(f"   K=|{kk}|: n={n} exact mults (decreasing distance) = {mu[:8]}  "
              f"mu2-n={mu[1]-n} mu3-n={mu[2]-n} mu4={mu[3]}  squared dists {[round(v,6) for v in vals[:4]]}")
