"""REF_C (R7): adversarial exact (80-digit) local configurations for Theorem W.

For each configuration we list named points, check the metric constraints of X (min distance 1 attained only by the
intended unit pairs, NO distance in (R, Delta), none > Delta), then test which D-points can possibly be in S by
enumerating the candidate Delta_2-partners forced by the cone lemma, and report the local run ratio.

 (A)  G = 1 two-gap run v0 z0 v1 z1 v2 (the claimed extremal ratio 2/3).
 (A2) G = 1 two runs at one centre, v0..v5, z0 z1 . z3 z4 (z2 absent): are z1, z3 in S possible?
 (B)  d = 0 double triangle in one E_w: Z = z1..z4, apexes v (base z1z2), v'' (base z3z4), successor v''+.
 (C)  G >= 2 alternating run S-A-S at the l=+1, k=2 resonance (G = 3 - O(1/R)): singleton gap, arc gap (j=3,k=2),
      singleton gap, three centres.  Metric consistency check (NC-type obstructions?).
"""
from mpmath import mp, mpf, sqrt, sin, cos, asin, acos, pi, atan2, findroot, e as E
mp.dps = 80
TOL = mpf(10) ** -40

def J(a): return (-a[1], a[0])
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def mul(c, a): return (c * a[0], c * a[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def nrm(a): return sqrt(dot(a, a))
def pol(r, th): return (r * cos(th), r * sin(th))

def params(R, tau):
    t = -R + sqrt(R * R + 1 + 2 * R * tau)
    return t, R + t, sqrt(1 - tau * tau)

def circ_inter(c1, r1, c2, r2):
    d = nrm(sub(c2, c1)); a = (r1 * r1 - r2 * r2 + d * d) / (2 * d); h2 = r1 * r1 - a * a
    if h2 < 0: return []
    h = sqrt(h2); e = mul(1 / d, sub(c2, c1)); m = add(c1, mul(a, e))
    return [add(m, mul(h, J(e))), add(m, mul(-h, J(e)))]

def o(u, sigma, tau, s): return add(mul(-tau, u), mul(sigma * s, J(u)))
def o_inv(vec, sigma, tau, s): return add(mul(-tau, vec), mul(-sigma * s, J(vec)))
def ang(a, b): return abs(atan2(a[0] * b[1] - a[1] * b[0], dot(a, b)))

def partner(v, u, z, sigma, tau, s):
    best = None
    for vp in circ_inter(v, mpf(1), z, mpf(1)):
        up = o_inv(sub(z, vp), -sigma, tau, s)
        if best is None or ang(u, up) < best[0]: best = (ang(u, up), vp, up)
    assert best[0] <= mpf('0.02')
    return best[1], best[2]

def metric_check(pts, R, D, unit_expected):
    bad = []; units = set()
    names = list(pts)
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = names[i], names[j]; d = nrm(sub(pts[a], pts[b]))
            if d < 1 - TOL: bad.append(('<1', a, b, mp.nstr(d, 8)))
            elif abs(d - 1) < TOL: units.add(frozenset((a, b)))
            elif R + TOL < d < D - TOL: bad.append(('in(R,D)', a, b, mp.nstr(d - R, 8)))
            elif d > D + TOL: bad.append(('>D', a, b, mp.nstr(d - D, 8)))
    exp = set(frozenset(p) for p in unit_expected)
    return bad, units == exp, units - exp, exp - units

def dist_class(pts, R, D, a, b):
    d = nrm(sub(pts[a], pts[b]))
    return 'R' if abs(d - R) < TOL else ('D' if abs(d - D) < TOL else None)

def partner_candidates_excluded(pts, R, D, zi, zk):
    """cone-lemma candidates y in C(zk, D) cap C(zi, R); return list of (excluded?, reason)."""
    res = []
    for y in circ_inter(pts[zk], D, pts[zi], R):
        reason = None
        for nme, p in pts.items():
            d = nrm(sub(y, p))
            if d < 1 - TOL and d > TOL: reason = '<1 from %s' % nme; break
            if R + TOL < d < D - TOL: reason = 'in(R,D) from %s (%s)' % (nme, mp.nstr(d - R, 6)); break
            if d > D + TOL: reason = '>D from %s' % nme; break
        res.append(reason)
    return res

def tau_of_G(R, G): return cos(pi / 6 + asin(G / (2 * R)))

R = mpf(10) ** 4
out_ok = True
# ---------------- (A) and (A2): G = 1 ----------------
tau = tau_of_G(R, mpf(1)); t, D, s = params(R, tau)
a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * D)); phi = asin(s / D)
assert abs(2 * phi - a2) < TOL
pts = {'w': (mpf(0), mpf(0))}
for i in range(6): pts['v%d' % i] = pol(R, i * a2)
for i in [0, 1, 3, 4]: pts['z%d' % i] = pol(D, (i + mpf(1) / 2) * a2)
unit = [('v%d' % i, 'v%d' % (i + 1)) for i in range(5)] + [('v%d' % i, 'z%d' % i) for i in [0, 1, 3, 4]] + \
       [('v%d' % (i + 1), 'z%d' % i) for i in [0, 1, 3, 4]]
bad, same, extra, missing = metric_check(pts, R, D, unit)
print('(A2) G=1 two runs at one centre: metric violations %d, unit pairs exactly T-edges+rungs: %s' % (len(bad), same))
out_ok &= (not bad) and same
# cone lemma refinement: X cap C(w,D) = {z0,z1,z3,z4}; partner of z1 (2nd) must be diametral to z0
for zi, zk in [('z1', 'z0'), ('z3', 'z4')]:
    r = partner_candidates_excluded(pts, R, D, zi, zk)
    print('     partners of %s (must be diametral to %s): candidates excluded by %s' % (zi, zk, r))
    out_ok &= all(x is not None for x in r)
print('     => in (A2) z1, z3 are NOT in S: the four gaps are not all rung-gaps; ratio collapses (<= 2 gaps / 6 K-points)')
# (A) single two-gap run: X cap C(w,D) = {z0, z1}; cone lemma gives no constraint; ratio 2/3
ptsA = {k: pts[k] for k in ['w', 'v0', 'v1', 'v2', 'z0', 'z1']}
bad, same, _, _ = metric_check(ptsA, R, D, [('v0', 'v1'), ('v1', 'v2'), ('v0', 'z0'), ('v1', 'z0'), ('v1', 'z1'), ('v2', 'z1')])
print('(A)  G=1 two-gap run: metric violations %d, units exact %s; gaps 2, K-points 3 -> local ratio 2/3 (= theta)' % (len(bad), same))
# can z0 get a partner at all here?  search y on C(z0,R) with all distances to the 5 others in [1,R] or = D
import mpmath
feasible = 0
N = 4000
for k in range(N):
    th = 2 * pi * k / N
    y = add(ptsA['z0'], pol(R, th))
    okk = True
    for nme, p in ptsA.items():
        d = nrm(sub(y, p))
        if d < 1 or (R + TOL < d < D - TOL) or d > D + TOL: okk = False; break
    feasible += okk
print('     partner positions for z0 on C(z0,R) compatible with the local set: %d/%d samples' % (feasible, N))

# ---------------- (B): d = 0 double triangle ----------------
tau = sqrt(3) / 2; t, D, s = params(R, tau)
a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * D)); phi = asin(s / D)
assert abs(2 * phi - a1) < TOL
ptsB = {'w': (mpf(0), mpf(0))}
for i in range(1, 5): ptsB['z%d' % i] = pol(D, i * a1)
ptsB['v'] = pol(R, mpf(3) / 2 * a1); ptsB['vv'] = pol(R, mpf(7) / 2 * a1); ptsB['vv+'] = pol(R, mpf(7) / 2 * a1 + a2)
unitB = [('z1', 'z2'), ('z2', 'z3'), ('z3', 'z4'), ('v', 'z1'), ('v', 'z2'), ('vv', 'z3'), ('vv', 'z4'), ('vv', 'vv+')]
bad, same, extra, missing = metric_check(ptsB, R, D, unitB)
print('(B)  d=0 double triangle: metric violations %s, units exact %s (extra %s)' % (bad, same, [tuple(x) for x in extra]))
print('     |v vv| = %s (break, no K-point fits between: 2 a1 < 2 a2)' % mp.nstr(nrm(sub(ptsB['v'], ptsB['vv'])), 12))
for zi, zk in [('z2', 'z1'), ('z3', 'z4')]:
    r = partner_candidates_excluded(ptsB, R, D, zi, zk)
    print('     partners of %s (2nd of 4, must be diametral to %s): %s' % (zi, zk, r))
print('     local charging: T=2, v type C (psi(v)=vv is an apex: C2), vv type A (vv+ in Q\'): e-s <= 2, |Q\'| >= 3 -> 2/3')

# ---------------- (C): G >= 2 alternating S-A-S at the k=2 resonance ----------------
def res_tau(R, k):
    def f(tau):
        t, D, s = params(R, tau)
        a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * D))
        return 2 * asin(s / D) - (a2 + k * (a2 - a1))
    return mp.re(findroot(f, sqrt(3) / 2, tol=mpf(10)**-70))
for kk in [2, 3]:
    tau = res_tau(R, kk); t, D, s = params(R, tau)
    a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * D)); phi = asin(s / D)
    G = 2 * R * sin(acos(tau) - pi / 6)
    j = kk + 1
    P = {'w1': (mpf(0), mpf(0))}
    thA = mpf(0)
    for i in range(j + 1): P['a%d' % i] = pol(R, thA + i * a2)          # a0 = v_A ... a_j = v_B
    for i in range(kk + 1): P['Z%d' % i] = pol(D, thA + phi + i * a1)   # z_A = Z0 ... z_B = Z_k
    assert abs(nrm(sub(P['Z%d' % kk], P['a%d' % j])) - 1) < TOL
    # other rungs: v_A left-directed rung, v_B right-directed rung
    P['zL'] = pol(D, thA - phi); P['zR'] = pol(D, thA + j * a2 + phi)
    # singleton partner of v_A through zL, and of v_B through zR
    uA = mul(-1 / R, P['a0']); uB = mul(-1 / R, P['a%d' % j])
    # sigma of rung (v_A, zL) w.r.t. uA
    for sg in [1, -1]:
        if nrm(sub(add(P['a0'], o(uA, sg, tau, s)), P['zL'])) < TOL: sL = sg
        if nrm(sub(add(P['a%d' % j], o(uB, sg, tau, s)), P['zR'])) < TOL: sR = sg
    vm, um = partner(P['a0'], uA, P['zL'], sL, tau, s)
    vp, up = partner(P['a%d' % j], uB, P['zR'], sR, tau, s)
    P['vm'] = vm; P['vp'] = vp; P['w0'] = add(vm, mul(R, um)); P['w2'] = add(vp, mul(R, up))
    unitC = [('a%d' % i, 'a%d' % (i + 1)) for i in range(j)] + [('Z%d' % i, 'Z%d' % (i + 1)) for i in range(kk)] + \
            [('a0', 'Z0'), ('a%d' % j, 'Z%d' % kk), ('a0', 'zL'), ('vm', 'zL'), ('vm', 'a0'),
             ('a%d' % j, 'zR'), ('vp', 'zR'), ('vp', 'a%d' % j)]
    bad, same, extra, missing = metric_check(P, R, D, unitC)
    print('(C)  S-A-S at k=%d resonance (G = %s, |w0w1| = %s): metric violations:' % (kk, mp.nstr(G, 10), mp.nstr(nrm(P['w0']), 10)))
    for b in bad: print('       ', b)
    print('       unit pairs exact: %s  extra %s missing %s' % (same, [tuple(x) for x in extra], [tuple(x) for x in missing]))
    print('       ratio if realisable: 3 gaps / %d K-points' % (j + 1 + 2))
assert out_ok
print('r7_refC_adv: done')
