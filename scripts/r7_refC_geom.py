"""REF_C (R7): independent first-principles re-derivation of Lemmas SG, NC, P4 (high precision, mpmath).

Construction from definitions only (no closed forms from branch C):
  delta = 1, R = Delta_2, tau given, t solves tau = t - (1 - t^2)/(2R), Delta = R + t, s = sqrt(1 - tau^2).
  A K-point v with centre w (u = (w - v)/R) has rung ends z = v + o_sigma(u), o_sigma(u) = -tau u + sigma s J u
  (J = rotation by +90 deg).  Given a rung (v, z) (sigma), a singleton-gap partner v' is a point with |v'z| = |v'v| = 1;
  its normal u' is recovered from z - v' = o_{-sigma}(u') (o is a rotation, invertible); w' = v' + R u'.
Checks:
  SG: |w w'| = |1 - G|, |v' - w|^2 - R^2 = 1 - G, with G = 2R sin(theta0 - pi/6).
  NC: chain v0 -> v1 -> v2 (v1's other rung), |z0 w2| strictly in (R, Delta) for G > 1 (and w2 = w0.. for G = 1).
  P4: at G = 1 build v0..v3, z0..z2 by the same chain; partners of z1 diametral to z0: y in C(z0,Delta) cap C(z1,R);
      check |y - w| > Delta or R < |y - v0| < Delta; mirror with z2, v3.
"""
from mpmath import mp, mpf, sqrt, sin, cos, asin, pi, matrix
mp.dps = 80

def J(a):
    return (-a[1], a[0])
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def mul(c, a): return (c * a[0], c * a[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def nrm(a): return sqrt(dot(a, a))

def params(R, tau):
    # tau = t - (1 - t^2)/(2R)  ->  t^2 + 2R t - (1 + 2R tau) = 0
    t = -R + sqrt(R * R + 1 + 2 * R * tau)
    return t, R + t, sqrt(1 - tau * tau)

def o(u, sigma, tau, s):
    return add(mul(-tau, u), mul(sigma * s, J(u)))

def o_inv(vec, sigma, tau, s):
    # vec = -tau u + sigma s J u = M u with M = [[-tau, -sigma s],[sigma s, -tau]] (orthogonal, det 1)
    a, b = -tau, sigma * s
    # M = a I + b J ; inverse = a I - b J
    return add(mul(a, vec), mul(-b, J(vec)))

def circ_inter(c1, r1, c2, r2):
    d = nrm(sub(c2, c1))
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h = sqrt(r1 * r1 - a * a)
    e = mul(1 / d, sub(c2, c1))
    m = add(c1, mul(a, e))
    return add(m, mul(h, J(e))), add(m, mul(-h, J(e)))

def angle(a, b):
    import mpmath
    return abs(mpmath.atan2(a[0] * b[1] - a[1] * b[0], dot(a, b)))

def partner(v, u, z, sigma, tau, s, beta=mpf('0.01')):
    """the K-point v' with |v'z| = |v'v| = 1 whose rung (v', z) has sign -sigma and good normal."""
    out = []
    for vp in circ_inter(v, mpf(1), z, mpf(1)):
        up = o_inv(sub(z, vp), -sigma, tau, s)
        out.append((angle(u, up), vp, up))
    out.sort(key=lambda x: x[0])
    ang, vp, up = out[0]
    assert ang <= 2 * beta, ang
    return vp, up

def chain(R, tau, nsteps):
    t, D, s = params(R, tau)
    w0 = (mpf(0), mpf(0))
    v = (mpf(0), -R); u = (mpf(0), mpf(1))
    sigma = 1
    vs, us, zs, ws = [v], [u], [], [w0]
    for k in range(nsteps):
        z = add(v, o(u, sigma, tau, s))
        vp, up = partner(v, u, z, sigma, tau, s)
        zs.append(z); vs.append(vp); us.append(up); ws.append(add(vp, mul(R, up)))
        v, u = vp, up            # v' carries rung (v', z) with -sigma; its other rung has +sigma = sigma again
    return t, D, s, vs, us, zs, ws

def G_of(R, tau):
    import mpmath
    th = mpmath.acos(tau)
    return 2 * R * sin(th - pi / 6)

def tau_of_G(R, G):
    return cos(pi / 6 + asin(G / (2 * R)))

ok = True
print('--- SG and NC ---')
for R in [mpf(10) ** 4, mpf(10) ** 6, mpf(10) ** 9]:
    for G in [mpf(1), mpf(2), mpf('2.5'), mpf(3), mpf(7), mpf(100), mpf('0.0199') * R]:
        tau = tau_of_G(R, G)
        assert tau > sqrt(3) / 2 - mpf('0.02') and tau < sqrt(3) / 2 + mpf('0.03')
        t, D, s, vs, us, zs, ws = chain(R, tau, 2)
        wwp = nrm(sub(ws[1], ws[0]))
        sg1 = abs(wwp - abs(1 - G))
        sg2 = abs(dot(sub(vs[1], ws[0]), sub(vs[1], ws[0])) - R * R - (1 - G))
        # rung checks
        for j in range(2):
            assert abs(nrm(sub(zs[j], ws[j])) - D) < mpf(10) ** -50
            assert abs(nrm(sub(zs[j], ws[j + 1])) - D) < mpf(10) ** -50
            assert abs(nrm(sub(vs[j + 1], vs[j])) - 1) < mpf(10) ** -50
        z0w2 = nrm(sub(zs[0], ws[2]))
        gap = D * D - z0w2 ** 2
        inside = (z0w2 > R) and (z0w2 < D)
        line = 'R=%.0e G=%-10s |ww\'|-|1-G|=%.1e  |v\'w|^2-R^2-(1-G)=%.1e  D^2-|z0w2|^2=%s  (2(G-1)=%s)  in(R,D): %s' % (
            float(R), mp.nstr(G, 6), float(sg1), float(sg2), mp.nstr(gap, 8), mp.nstr(2 * (G - 1), 8), inside)
        print(line)
        assert sg1 < mpf(10) ** -40 and sg2 < mpf(10) ** -30
        if G > 1:
            ok &= bool(inside)
        else:
            ok &= abs(gap) < mpf(10) ** -30
print('SG identities and NC (|z0 w2| in (R,Delta) for G>1; = Delta at G=1):', ok)

print('--- P4 at G = 1 ---')
import mpmath
worst_plus = None; worst_minus_lo = None; worst_minus_hi = None
Rs = [mpf(10) ** (4 + k / mpf(4)) for k in range(0, 45)]   # 1e4 .. 1e15
p4ok = True
for R in Rs:
    tau = tau_of_G(R, mpf(1))
    t, D, s, vs, us, zs, ws = chain(R, tau, 3)
    w = ws[0]
    for wj in ws:
        assert nrm(sub(wj, w)) < mpf(10) ** -40     # same centre
    # all distances in the strip window: unit pairs, nothing in (R, D)
    for (za, zb, vend) in [(zs[0], zs[1], vs[0]), (zs[2], zs[1], vs[3])]:
        for y in circ_inter(za, D, zb, R):
            dw = nrm(sub(y, w)); dv = nrm(sub(y, vend))
            if dw > D:
                m = dw - D
                worst_plus = m if worst_plus is None else min(worst_plus, m)
            elif R < dv < D:
                lo, hi = D * D - dv * dv, dv * dv - R * R
                worst_minus_lo = lo if worst_minus_lo is None else min(worst_minus_lo, lo)
                worst_minus_hi = hi if worst_minus_hi is None else min(worst_minus_hi, hi)
            else:
                p4ok = False
                print('P4 FAIL at R=', R, dw, dv)
print('P4: every candidate partner of z1 excluded for R in [1e4,1e15] (45 values):', p4ok)
print('    min |y+ - w| - Delta = %s ; min Delta^2-|y- - v_end|^2 = %s ; min |y- - v_end|^2 - R^2 = %s' % (
    mp.nstr(worst_plus, 8), mp.nstr(worst_minus_lo, 8), mp.nstr(worst_minus_hi, 8)))
# series of Delta^2 - |y- - v0|^2: compare to 3 - 4 sqrt3/R
for R in [mpf(10) ** 4, mpf(10) ** 8]:
    tau = tau_of_G(R, mpf(1)); t, D, s, vs, us, zs, ws = chain(R, tau, 3)
    ys = circ_inter(zs[0], D, zs[1], R)
    for y in ys:
        dv = nrm(sub(y, vs[0]))
        if dv < D:
            print('    R=%.0e: Delta^2-|y-v0|^2 = %s vs 3-4sqrt3/R = %s' % (float(R), mp.nstr(D * D - dv * dv, 15), mp.nstr(3 - 4 * sqrt(3) / R, 15)))
assert ok and p4ok
print('r7_refC_geom: PASS')
