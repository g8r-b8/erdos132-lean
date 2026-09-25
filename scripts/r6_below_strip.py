"""Exact (60-digit mpmath) check of the single-centre 'hexagonal strip' (Region III resonance).

w = 0, R = Delta_2.  K-row: v_i = R e(i*a2), a2 = 2 asin(1/(2R))  (consecutive |v_i v_{i+1}| = 1).
D-row: z_i = Delta e((i+1/2) a2) with Delta chosen so that |z_i v_i| = |z_i v_{i+1}| = 1.
Checks: all pairwise distances in a window >= 1 - 1e-50; the unit pairs are exactly the T-edges v_i v_{i+1}
and the rungs v_i z_i, v_{i+1} z_i; |z_i z_{i+1}| = Delta/R > 1 (every z is a singleton D-component);
tau = t - (1-t^2)/(2R) is in Region III (sqrt3/2 - 2beta, sqrt3/2 + 3beta); the rung is an exception
(|z - w| = Delta exactly, (z - v).u_v = -tau exactly); dist(z, D(w,R)) = t; rung goodness angle
between u_v and u_z (u_z = (w - z)/Delta) is < beta.
Local counts per period (1 K-point + 1 D-point): e = 1 T-edge + 2 rungs = 3, s = 2, so e - s = 1 = one
Q-point (v_i has the single Delta_2-partner w: it is a relative-interior point of the arc).
Also computes the 'D-triangle' resonance (phi = a1/2) and the rung angle phi = atan(s/(R+tau)).
"""
from mpmath import mp, mpf, asin, cos, sin, sqrt, atan, acos, pi, findroot

mp.dps = 60
beta = mpf(1) / 100


def e(th):
    return (cos(th), sin(th))


def d(p, q):
    return sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)


def strip(R, N=12):
    a2 = 2 * asin(1 / (2 * R))
    c = cos(a2 / 2)
    Dl = R * c + sqrt(R * R * c * c - (R * R - 1))
    t = Dl - R
    tau = t - (1 - t * t) / (2 * R)
    V = [tuple(R * x for x in e(i * a2)) for i in range(N)]
    Z = [tuple(Dl * x for x in e((i + mpf(1) / 2) * a2)) for i in range(N - 1)]
    pts = [('v', i, p) for i, p in enumerate(V)] + [('z', i, p) for i, p in enumerate(Z)]
    unit = []
    tol = mpf(10) ** -45
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            dd = d(pts[i][2], pts[j][2])
            assert dd > 1 - tol, (pts[i][:2], pts[j][:2], dd)
            if abs(dd - 1) < tol:
                unit.append((pts[i][:2], pts[j][:2]))
    # expected unit pairs
    exp = set()
    for i in range(N - 1):
        exp.add((('v', i), ('v', i + 1)))
        exp.add((('v', i), ('z', i)))
        exp.add((('v', i + 1), ('z', i)))
    got = set(tuple(sorted(u)) for u in unit)
    exp = set(tuple(sorted(u)) for u in exp)
    assert got == exp, (got ^ exp)
    # z-z distance
    zz = d(Z[0], Z[1])
    assert zz > 1 and abs(zz - Dl / R) < tol
    # region III
    s3 = sqrt(3) / 2
    assert s3 - 2 * beta < tau < s3 + 3 * beta
    # exception identity for rung v_0 z_0
    v, z = V[0], Z[0]
    u = (-v[0] / R, -v[1] / R)
    dot = (z[0] - v[0]) * u[0] + (z[1] - v[1]) * u[1]
    assert abs(dot + tau) < tol
    assert abs(d(z, (0, 0)) - Dl) < tol and abs((d(z, (0, 0)) - R) - t) < tol
    uz = (-z[0] / Dl, -z[1] / Dl)
    ang = acos(u[0] * uz[0] + u[1] * uz[1])
    assert ang < beta
    s = sqrt(1 - tau * tau)
    phi = atan(s / (R + tau))
    assert abs(phi - a2 / 2) < tol  # the resonance condition phi = alpha_2/2
    # per-period counts
    e_S = (N - 1) + 2 * (N - 1)  # T-edges + rungs among the window
    s_S = N + (N - 1)
    return dict(t=t, tau=tau, tau_minus=tau - s3, zz_minus_1=zz - 1, rung_angle=ang,
                eS_minus_s=e_S - s_S, q=N)


def dtriangle_tau(R):
    """tau at which phi = alpha_1/2 (apex v over a unit D-D base): R4's exact tau = sqrt3/2 case."""
    def f(t):
        Dl = R + t
        a1 = 2 * asin(1 / (2 * Dl))
        tau = t - (1 - t * t) / (2 * R)
        s = sqrt(1 - tau * tau)
        return atan(s / (R + tau)) - a1 / 2
    t = findroot(f, mpf('0.866'))
    return t, t - (1 - t * t) / (2 * R)


if __name__ == "__main__":
    for R in [mpf(10) ** 4, mpf(10) ** 5, mpf(10) ** 6]:
        r = strip(R)
        print('R=%s t=%s tau-sqrt3/2=%s (x R = %s) zz-1=%s rung-angle=%s  window: e-s=%s with q=%s' % (
            mp.nstr(R, 3), mp.nstr(r['t'], 25), mp.nstr(r['tau_minus'], 12), mp.nstr(r['tau_minus'] * R, 12),
            mp.nstr(r['zz_minus_1'], 8), mp.nstr(r['rung_angle'], 5), r['eS_minus_s'], r['q']))
        tD, tauD = dtriangle_tau(R)
        print('   D-triangle resonance: tau - sqrt3/2 = %s (x R = %s)' % (
            mp.nstr(tauD - sqrt(3) / 2, 12), mp.nstr((tauD - sqrt(3) / 2) * R, 12)))
    print('strip checks pass')
