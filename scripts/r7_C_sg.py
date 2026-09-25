"""R7/C: Lemma SG (singleton-gap centres), exact.

Setting: rung (v,z) w.r.t. u = u_v (z - v = -tau u + sig s iu) and rung (v',z) w.r.t. u' = u_{v'}
(z - v' = -tau u' - sig s iu'), angle(u,u') = gamma, mean normal e(m).  s = sin th0, tau = cos th0.
Claims (symbolic):
 (a) v' - v = 2 sig sin(th0 + sig gamma/2) i e(m); so |vv'| = 1 (small gamma) <=> sig gamma/2 = pi/6 - th0 =: c.
 With G := 2R sin(th0 - pi/6) = -2R sin c, w = v + R u, w' = v' + R u':
 (b) w' - w = sig (1 - G) i e(m)                 => |w w'| = |1 - G|
 (c) |v' - w|^2 = R^2 + 1 - G,  |v - w'|^2 = R^2 + 1 - G.
Consequence (Lemma SG): v' in K subset D(w,R) forces G >= 1; G = 1 <=> w = w'; otherwise |ww'| = G-1 >= 1 (w,w' in X).
Also: exact relation to d = 2s - 1:  d = 2 sin(pi/6 + x) - 1 with sin x = G/(2R).
Numeric 60-digit cross-check of the full construction at several (R, G).
"""
import sympy as sp
from mpmath import mp, mpf, sqrt, sin, cos, asin, pi as mpi, mpc, exp as mexp
th, g, R, m = sp.symbols('theta0 gamma R m', real=True)
I = sp.I
def e(x): return sp.exp(I * x)
for sig in (1, -1):
    u, up = e(m - g / 2), e(m + g / 2)
    s, tau = sp.sin(th), sp.cos(th)
    v = 0
    z = v - tau * u + sig * s * I * u
    vp = z + tau * up + sig * s * I * up
    lhs = sp.simplify(vp - v - 2 * sig * sp.sin(th + sig * g / 2) * I * e(m))
    assert sp.simplify(sp.expand(sp.expand_complex(lhs))) == 0
    # impose sig*g/2 = c = pi/6 - th
    c = sp.symbols('c', real=True)
    sub = {th: sp.pi / 6 - c, g: 2 * sig * c}
    G = -2 * R * sp.sin(c)
    w = v + R * u
    wp = vp + R * up
    diff_b = sp.simplify(sp.expand_complex((wp - w - sig * (1 - G) * I * e(m)).subs(sub)))
    assert sp.simplify(diff_b) == 0, diff_b
    def abs2(x):
        x = sp.expand_complex(x.subs(sub))
        return sp.simplify(sp.re(x) ** 2 + sp.im(x) ** 2)
    assert sp.simplify(abs2(vp - w) - (R ** 2 + 1 - G)) == 0
    assert sp.simplify(abs2(v - wp) - (R ** 2 + 1 - G)) == 0
    assert sp.simplify(abs2(vp - v) - 1) == 0
print('SG identities (a),(b),(c) verified symbolically for sig = +1, -1')

# numeric cross-check (60 digits), independent construction by root finding is in r7_C_explore1.py; here direct:
mp.dps = 60
for Rv in [10 ** 4, 10 ** 6]:
    Rm = mpf(Rv)
    for Gv in ['0.5', '1', '1.5', '2', '3.7', '-1.2']:
        Gm = mpf(Gv); cc = -asin(Gm / (2 * Rm)); t0 = mpi / 6 - cc
        tau, s = cos(t0), sin(t0)
        for sig in (1, -1):
            gam = 2 * sig * cc
            u, up = mpc(cos(-gam / 2), sin(-gam / 2)), mpc(cos(gam / 2), sin(gam / 2))
            z = -tau * u + sig * s * 1j * u
            vp = z + tau * up + sig * s * 1j * up
            w, wp = Rm * u, vp + Rm * up
            assert abs(abs(vp) - 1) < mpf(10) ** -50 and abs(abs(z) - 1) < mpf(10) ** -50 and abs(abs(z - vp) - 1) < mpf(10) ** -50
            assert abs(abs(vp - w) ** 2 - (Rm ** 2 + 1 - Gm)) < mpf(10) ** -40
            assert abs(abs(w - wp) - abs(1 - Gm)) < mpf(10) ** -40
            # exception identities: (z - v).u = -tau, (z - v').u' = -tau
            assert abs((z.conjugate() * u).real + tau) < mpf(10) ** -50
            assert abs(((z - vp).conjugate() * up).real + tau) < mpf(10) ** -50
        d = 2 * s - 1
        print('R=%d G=%s: R*d = %s ; |ww\'| = %s ; |v\'w|^2 - R^2 = %s' % (Rv, Gv, mp.nstr(Rm * d, 10), mp.nstr(abs(1 - Gm), 6), mp.nstr(1 - Gm, 6)))
# window translation: G = 1 <=> strip value (A3: tau = cos(pi/6 + alpha2/2) <=> sin(th0 - pi/6) = 1/(2R)); G >= 2 <=> R d >= ~sqrt3
Rm = mpf(10) ** 4
for Gv in [1, 2]:
    x = asin(mpf(Gv) / (2 * Rm)); print('G=%d at R=1e4: R d = %s' % (Gv, mp.nstr(Rm * (2 * sin(mpi / 6 + x) - 1), 12)))
print('r7_C_sg: all checks pass')
