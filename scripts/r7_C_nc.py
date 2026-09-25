"""R7/C: Lemma NC (no two consecutive distinct-centre singleton gaps), exact identity + rigorous bound.

Chain: gaps (v0,v1 | z0) and (v1,v2 | z1), all rungs w.r.t. the fixed normals u_j = u_{v_j}, G >= 2 (Lemma SG).
By SG(a) each step is v_{j+1} - v_j = sig i e(m_j) and u_{j+1} = u_j rotated by gamma = 2 sig c (c = pi/6 - th0),
so the v_j lie on a circle of radius rho = R/G about c0 := v0 + rho u0, with u_j pointing to c0 and rotating by
psi := |gamma| = 2 asin(G/(2R)) per step.  Then  w_j = c0 + b u_j (b = R - rho > 0 as G > 1),
z_j = c0 - (rho + tau) u_j + sig s iu_j,  and |z0 - w_k|^2 = Delta^2 - 2 b r (cos(psi/2) - cos((k - 1/2) psi)),
r = sqrt((rho+tau)^2 + s^2)  [zero at k = 0 (L0) and k = 1 (tan(psi/2) = s/(rho+tau), proved in the report)].
Hence |z0 w2|^2 = Delta^2 - 4 b r sin(psi) sin(psi/2), and 0 < 4 b r sin psi sin(psi/2) <= 2(G-1)(1+2G/R) < Delta^2 - R^2
on all of Region III: |z0 w2| in (R, Delta), impossible since z0, w2 in X.
Checks: (1) 60-digit direct construction (rung by rung) vs formula; (2) sympy: tan relation; (3) rational bound.
"""
from mpmath import mp, mpf, sqrt, sin, cos, asin, acos, pi as mpi, mpc
import sympy as sp
from fractions import Fraction as F
mp.dps = 60
def chain(Rm, Gm, n=5, sig=1):
    c = -asin(Gm / (2 * Rm)); th0 = mpi / 6 - c; tau, s = cos(th0), sin(th0)
    Dl = sqrt(Rm * Rm + 2 * Rm * tau + 1)
    gam = 2 * sig * c
    V, Z, W = [], [], []
    u = mpc(0, 1); v = mpc(0, 0)
    for j in range(n):
        V.append(v); W.append(v + Rm * u)
        z = v - tau * u + sig * s * 1j * u; Z.append(z)
        u2 = u * mpc(cos(gam), sin(gam))
        v = z + tau * u2 + sig * s * 1j * u2
        assert abs(abs(v - V[-1]) - 1) < mpf(10) ** -45
        u = u2
    return V, Z, W, Dl, tau, s
maxratio = 0
for Rv in [10 ** 4, 10 ** 5, 10 ** 7]:
    Rm = mpf(Rv)
    for Gv in ['2', '2.5', '4', '5.8', '50', str(int(0.078 * Rv))]:
        Gm = mpf(Gv)
        for sig in (1, -1):
            V, Z, W, Dl, tau, s = chain(Rm, Gm, 5, sig)
            psi = 2 * asin(Gm / (2 * Rm)); rho = Rm / Gm; b = Rm - rho; r = sqrt((rho + tau) ** 2 + s * s)
            # zero at k = 0, 1
            assert abs(abs(Z[0] - W[0]) - Dl) < mpf(10) ** -40 and abs(abs(Z[0] - W[1]) - Dl) < mpf(10) ** -40
            for k in range(2, 5):
                f = Dl ** 2 - 2 * b * r * (cos(psi / 2) - cos((k - mpf(1) / 2) * psi))
                assert abs(abs(Z[0] - W[k]) ** 2 - f) < mpf(10) ** -30, (Rv, Gv, k)
            gap = 4 * b * r * sin(psi) * sin(psi / 2)
            assert abs(Dl ** 2 - abs(Z[0] - W[2]) ** 2 - gap) < mpf(10) ** -30
            assert 0 < gap <= 2 * (Gm - 1) * (1 + 2 * Gm / Rm) < Dl ** 2 - Rm ** 2
            # symmetric statement for the other end: |z1 - w_{-1}| handled by reflection; check |z1 w0| too
            assert Rm < abs(Z[1] - W[0]) < Dl
            maxratio = max(maxratio, gap / (2 * (Gm - 1)))
    print('R=%d: |z0 w2| in (R, Delta) for all tested G; Delta^2-|z0w2|^2 = 4br sin(psi) sin(psi/2) verified' % Rv)
print('max of gap/(2(G-1)) = %s (<= 1+2G/R)' % mp.nstr(maxratio, 8))

# (2) symbolic: tan(psi/2) = s/(rho + tau) with rho = R/G, sin(psi/2) = G/(2R), th0 = pi/6 + psi/2
x, Rs = sp.symbols('x R', positive=True)   # x = psi/2
G = 2 * Rs * sp.sin(x)
s_ = sp.sin(sp.pi / 6 + x); tau_ = sp.cos(sp.pi / 6 + x)
expr = sp.simplify(sp.expand_trig((Rs + tau_ * G) - 2 * Rs * s_ * sp.cos(x)))
assert sp.simplify(expr) == 0
print('(2) R + tau G = 2 R s cos(psi/2), i.e. tan(psi/2) = s/(rho+tau): symbolic OK')

# (3) rigorous range of G on Region III with d > 0: th0 <= arccos(sqrt3/2 - 2 beta), beta = 1/100.
mp.dps = 30
th0max = acos(sqrt(3) / 2 - mpf('0.02'))
Gmax_over_R = 2 * sin(th0max - mpi / 6)
print('(3) Region III: G/R <= %s ; need 2(G-1)(1+2G/R) < 2Rt + t^2 with t >= 0.846:' % mp.nstr(Gmax_over_R, 6))
q = F(79, 1000)                              # G/R <= 0.079 (rounded up)
assert Gmax_over_R < mpf(79) / 1000
# 2(G-1)(1+2G/R) < 2 G (1 + 2q) <= 2 q R (1 + 2q) and 2 q (1+2q) < 2 * 0.846
assert 2 * q * (1 + 2 * q) < 2 * F(846, 1000)
print('    2(G-1)(1+2G/R) < 2qR(1+2q) = %s R < 1.692 R <= 2Rt: OK (exact rational)' % float(2 * q * (1 + 2 * q)))
print('r7_C_nc: all checks pass')
