"""Exact checks for the neighbour lemma (R-NEIGHBOUR route). Fractions / Decimal only (no sympy/mpmath here).
(1) single-arc thresholds c_K(h), c_D(h) and the identity c_D(0) = tau (rational identity, checked at random
    rationals; it is also a one-line expansion); monotonicity of c_D in h.
(2) LP values with the P1 term.
(3) constants of the thin-K lemma and multiplicity count, via rigorous rational bounds on sin/cos/tan.
(4) exact 'chord-midpoint fan' configuration (deg 6, m 4 locally) in 60-digit Decimal arithmetic."""
from fractions import Fraction as F
from decimal import Decimal as D, getcontext
import random

# (1)
def cK(R, h): return (R*R - (R-h)**2 - 1) / (2*(R-h))
def cD(R, h, t): return ((R+t)**2 - (R-h)**2 - 1) / (2*(R-h))
random.seed(1)
for _ in range(2000):
    R = F(random.randint(10**4, 10**6)); h = F(random.randint(0, 10**6), 10**6); t = F(random.randint(1, 2*10**6), 10**6)
    tau = t - (1 - t*t) / (2*R)
    assert cD(R, 0, t) == tau
    assert cK(R, h) == h + (h*h - 1) / (2*(R-h))
    assert cD(R, h, t) == h + t + ((h+t)**2 - 1) / (2*(R-h))
    assert cD(R, h + F(1, 10**7), t) > cD(R, h, t)
print("(1) c_D(0)=tau, closed forms and monotonicity: OK")

# (2)
def lp(c, P1=True):
    c = F(c); lam = (c - 1) / (c + F(1, 2))
    if P1 and lam < F(2, 3): lam = F(2, 3)
    if P1: assert -lam/2 + (1 - lam) <= 0
    return max(lam*F(3, 2) + 1 - lam, (1 - lam)*c)
for c2 in [6, 8, 9, 10, 12]:
    print(f"(2) 2c={c2}: with P1 term {lp(F(c2,2))}, Region-I form (no P1) {lp(F(c2,2), False)}")
assert lp(5) == F(15, 11) and lp(4) == F(4, 3) and lp(3) == F(4, 3) and lp(3, False) == F(9, 7) and lp(6) == F(18, 13)

# (3) rigorous rational bounds for x in (0, 0.1]: x - x^3/6 <= sin x <= x; 1 - x^2/2 <= cos x <= 1; tan x <= x + x^3/2
PI_LO, PI_HI = F(333, 106), F(355, 113)
x_hi = PI_HI / 360; x_lo = PI_LO / 360           # theta/2 = 0.5 degree
sin_lo = x_lo - x_lo**3 / 6; cos_lo = 1 - x_hi**2 / 2; tan_hi = x_hi + x_hi**3 / 2
apex_arc = 2 + 2 / sin_lo
assert apex_arc < 232
wy = 2 / cos_lo                                   # cross-section of the cone at y's level
tphi = 2 * wy / 400 + 4 * tan_hi                  # tan(phi*) upper bound when L >= 400
# cos(phi*) = 1/sqrt(1+tphi^2) >= 1 - tphi^2/2
cphi_lo = 1 - tphi**2 / 2
lhs = 2 * cphi_lo - 4 * tan_hi - wy / 10**4      # lower bound for (2R cos phi* - W)/R with R >= 1e4, L <= 2R
assert lhs > F(194, 100)
print(f"(3) apex arc <= {float(apex_arc):.2f} < 232; thin-cone margin {float(lhs - F(194,100)):.4f} > 0;"
      f" diam K < {float(400 + wy + 2*tan_hi*400):.1f}")
M = (2*233 + 2)**2
print(f"    multiplicity M <= {M}; exceptions (turning > eps0=1/50) <= {float(2*PI_HI*M*50):.3g}")
# Region II flat bound needs eps = tan(eps0) < 3*beta = 0.03 and window < 60 deg; eps0 = 0.02 -> tan <= 0.0201
e0 = F(1, 50); assert e0 + e0**3 / 2 < F(3, 100)

# (4) fan, 60 digits
getcontext().prec = 60
R2 = D(10)**4
sh = 1 / R2; ch = (1 - sh*sh).sqrt()               # half-angle of a chord of length 2
c2, s2 = ch*ch - sh*sh, 2*sh*ch                    # rotation by the full chord angle
def rot(p, c, s): return (p[0]*c - p[1]*s, p[0]*s + p[1]*c)
def sub(a, b): return (a[0]-b[0], a[1]-b[1])
def add(a, b): return (a[0]+b[0], a[1]+b[1])
def mul(a, k): return (a[0]*k, a[1]*k)
def nrm(a): return (a[0]*a[0] + a[1]*a[1]).sqrt()
r3 = D(3).sqrt() / 2
pts = {}
pm0 = (R2*ch, -R2*sh); pp0 = (R2*ch, R2*sh)
c, s = D(1), D(0)
for i in range(6):
    if i % 2:
        c, s = c*c2 - s*s2, c*s2 + s*c2; continue
    pm, pp = rot(pm0, c, s), rot(pp0, c, s)
    y = mul(add(pm, pp), D(1)/2); n = mul(y, 1/nrm(y)); e = mul(sub(pp, pm), 1/nrm(sub(pp, pm)))
    pts[('y', i)] = y; pts[('p', i)] = pm; pts[('p', i+1)] = pp
    pts[('z', i, 0)] = add(add(y, mul(e, D(-1)/2)), mul(n, r3)); pts[('z', i, 1)] = add(add(y, mul(e, D(1)/2)), mul(n, r3))
    pts[('a', i, 0)] = add(add(y, mul(e, D(-1)/2)), mul(n, -r3)); pts[('a', i, 1)] = add(add(y, mul(e, D(1)/2)), mul(n, -r3))
    c, s = c*c2 - s*s2, c*s2 + s*c2
tt = nrm(pts[('z', 0, 0)]) - R2
tau = tt - (1 - tt*tt) / (2*R2)
keys = list(pts); eps = D(10)**-40
mind = min(nrm(sub(pts[a], pts[b])) for i, a in enumerate(keys) for b in keys[i+1:])
assert mind > 1 - eps
assert all(abs(nrm(pts[k]) - R2 - tt) < eps for k in keys if k[0] == 'z')
assert all(abs(nrm(pts[k]) - R2) < eps for k in keys if k[0] == 'p')
for i in range(0, 6, 2):
    y = pts[('y', i)]
    nb = [k for k in keys if k != ('y', i) and abs(nrm(sub(pts[k], y)) - 1) < eps]
    assert len(nb) == 6 and nrm(y) < R2
print(f"(4) fan R=1e4 (blocks on every other chord): t={tt:.15f}, sqrt3/2 - tau = {r3 - tau:.3e} > 0; every y: deg 6, 2 nbrs on C(w,R), 2 at distance"
      f" exactly t outside D(w,R), 2 inside; min pairwise distance - 1 = {mind - 1:.2e}")
