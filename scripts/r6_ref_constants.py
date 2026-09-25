"""R6 referee (A_ref): exact-rational checks of every numeric constant in N3_draft.md.
Trig via Taylor partial sums with explicit Lagrange remainder (interval arithmetic in Fractions).
Every claim is an `assert`; the script prints a line per group."""
from fractions import Fraction as F
from math import factorial

PI = (F(314159265358, 10**11), F(314159265359, 10**11))  # pi in [lo, hi]


def deg(d):
    """interval (lo, hi) for d degrees in radians; d a Fraction >= 0."""
    d = F(d)
    return (d * PI[0] / 180, d * PI[1] / 180) if d >= 0 else (d * PI[1] / 180, d * PI[0] / 180)


def _series(x, start, N=24):
    s, term = F(0), None
    for k in range(start, N, 2):
        s += (-1) ** ((k - start) // 2) * x ** k / factorial(k)
    rem = abs(x) ** N / factorial(N)
    return s - rem, s + rem


def sin_iv(iv):
    """sin on an interval inside [-pi/2, pi/2] (monotone): returns (lo, hi)."""
    lo, hi = iv
    assert -F(157, 100) < lo <= hi < F(157, 100)
    return _series(lo, 1)[0], _series(hi, 1)[1]


def cos_iv(iv):
    """cos on an interval inside [0, pi] (decreasing)."""
    lo, hi = iv
    assert 0 <= lo <= hi < F(314, 100)
    return _series(hi, 0, 40)[0], _series(lo, 0, 40)[1]


def sind(d): return sin_iv(deg(d))
def cosd(d): return cos_iv(deg(d))


e0 = F(1, 50)                      # eps0 in radians
sin_e0 = _series(e0, 1); cos_e0 = _series(e0, 0)
tan_e0_hi = sin_e0[1] / cos_e0[0]
EPS = tan_e0_hi                    # rigorous upper bound on eps = tan(eps0)
e0deg_hi = e0 * 180 / PI[0]        # eps0 in degrees (upper)
assert e0deg_hi < F(11460, 10000)  # 1.1459...
print(f"[0] eps = tan(1/50) <= {float(EPS):.7f} < 0.02001; eps0 = {float(e0deg_hi):.5f} deg")
assert EPS < F(2001, 100000)

# ---------------- Lemma T*
s05 = sind(F(1, 2)); c05 = cosd(F(1, 2)); t05 = s05[1] / c05[0]
arc = 4 / s05[0]
assert arc < F(4584, 10) < 464
w0 = 4 + 4 * t05
assert w0 < F(404, 100)
w0_true = 4 / c05[0]                 # the correct section width 4/cos(theta/2) (smaller)
assert w0_true < w0
tphi = 2 * w0 / 1000 + 4 * t05
assert tphi < F(430, 10000)
cphi_lo = 1 - tphi ** 2 / 2          # 1/sqrt(1+x^2) >= 1 - x^2/2
lhs = 2 * cphi_lo - w0 / 10**4 - 4 * t05
assert lhs > F(1962, 1000) > F(194, 100)
W = w0 + 2000 * t05
assert W < F(215, 10)
pack = (1000 + 1) * (W + 1) * 4 / PI[0]
assert pack < 3 * 10**4
print(f"[T*] apex arc <= {float(arc):.2f} < 464; w0 <= {float(w0):.4f}; tan phi* <= {float(tphi):.5f};"
      f" margin lhs >= {float(lhs):.5f} (claimed >1.962); W <= {float(W):.3f}; |X\\D| <= {float(pack):.0f}")
# graph domain for Lambda=464
assert 464 * cos_e0[0] > 463
M_BT = (2 * 464 + 3) ** 2
print(f"[BT] 464 cos eps0 >= {float(464*cos_e0[0]):.3f} > 463; multiplicity (2L+3)^2={M_BT}; count < {float(2*PI[1]*M_BT/e0):.3g}")

# ---------------- Lemma DN
tau_star_2 = (463 * EPS + 2) / 460
tau_star_3 = (463 * EPS + 3) / 460
tau_star_1 = (463 * EPS + 1) / 460
assert tau_star_2 < F(245, 10000)
assert not (tau_star_3 < F(245, 10000))     # z_z <= 3 (not 2) is what B(y,3) gives
print(f"[DN] tau* (z_z<=2) = {float(tau_star_2):.5f} < 0.0245 OK; but z in B(y,3) only gives z_z <= 3: "
      f"(463eps+3)/460 = {float(tau_star_3):.5f} (> 0.0245); for NEIGHBOURS z_z <= 1: {float(tau_star_1):.5f}")

# ---------------- Lemma P
assert 2 * tau_star_2 < F(49, 1000)
assert F(49, 1000) < sind(F(281, 100))[0]   # arcsin(0.049) < 2.81 deg
assert EPS < sind(F(115, 100))[0]           # arcsin(eps) < 1.15 deg
assert 2 * tau_star_3 < sind(F(306, 100))[0]  # even with tau*_3: offset < 3.06 deg
print("[P] D-pair offset < 2.81 deg, K-pair offset < 1.15 deg (also: with z_z<=3, D offset < 3.06 deg)")

# ---------------- Lemma M
c = cosd(30 + e0deg_hi)[0]
assert c > F(85, 100)
assert sin_e0[1] < F(85, 100) - EPS        # D at +-90 would need c(D)<=sin eps0 >= h+t-eps
print(f"[M] cos(30+eps0) >= {float(c):.4f} > 0.85")

# ---------------- Lemma H (hexagon offset delta <= 2.81 deg)
dH = F(281, 100)
assert cosd(30 + dH)[0] > F(84, 100)
assert sind(dH)[1] < F(5, 100)
assert cosd(dH)[0] > F(998, 1000)
assert cosd(dH)[0] - EPS > F(978, 1000)
assert cosd(60 - dH)[1] < F(55, 100)
assert sind(dH)[1] + EPS < F(7, 100)
print("[H] all six case thresholds OK (0.84, 0.05, 0.998, 0.978, 0.55, 0.07)")

# ---------------- Lemma Pin
two_sin = 2 * sin_e0[1]; one_m_cos = 1 - cos_e0[0]
def pin(dc_lo, dc_hi):
    t_hi = dc_hi + two_sin + F(4, 2 * 10**4)
    t_lo = dc_lo * cos_e0[0] - two_sin - t_hi ** 2 / (2 * 10**4)
    return t_lo, t_hi
# fan: worst case over F6/F5 (offset eps0) and HF1/HF2 (offset <= 2.81): D at 30+-2.81, K at 90+-2.81, c(K) >= -eps
dc_lo = cosd(30 + dH)[0] - sind(dH)[1]
dc_hi = cosd(30 - dH)[1] + EPS
tl, th = pin(dc_lo, dc_hi)
assert dc_lo > F(78, 100) and tl > F(74, 100) and th < F(99, 100)
print(f"[Pin fan] dc in [{float(dc_lo):.4f},{float(dc_hi):.4f}] -> t in [{float(tl):.4f},{float(th):.4f}] subset [0.74,0.99]")
dK = F(115, 100)
dc_lo = cosd(dK)[0] - cosd(60 - dK)[1]
dc_hi = 1 - cosd(60 + dK)[0]
tl, th = pin(dc_lo, dc_hi)
print(f"[Pin cap] dc in [{float(dc_lo):.4f},{float(dc_hi):.4f}] -> t in [{float(tl):.4f},{float(th):.4f}] (claimed dc in [0.48,0.52], t in [0.44,0.56])")
assert tl > F(44, 100) and th < F(56, 100)
assert dc_lo > 2 * EPS  # exception forced
# (z-p).u_p < 0 needs dc cos eps0 > 2 sin eps0
assert F(48, 100) * cos_e0[0] > two_sin

# ---------------- Receivers
a_z_hi = -cosd(33)[0]                       # |psi_a - 180| <= 32.81 (hexagon) or <= 31.15 (F5)
assert a_z_hi < -F(838, 1000)
vert = -a_z_hi - 2 * EPS
assert vert > F(798, 1000)
# window half-angle arccos(vert) < 37.1 deg < 60 deg  (3 points need 120 deg)
assert cosd(F(371, 10))[1] < vert
print(f"[recv fan] a_z <= {float(a_z_hi):.4f}; vertical gap >= {float(vert):.4f} -> within 37.1 deg of vertical; window 74.2 < 120")
h_lo = cosd(60 + dK)[0]
assert h_lo > F(48, 100)
b_z_hi = -cosd(dK)[0] - h_lo
assert b_z_hi < -F(147, 100) and -b_z_hi - 2 * EPS > 1
print(f"[recv cap] h >= {float(h_lo):.4f}, b_z <= {float(b_z_hi):.4f}, gap {float(-b_z_hi-2*EPS):.4f} > 1 -> m_b = 0")

# ---------------- Fan owners: y' within <1 of y's +90 slot neighbour q
A_OWN = 33; A_OWN2 = 33 + e0deg_hi   # 34.15
alpha_hi = A_OWN2 - 60                # alpha in [-33, -25.85]
Lmax = 2 * sind((A_OWN + A_OWN2) / 2)[1]
beta = max(abs(F(-33 + 27, 2)), abs((alpha_hi + A_OWN2) / 2))  # |(alpha+alpha')/2|
bound = (Lmax - 1) + 2 * sind(beta / 2)[1] + 2 * sind(dH / 2)[1] + 2 * sind(e0deg_hi / 2)[1]
assert bound < F(1, 2)
print(f"[own] |y'-y| <= {float(Lmax):.4f}, direction within {float(beta):.2f} deg of 90; |y' - q| <= {float(bound):.4f} < 1")

# ---------------- LP
lam = F(2, 3)
cs = lam * F(3, 2) + (1 - lam) * 1; cp = -lam / 2 + (1 - lam); cr = (1 - lam) * 4
assert cs == F(4, 3) and cr == F(4, 3) and cp == 0
print("[LP] weights 2/3,1/3: s-coef 4/3, r-coef 4/3, Q-coef 0")
print("ALL ASSERTIONS PASSED")
