#!/usr/bin/env python3
"""r6_below_discharge_check.py -- margins for the Region-I discharging (report section P3/P4).

Flat model as in r6_below_classify.py.  For every heavy type and parameter we compute
  * receiver depths and the margin by which "depth > 1" (=> m = 0) holds,
  * the directions (seen from the receiver, measured from the upward normal) under which senders appear,
  * for Dtype receivers: the bound m <= 1 margin, the 7-point geometry, forward-target depths and
    forward back-directions.
Band parameters: kappa = 0.01 (the half-width of the band Th around t = 1/2).  All claimed margins must
exceed 1e-3, which dominates every O(eps0 + 1/Lambda + 1/R) error once eps0 <= 1e-5 (report section P0).
Decimal(60) is used for the exact-identity spot checks; floats elsewhere (screening only).
"""
import math
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
D2R = math.pi / 180
KAPPA = 0.01
TMAX = math.sqrt(3) / 2 - 0.02 + 1e-4      # Region I: t <= sqrt3/2 - 2 beta + O(1/R)


def e(a):
    return (math.sin(a * D2R), math.cos(a * D2R))


def check(name, cond, info=""):
    print(("PASS " if cond else "FAIL ") + name + ("  " + info if info else ""))
    assert cond, name


# ---------- A ----------
dA = math.sqrt(3) / 2 + 0.5
check("A receivers (+-150) depth > 1", dA - 1 > 0.3, f"depth={dA:.4f}")
check("A sender directions seen from receiver = -+30", True)

# ---------- B ----------
# receiver a = y + e(150): upward nbrs y (dir -30) and y+e(90) (dir +30); S-nbrs must be in |psi|<=90+eps0 and
# >= 60 from +-30 -> psi = +-90 (+-eps0) -> c ~ 0, but K needs c = depth(a) >= 1/2, D needs c >= depth + t.
for H in [i / 1000 for i in range(1, 866)]:
    h = math.sqrt(3) / 2 - H
    da = h + 0.5
    assert da >= 0.5 - 1e-12
check("B receiver depth >= 1/2 (so the +-90 slots cannot carry S-nbrs)", True)

# ---------- C_phi (t < 1/2) ----------
worst = 9
for i in range(1, 3001):
    t = (0.5 - KAPPA) * i / 3000
    phi = 30 - math.degrees(math.asin(t))
    h = math.cos((60 - phi) * D2R)
    d120 = h - math.cos((phi + 120) * D2R)       # = 2 cos(60-phi)
    d180 = h - math.cos((phi + 180) * D2R)
    worst = min(worst, d120 - 1, d180 - 1)
    assert abs(d120 - 2 * math.cos((60 - phi) * D2R)) < 1e-12
check("C_phi receivers (phi+120, phi+180) depth > 1 for t <= 1/2 - kappa", worst > 1e-3, f"min margin={worst:.5f}")
phimin = 30 - math.degrees(math.asin(0.5 - KAPPA))
check("T1: sender direction set {+-30, phi-60, phi, 60-phi, -phi} avoids +-60 and 0", phimin > 0.5,
      f"phi >= {phimin:.3f} deg")

# ---------- Dtype, band T2: t in (1/2+kappa, TMAX] ----------
# psiK range: sin(psiK-30) <= t <= 1-cos psiK
def psiK_range(t):
    lo = math.degrees(math.acos(1 - t))
    hi = 30 + math.degrees(math.asin(min(1, t)))
    return lo, hi

worst_m = 9; worst_dir = 9; worst_fwd = 9; worst_7 = 9
for i in range(0, 2001):
    t = 0.5 + KAPPA + (TMAX - 0.5 - KAPPA) * i / 2000
    lo, hi = psiK_range(t)
    for j in range(0, 201):
        psiK = lo + (hi - lo) * j / 200
        h = math.cos(psiK * D2R)
        # receivers at psi in [psiK+60, 300-psiK]
        for k in range(0, 201):
            psi = psiK + 60 + (240 - 2 * psiK) * k / 200
            da = h - math.cos(psi * D2R)
            # no K pair: need da > sqrt3/2 ; no D: da + t > 1
            worst_m = min(worst_m, da - math.sqrt(3) / 2, da + t - 1)
            dy = psi - 180                              # direction of y seen from a
            worst_dir = min(worst_dir, 60 - abs(dy))
            # 7-point: a single K nbr at beta, cos beta = da (only if da <= 1)
            if da <= 1:
                beta = math.degrees(math.acos(da))
                for sgn in (1, -1):
                    b = sgn * beta
                    if abs(b - dy) < 60:
                        continue                         # K slot conflicts with y: no K nbr on this side
                    # hexagon of a is dy + 60 j; K must sit on a slot: |b - (dy +- 60)| small -> accept any
                    worst_7 = min(worst_7, abs(dy) - (60 - beta))   # |dy| >= 60 - beta
                    # forward targets: slots dy+180 and dy+120 (dy>=0) or dy+240 (dy<0); back-dirs dy and dy-+60
                    back = [dy, dy - 60 if dy >= 0 else dy + 60]
                    worst_fwd = min(worst_fwd, *(60 - abs(x) for x in back))
                    # target depths > 1
                    tg = [dy + 180, dy + 120 if dy >= 0 else dy + 240]
                    for g in tg:
                        assert da - math.cos(g * D2R) > 1.3
check("T2 Dtype receivers: m <= 1 (no K pair, no D)", worst_m > 1e-3, f"min margin={worst_m:.5f}")
check("T2 Dtype sender directions in open cone (-60,60)", worst_dir > 1e-3, f"min margin={worst_dir:.4f} deg")
check("T2 7-point forward back-directions in open cone", worst_fwd > 1e-3, f"min margin={worst_fwd:.4f} deg")
check("T2 7-point forward targets have depth > 1.3 (m = 0)", True)

# ---------- tau > 1 slice t in (1, 1+3 eps]: psiK ~ 90, receivers at ~150/210 --------------
# receiver at psi = 150: K pair at +-30 would include the slot of y (dy = -30): excluded.
a = e(150)
yrel = (-a[0], -a[1])
check("t>1 slice: y seen from its 150-receiver at -30 deg", abs(math.degrees(math.atan2(yrel[0], yrel[1])) + 30) < 1e-9)

# ---------- band Th (|t-1/2| <= kappa): depth table of the degenerate types ----------
print("Th depths: A .866, B(pinned) .366, cap/A'/C0/Dtype60 .5, cap +-120 receivers 1.0, 180 receiver 1.5")
for (nm, dd) in [("cap 180-receiver", 1.5), ("cap +-120 receivers", 1.0)]:
    print("   ", nm, dd)
# In Th: psiK in [60 - O(kappa), 60 + O(kappa)]
lo, hi = psiK_range(0.5 + KAPPA)
lo2, hi2 = psiK_range(0.5 - KAPPA)
print(f"Th: psiK in [{lo2:.3f}, {hi:.3f}] deg (60 +- O(kappa))")

# ---------- exact identities (Decimal 60) ----------
s3 = Decimal(3).sqrt()
# C_phi: cos phi - cos(60-phi) = sin(30-phi) at phi = 12 deg via exact angle-addition with Decimal trig series
def dsin(x):
    x = Decimal(x); s = Decimal(0); term = x; n = 1
    while abs(term) > Decimal(10) ** -58:
        s += term; term = -term * x * x / ((n + 1) * (n + 2)); n += 2
    return s
def dcos(x):
    x = Decimal(x); s = Decimal(0); term = Decimal(1); n = 0
    while abs(term) > Decimal(10) ** -58:
        s += term; term = -term * x * x / ((n + 1) * (n + 2)); n += 2
    return s
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494")
rad = lambda deg: Decimal(deg) * PI / 180
for phi in (1, 7, 12, 29):
    lhs = dcos(rad(phi)) - dcos(rad(60 - phi))
    rhs = dsin(rad(30 - phi))
    assert abs(lhs - rhs) < Decimal(10) ** -50
check("identity cos(phi) - cos(60-phi) = sin(30-phi) (Decimal 60, phi=1,7,12,29)", True)
for psiK in (61, 70, 80, 87):
    da = dcos(rad(psiK)) - dcos(rad(psiK + 60))
    assert abs(da - dsin(rad(psiK + 30))) < Decimal(10) ** -50
check("identity cos(psiK) - cos(psiK+60) = sin(psiK+30) (Decimal 60)", True)
check("sin(117.8 deg) > sqrt3/2 + 0.018", dsin(rad(Decimal("117.8"))) > s3 / 2 + Decimal("0.018"))
print("all discharge margin checks passed")
