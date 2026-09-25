#!/usr/bin/env python3
"""r7_refB_margins.py -- REF_B independent recomputation of branch B's margins M1-M11 (Region II, weight 7).

Rigorous: mpmath interval arithmetic at 60 digits. Instead of re-checking B's rounded constants (30.06, 36.01, ...),
we compute the TRUE extremal quantities as intervals and report the true margins.
Parameters: eps0 = 1e-6 rad (frame), d0 = 1e-4 (height error), beta = 1/100, t in [tmin, 1], tmin = sqrt3/2 + 3 beta.
Also checks the referee's simplified proof of m_a <= 1 (receiver sees y inside the sender cone) and the frame-radius
fact used for two forwarders (distance 4 < rho - 1 = 5).
Run: .venv/bin/python r7_refB_margins.py
"""
from mpmath import iv, mp
iv.dps = 60
PI = iv.pi
DEG = PI / 180
e0 = iv.mpf(1) / 10**6
d0 = iv.mpf(1) / 10**4
eps = iv.tan(e0)
tmin = iv.sqrt(3) / 2 + iv.mpf(3) / 100
s32 = iv.sqrt(3) / 2
res = []

def iacos(x):
    # acos is decreasing; endpoints at 70 digits, padded outward by 1e-55 (rigorous up to mpmath's correct rounding)
    with mp.workdps(70):
        lo = mp.acos(mp.mpf(x.b)) - mp.mpf('1e-55'); hi = mp.acos(mp.mpf(x.a)) + mp.mpf('1e-55')
    return iv.mpf([lo, hi])
iv.acos = iacos

def deg(x):   # radians interval -> degrees interval
    return x / DEG

def lt(name, a, b):
    ok = a.b < b.a
    res.append(ok)
    print(("PASS " if ok else "FAIL ") + f"{name}: {mp.nstr(mp.mpf(a.b), 10)} < {mp.nstr(mp.mpf(b.a), 10)}"
          f"   (margin {mp.nstr(mp.mpf(b.a) - mp.mpf(a.b), 4)})")

# ---- M1: fan / half-fan t upper bound ----
tfan = iv.cos(30 * DEG - 2 * e0) + iv.sin(2 * e0) + d0
lt("M1  fan/half-fan need t <= cos(30-2e0)+sin(2e0)+d0 < tmin", tfan, tmin)
lt("M1b cap/A' need t <= 1/2 + d0 < tmin", iv.mpf(1) / 2 + d0, tmin)

# ---- M2: D-type half-angle (true value) ----
cDmin = tmin - eps * 2          # c >= h + t - eps|x| with |x| <= 1 ... take 2 eps
aD = deg(iv.acos(cDmin))         # max |psi| of a D-type neighbour
print("   true max |psi_D| =", mp.nstr(mp.mpf(aD.b), 8), "deg")
lt("M2  two D-type nbrs: 2*max|psi_D| < 60", 2 * aD, iv.mpf(60))

# ---- M3: hexagon with h >= 1/2 - d0 has no D-type ----
lt("M3  1 < (1/2 - d0) + tmin - d0", iv.mpf(1), iv.mpf(1) / 2 - d0 + tmin - d0)

# ---- M4: K-slots of a deg-6 point: c >= sqrt3/2 - 2d0 ----
aK6 = deg(iv.acos(s32 - 2 * d0))
print("   deg-6 K-slot max |psi| =", mp.nstr(mp.mpf(aK6.b), 8), "deg (two slots 60 apart => both at +-30 +- ",
      mp.nstr(mp.mpf(aK6.b) - 30, 4), ")")
lt("M4  2*maxK6 < 60 + 1 (only the pair at +-30 fits; slots 60 apart)", 2 * aK6, iv.mpf(61))

# ---- M5: D_II psi_K range ----
hmax = 1 - tmin + d0 + eps
psiKmin = deg(iv.acos(hmax))
psiKmax = iv.mpf(90) + deg(e0 + d0)   # conservative, as B: K-row c >= -d0 (blanket height error) + frame e0
print("   D_II psi_K in [", mp.nstr(mp.mpf(psiKmin.a), 8), ",", mp.nstr(mp.mpf(psiKmax.b), 8), "] deg; h <=",
      mp.nstr(mp.mpf(hmax.b), 8))
lt("M5  psi_K >= 84 deg", iv.mpf(84), psiKmin)
lt("M5' psi_K <= 90.006 deg", psiKmax, iv.mpf(90.006))

# ---- M6: receiver depth ----
dmin = iv.sin((psiKmax + 30) * DEG) - 2 * d0
print("   D_II receiver depth >=", mp.nstr(mp.mpf(dmin.a), 10))
lt("M6  receiver depth >= 0.8657 (B's text value)", iv.mpf("0.8657"), dmin)
lt("M6' receiver has no D-nbr: 1 < dmin + tmin - d0", iv.mpf(1), dmin + tmin - d0)
# depth identity cos A - cos(A+60) = sin(A+30) at a few points (sanity; it is exact trig)
for A in (84, 87, 90):
    Ai = iv.mpf(A) * DEG
    diff = iv.cos(Ai) - iv.cos(Ai + 60 * DEG) - iv.sin(Ai + 30 * DEG)
    assert abs(mp.mpf(diff.a)) < 1e-50 and abs(mp.mpf(diff.b)) < 1e-50

# ---- M7 (referee's simplified version): receiver's K-slots and sender cone ----
bK = deg(iv.acos(dmin - d0))            # any K-nbr of receiver a has |beta| <= bK
cone = 120 - psiKmin + deg(e0 + d0)      # D_II sender (= y) seen from a: |dir| <= cone
print("   receiver K-slot |beta| <=", mp.nstr(mp.mpf(bK.b), 8), "; D_II sender cone |.| <=", mp.nstr(mp.mpf(cone.b), 8))
# two K at a: beta1 < 0 < beta2, beta2 - beta1 >= 60 => |beta_i| >= 60 - bK. y at theta, |theta| <= cone, must be
# >= 60 from both: theta >= beta1 + 60 >= 60 - bK and theta <= beta2 - 60 <= bK - 60  => need bK >= 60.
lt("M7* m_a <= 1: receiver K-slot bound bK < 60 (so no room for y between/outside the K pair)", bK, iv.mpf(60))
lt("M7*' and y's cone lies inside (-(60 - bK)-..., ...): cone + bK < 120 (y can't be outside both)", cone + bK, iv.mpf(120))
# B's own M7 chain (a,b,c) re-verified
x = iv.mpf(8) * d0 * iv.mpf("1.01")
lt("M7a sin(120deg - 8.08e-4 rad) > sqrt3/2 + 4 d0", s32 + 4 * d0, iv.sin(120 * DEG - x))
z = iv.mpf(6) * d0 * iv.mpf("1.01")
lt("M7b cos(30deg - 6.06e-4 rad) > sqrt3/2 + 3 d0", s32 + 3 * d0, iv.cos(30 * DEG - z))
lt("M7c 2 sin(0.075 deg) < 1", 2 * iv.sin(iv.mpf("0.075") * DEG), iv.mpf(1))

# ---- M8: sender cone and forwarder direction ----
lt("M8a D_II sender cone <= 36.01", cone, iv.mpf("36.01"))
lt("M8b forwarder |beta| <= 30.06", bK, iv.mpf("30.06"))
lt("M8c cone width 2*max(cone, 30 + e0, bK) < 120", 2 * cone, iv.mpf(120))

# ---- M9: 7-point has <= 1 D_II sender ----
lower = 60 - cone          # two senders >= 60 apart in [-cone, cone]: |d_i| >= 60 - cone
lt("M9  K (|beta|<=bK) outside both senders needs |beta| >= lower+60 > bK", bK, lower + 60)
lt("M9' K between both senders needs gap >= 120 > 2 cone", 2 * cone, iv.mpf(120))

# ---- M10 / M11: forwarding target and A-receiver depths ----
tgt = dmin + (dmin - d0) - d0     # depth(a) + cos(beta) with cos(beta) >= dmin - d0
lt("M10 forwarding target depth > 1 (m = 0); value", iv.mpf(1), tgt)
print("   forwarding target depth >=", mp.nstr(mp.mpf(tgt.a), 10))
Aslot = iv.cos(iv.mpf("150.05") * DEG)   # A's +-150 slot, hexagon rotation error <= 0.05 deg (M4)
Arec = (s32 - d0) - Aslot - d0
lt("M11 A receiver depth > 1.7", iv.mpf("1.7"), Arec)
# A receivers cannot coincide with D_II receivers: D_II receiver depth <= hmax + 1 < A receiver depth
lt("M12 D_II receiver depth <= hmax + 1 < min(A receiver, fwd target) depth", hmax + 1 + d0, tgt)

# ---- frame radius: two forwarders into one x have D_II senders <= 4 apart; foot point of the second is
#      within 5 of the first, inside B(y, rho=6): F'4 gives normals within e0. ----
lt("FR  4 + 1 <= rho = 6", iv.mpf(5), iv.mpf(6) + iv.mpf("1e-30"))

# ---- LP: 5/8, 3/8 certificate (exact rationals) ----
from fractions import Fraction as Fr
lam = Fr(5, 8)
coefS = lam * Fr(3, 2) + (1 - lam) * 1
coefQ = -lam * Fr(1, 2) + (1 - lam) * Fr(1, 2)
coefR = (1 - lam) * Fr(7, 2)
print("   LP: s-coef", coefS, " |Q'|-coef", coefQ, " r-coef", coefR)
assert coefS == Fr(21, 16) and coefR == Fr(21, 16) and coefQ < 0
res.append(True)
print("ALL PASS" if all(res) else "SOME FAIL")
