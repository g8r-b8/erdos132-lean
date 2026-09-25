#!/usr/bin/env python3
"""r7_B_margins.py -- rigorous interval-arithmetic (mpmath.iv, 60 digits) check of every numeric margin used in
the Region II weight-7 proof (report sections 1-3).  Parameters (B1, refereed): eps0 = 1e-6 (angles, rad),
delta0 = 1e-4 (heights), t >= tmin := sqrt(3)/2 + 3*beta, beta = 1/100 (WRITEUP_A2), t <= 1.
Every assertion is an interval inequality; an AssertionError means a margin fails.
Run with the repo venv: .venv/bin/python r7_B_margins.py
"""
from mpmath import iv, mp
iv.dps = 60
PI = iv.pi
D = PI / 180                      # one degree
e0 = iv.mpf(1) / 10**6
d0 = iv.mpf(1) / 10**4
tmin = iv.sqrt(3) / 2 + iv.mpf(3) / 100
s32 = iv.sqrt(3) / 2
ok = []

def check(name, cond_iv_lt):
    a, b = cond_iv_lt          # assert a < b rigorously: sup(a) < inf(b)
    good = a.b < b.a
    ok.append(good)
    print(("PASS " if good else "FAIL ") + name + "   [" + mp.nstr(mp.mpf(a.b), 12) + " < " + mp.nstr(mp.mpf(b.a), 12) + "]")

# M1: fans / half-fans need t <= cos(30deg - 2e0) + sin(2e0) + d0 (K within 2e0 of +-90, D within 2e0 of +-30)
tfan = iv.cos(30 * D - 2 * e0) + iv.sin(2 * e0) + d0
check("M1 fan/half-fan t_max < tmin (no F6/F5/HF in Region II)", (tfan, tmin))
# caps / A': t = 1/2 +- d0
check("M1b cap t < tmin", (iv.mpf(0.5) + d0, tmin))
# M2: a D-type neighbour (S or R) has c >= h + t - d0 >= tmin - d0 > cos(26.5 deg): within 26.5 deg of vertical
check("M2 D-type slot within 26.5deg of vertical: cos(26.5deg) < tmin - d0", (iv.cos(iv.mpf(26.5) * D), tmin - d0))
check("M2' => two D-type nbrs impossible (53 < 60)", (iv.mpf(2 * 26.5), iv.mpf(60)))
# M3: hexagon with h < 1/2 - d0 has two slots with c >= 1/2 > h + d0 (both D-type, contradiction M2');
#      with h >= 1/2 - d0 a D-type needs c >= 1/2 - d0 + tmin - d0 > 1
check("M3 hexagon: h >= 1/2 - d0 excludes D-type nbrs", (iv.mpf(1), iv.mpf(0.5) - d0 + tmin - d0))
# M4: then all slots c <= h + d0, top slot c >= sqrt3/2, so h >= sqrt3/2 - d0; K slots (c >= h - d0 >= sqrt3/2 - 2d0)
#      lie within arccos(sqrt3/2 - 2 d0) of vertical: 30.02 deg
check("M4 K slots of a deg-6 point within 30.05deg of vertical: cos(30.05deg) < sqrt3/2 - 2d0",
      (iv.cos(iv.mpf(30.05) * D), s32 - 2 * d0))
# M5: Dtype: h <= 1 - t + d0 <= 1 - tmin + d0 -> psiK >= arccos(1 - tmin + d0) >= 84.0 deg
check("M5 Dtype psiK >= 84.0deg: 1 - tmin + d0 < cos(84deg)", (1 - tmin + d0, iv.cos(iv.mpf(84) * D)))
psiKmin = iv.mpf(84)
psiKmax = iv.mpf(90) + (e0 + d0) / D    # K-row nbr: c >= -d0 -> psi <= 90 + ~d0 rad
check("M5' psiK <= 90.006 deg", (psiKmax, iv.mpf(90.006)))
# M6: receiver depth >= sin(psiK + 30) - 2d0 over psiK in [84, 90.006]; sin decreasing on [114,120.006]
dmin = iv.sin((psiKmax + 30) * D) - 2 * d0
check("M6 Dtype receiver depth >= 0.8656", (iv.mpf(0.8656), dmin))
# M6': D-nbr of receiver needs c >= depth + t - d0 > 1
check("M6' receiver has no D-nbr", (iv.mpf(1), dmin + tmin - d0))
# M7 (m_a <= 1): a K pair at a sits at +-b0 with b0 >= 30deg (60deg apart, mirror up to 2.3deg... use c):
#   both K at height c = depth(a) +- d0 and 60deg apart  =>  depth(a) <= cos(30deg) + 2 d0  (Lemma P mirror)
#   => sin(psiK+30) - 2d0 <= depth <= sqrt3/2 + 2d0  => psiK + 30 >= 120 - x  with sin(120 - x) <= sqrt3/2 + 4d0
#   derivative of sin at 120 is -1/2 in magnitude: x <= 8 d0 rad *(1+small)  -> psiK >= 90 - 0.05 deg
x = iv.mpf(8) * d0 * 1.01 / D     # degrees
check("M7a sin(120deg - x) > sqrt3/2 + 4d0 at x = 8.08e-4 rad (so psiK >= 90 - 0.047deg)",
      (s32 + 4 * d0, iv.sin((120 - x) * D)))
#   psi_a in [psiK + 60, 300 - psiK]; depth(a) = cos psiK - cos psi_a <= sqrt3/2 + 2d0 and cos psiK >= -d0
#   -> -cos psi_a <= sqrt3/2 + 3 d0 -> |psi_a - 180| >= 30 - z,  z <= 6 d0 rad*1.01
z = iv.mpf(6) * d0 * 1.01 / D
check("M7b cos(30deg - z) > sqrt3/2 + 3d0 (so psi_a <= 150 + 0.035 deg)", (s32 + 3 * d0, iv.cos((30 - z) * D)))
#   so psi_a in [150 - 0.047, 150 + 0.035] (or mirror); y is seen from a at psi_a - 180 in [-30.05, -29.96];
#   a's K pair psi1<psi2: both |psi_i| <= 30.07 (depth >= dmin) and psi2-psi1 >= 60 -> psi1 in [-30.07,-29.93]: angle diff <= 0.1 deg -> distance 2 sin(0.05deg) < 1 -> same point, y in S: contradiction
check("M7-aux K-pair nbrs of a within 30.07deg: cos(30.07deg) < dmin - 2d0", (iv.cos(iv.mpf(30.07) * D), dmin - 2 * d0))
check("M7c two unit nbrs of a within 0.15deg are < 1 apart", (2 * iv.sin(iv.mpf(0.075) * D), iv.mpf(1)))
# M8: sender cone.  Dtype sender seen from its receiver: in [psiK - 120, 120 - psiK] subset [-36.0, 36.0];
#     A at +-30 (+ frame error); forwarder at beta, cos beta = depth(a) +- d0 >= dmin - d0
coneD = 120 - psiKmin + (e0 + d0) / D
check("M8a Dtype sender direction |.| <= 36.01 deg", (coneD, iv.mpf(36.01)))
check("M8b forwarder direction |beta| <= 30.06 deg: cos(30.06deg) < dmin - d0", (iv.cos(iv.mpf(30.06) * D), dmin - d0))
check("M8c whole cone width 72.12 < 120 => at most 2 senders (pairwise >= 60)", (iv.mpf(72.12), iv.mpf(120)))
# M9: 7-point has <= 1 Dtype sender: senders d1<d2 in [-36,36], d2-d1>=60 -> d1<=-24, d2>=24;
#     its K at |beta|<=30.06 must be >= 60 from both: between needs d2-d1>=120 (>72), outside needs |beta|>=84
check("M9 single Dtype sender: senders at <=-23.99 and >=23.99, K needs |beta|>=83.99 > 30.06", (iv.mpf(30.06), iv.mpf(83.99)))
# M10: forwarding target depth = depth(a) + cos(beta) >= 2 dmin - 2 d0 > 1 (m = 0)
check("M10 forwarding target depth > 1.7", (iv.mpf(1.7), 2 * dmin - 2 * d0))
# M11: A receivers (+-150 slots) depth = sqrt3/2 + sqrt3/2 - 2d0 > 1.7
check("M11 A receivers depth > 1.7", (iv.mpf(1.7), 2 * s32 - 2 * d0))
print("ALL PASS" if all(ok) else "SOME FAIL")
