"""R6 / Theorem N3: exact checks of every numerical constant (Fractions + rigorous Taylor bounds).

Angles are handled as rational intervals of radians: deg(a) = [a*PI_LO/180, a*PI_HI/180].
For 0 <= x <= 1.6 (alternating Taylor series with decreasing terms): sin x in [T7(x), T5(x)], cos x in [T6(x), T4(x)],
tan x <= sin_hi/cos_lo. All assertions are exact rational comparisons.
Sections follow scratchpad/R6/N3_draft.md and problems/132/angle_R6.md.
"""
from fractions import Fraction as F

PI_LO, PI_HI = F(333, 106), F(355, 113)


def deg(a):
    a = F(a)
    return (a * PI_LO / 180, a * PI_HI / 180)


def sin_lo(x): return x - x**3 / 6 + x**5 / 120 - x**7 / 5040
def sin_hi(x): return x - x**3 / 6 + x**5 / 120
def cos_lo(x): return 1 - x**2 / 2 + x**4 / 24 - x**6 / 720
def cos_hi(x): return 1 - x**2 / 2 + x**4 / 24


def Sin(a):  # rigorous enclosure of sin(a degrees), 0 <= a <= 90
    lo, hi = deg(a)
    return sin_lo(lo), sin_hi(hi)


def Cos(a):  # rigorous enclosure of cos(a degrees), 0 <= a <= 90
    lo, hi = deg(a)
    return cos_lo(hi), cos_hi(lo)


def Tan(a):
    return Sin(a)[0] / Cos(a)[1], Sin(a)[1] / Cos(a)[0]


ok = 0
def check(cond, msg):
    global ok
    assert cond, msg
    ok += 1


# ---------------- parameters
e0 = F(1, 50)                       # eps0 in radians
eps = sin_hi(e0) / cos_lo(e0)       # >= tan(eps0)
check(eps < F(2001, 100000), "eps = tan(1/50) < 0.02001")
E0DEG = F(115, 100)                 # eps0 = 1/50 rad < 1.15 deg
check(e0 * 180 < E0DEG * PI_LO, "eps0 < 1.15 deg")
Lam = 464
R = 10**4

# ---------------- Lemma T*: chord <= 4, Lambda = 464
x = deg(F(1, 2))[0]
check(4 / sin_lo(x) < Lam, "apex-side arc 4/sin(0.5 deg) < 464")
tan_half = Tan(F(1, 2))[1]          # tan(theta/2) for theta < 1 deg
w0 = 4 + 4 * tan_half
check(w0 < F(404, 100), "w0 < 4.04")
tphi = 2 * w0 / 1000 + 4 * tan_half
check(tphi < F(43, 1000), "tan phi* < 0.043")
cphi = 1 - tphi**2 / 2             # cos = 1/sqrt(1+tan^2) >= 1 - tan^2/2
lhs = 2 * cphi - w0 / R - 4 * tan_half
check(lhs > F(1962, 1000), "fatness: 2cos phi* - W/R > 1.962 > 1.94")
W = w0 + 2 * tan_half * 1000
check(W < F(215, 10), "W < 21.5")
PIq = PI_LO / 4
check((1000 + 1) * (W + 1) / PIq < 30000, "|X minus D| < 3e4 in the thin case")
M = (2 * (Lam + 1) + 1)**2
BT = 2 * PI_HI * M / e0
check(BT < 3 * 10**8, "Lemma BT count with Lambda=464 < 3e8")
print(f"[T*/BT] margin {float(lhs - F(194,100)):.4f}; W<{float(W):.2f}; BT<{float(BT):.3g}")

# ---------------- Lemma DN
L = Lam - 1
taus = (L * eps + 2) / (L - 3)
check(taus < F(245, 10000), "tau* = (463 eps + 2)/460 < 0.0245 (neighbour case; exact neighbour bound (463eps+1)/462 is smaller)")
check((L * eps + 3) / (L - 3) < F(267, 10000), "tau_3 (radius-3 DN) < 0.0267")
check((L * eps + 1) / (L - 1) < F(224, 10000), "tau* for neighbours < 0.0224")

# ---------------- Lemma P (pair tolerances)
# same kind at psi1<psi2: |cos1-cos2| = 2|sin((p1+p2)/2)| sin((p2-p1)/2) >= |sin((p1+p2)/2)|
# K: |dc| <= eps ; D: |dc| <= 2 tau*. Need |p1+p2| bounds: sin(half) <= eta  => half <= angle A if sin(A) >= eta.
check(Sin(F(115, 100))[0] >= eps, "K pair: |psi1+psi2|/2 <= 1.15 deg")
check(Sin(F(281, 100))[0] >= 2 * taus, "D pair: |psi1+psi2|/2 <= 2.81 deg")
# three of a kind: |psi3-psi1| <= 4*2.81 deg < 60 deg -> impossible
check(4 * F(281, 100) < 60, "no three of a kind")

# ---------------- Lemma M (m=4): K at +-30 and D at +-90 impossible
hK = Cos(30 + E0DEG)[0]             # h >= c_K >= cos(31.15)
cD_max = Sin(E0DEG)[1]              # D at |psi| in (90-e0, 90+e0): c <= sin(e0)
check(cD_max < hK - eps, "Lemma M: D at +-90 impossible when K at +-30")

# ---------------- Lemma H (deg 6, m 3): the three excluded cases (tolerance 2.81 deg for all slots)
T = F(281, 100)
# K pair at +-30, third D at ~ +-90
check(Sin(T)[1] < Cos(30 + T)[0] - eps, "H: K pair +-30 with D at +-90 impossible")
# D pair at +-60, K at ~0: h >= cos(T); D needs c >= h - eps but c <= cos(60-T)
check(Cos(60 - T)[1] < Cos(T)[0] - eps, "H: D pair +-60 with K at 0 impossible")
# D pair at +-90 (c <= sin T), K at +-30 (h >= cos(30+T))
check(Sin(T)[1] < Cos(30 + T)[0] - eps, "H: D pair +-90 with K at +-30 impossible")
# slots at +-120 / +-150 / 180 are never S: cos < -eps
check(-Cos(90 - 30 + T)[0] < -eps and True, "slot 120-T has c < -eps")   # cos(120 - T) = -sin(30 - T)
check(Sin(30 - T)[0] > eps, "slot 120 +- T: c <= -sin(30-T) < -eps")

# ---------------- Lemma Pin
Tf = 3
dc_fan_lo = Cos(30 + Tf)[0] - Sin(Tf)[1]           # D at 30+-3, K at 90+-3
dc_fan_hi = Cos(30 - Tf)[1] + Sin(Tf)[1]
s0 = sin_hi(e0); c0 = cos_lo(e0)
check(2 * s0 - dc_fan_lo * c0 < 0, "Pin: fan K-D pair is an exception")
tfan_lo = dc_fan_lo * c0 - 2 * s0 - F(2, 10**4)
tfan_hi = dc_fan_hi + 2 * s0 + F(2, 10**4)
check(tfan_lo > F(74, 100) and tfan_hi < F(99, 100), "Pin: fan t in [0.74, 0.99]")
dc_cap_lo = Cos(E0DEG)[0] - Cos(60 - E0DEG)[1]      # D at 0+-1.15, K at 60+-1.15
dc_cap_hi = 1 - Cos(60 + E0DEG)[0]
check(2 * s0 - dc_cap_lo * c0 < 0, "Pin: cap K-D pair is an exception")
tcap_lo = dc_cap_lo * c0 - 2 * s0 - F(2, 10**4)
tcap_hi = dc_cap_hi + 2 * s0 + F(2, 10**4)
check(tcap_lo > F(43, 100) and tcap_hi < F(57, 100), "Pin: cap t in [0.43, 0.57]")
check(tcap_hi < tfan_lo, "fans and caps cannot coexist")
print(f"[Pin] fan t in [{float(tfan_lo):.4f},{float(tfan_hi):.4f}], cap t in [{float(tcap_lo):.4f},{float(tcap_hi):.4f}]")

# ---------------- receivers
# fan receiver a at psi in [147,213]: a_z <= -cos 33; S-nbr q has q_z >= -2 eps; vertical component >= cos(37)
vert = Cos(33)[0] - 2 * eps
check(vert > Cos(38)[1], "fan receiver: S-neighbours within 38 deg of vertical")
check(2 * 38 < 120, "window 76 deg holds at most 2 points pairwise >= 60 deg")
# F5 fifth neighbour range (150 - e0, 210 + e0) inside [147, 213]
check(150 - E0DEG > 147, "F5 lower point inside the receiver range")
# cap receiver b: b_z <= -(cos 61.15) - cos(1.15); S-nbr needs vertical >= that - 2 eps > 1
vb = Cos(60 + E0DEG)[0] + Cos(E0DEG)[0] - 2 * eps
check(vb > 1, "cap receiver has no S-neighbour")

# ---------------- uniqueness
check(3 * E0DEG < 60, "cap owners < 60 deg apart")
# fan owners: rho <= 2 sin(33.6 deg) ; chord direction within [87, 94.15]; distance to slot occupant < 1
rho = 2 * Sin(F(336, 10))[1]
check(rho < F(1107, 1000), "|y y'| <= 1.107")
dist = (rho - 1) + 2 * Sin(F(36, 10))[1]
check(dist < 1, "y' coincides with y's +-90 slot occupant")
print(f"[uniq] |yy'| <= {float(rho):.4f}, |y' - q| <= {float(dist):.4f}")

# ---------------- LP: mu2 <= 1.5 s - 0.5 p, mu_delta <= s + p + 4 r
lam = F(2, 3)
cs = lam * F(3, 2) + (1 - lam) * 1
cp = lam * F(-1, 2) + (1 - lam) * 1
cr = (1 - lam) * 4
check(cs == F(4, 3) and cp == 0 and cr == F(4, 3), "LP certificate 4/3 (with Q term)")
# Region I (no Q): mu_delta <= s + 4r
check(lam * F(3, 2) + (1 - lam) == F(4, 3) and (1 - lam) * 4 == F(4, 3), "LP Region I 4/3")
# optimality of 4/3 for this LP: s = n*8/9... adversary s=8n/9? value min(1.5s, s+4r) at 1.5s = s + 4(n-s)
s_star = F(8, 9)
check(F(3, 2) * s_star == s_star + 4 * (1 - s_star) == F(4, 3), "LP tight at s = 8n/9 (Region I form)")
print(f"all {ok} exact assertions passed")
