"""Second referee (REFEREE2_A2.md): independent re-derivation of the numerical constants of
WRITEUP_A2.md, with exact rationals / one-sided rational bounds (no floats in any assertion),
plus a floating-point adversarial search (reported, not asserted) for the §7.2 proximity
lemmas (R1), (R2), (R2-sym).

Rational enclosures used:  1.7320508 < sqrt3 < 1.7320509,  3.1415926 < pi < 3.1415927,
x - x^3/6 <= sin x <= x,  1 - x^2/2 <= cos x <= 1 - x^2/2 + x^4/24,
x <= arcsin x <= x + x^3/(6(1-x^2)^{3/2}) <= x + x^3/3 for 0<=x<=1/2.
"""
from fractions import Fraction as F
import math, random

beta = F(1, 100)
S3lo, S3hi = F(17320508, 10**7), F(17320509, 10**7)
PIlo, PIhi = F(31415926, 10**7), F(31415927, 10**7)
ok = 0
def A(c, msg):
    global ok
    assert c, msg
    ok += 1
    print("  ok:", msg)

def asin_hi(x):   # x in [0,1/2]
    return x + x**3 / 3
def cos_lo(x): return 1 - x*x/2
def cos_hi(x): return 1 - x*x/2 + x**4/24
def sin_lo(x): return x - x**3/6

print("[LP] Lemma 4.1 / 4.2 certificates")
for k, target in ((F(1), F(18, 13)), (F(5, 4), F(36, 25)), (F(4, 3), F(54, 37))):
    lam = (6 - k) / (F(15, 2) - k)
    cs = lam * F(3, 2) + (1 - lam) * k           # coefficient of s
    cr = (1 - lam) * 6                           # coefficient of r
    A(cs == target and cr == target and 0 < lam < 1, f"k={k}: coeffs s,r = {cs},{cr} = {target}")
# Lemma 4.2: weights 4/5,1/5 on  (p + 3/2(s-p))  and  (s + 2p + 6r)
cs = F(4,5)*F(3,2) + F(1,5)*1; cp = F(4,5)*(1-F(3,2)) + F(1,5)*2; cr = F(1,5)*6
A((cs, cp, cr) == (F(7,5), 0, F(6,5)), "Lemma 4.2: 1.4 s + 0 p + 1.2 r")
A(max(F(18,13), F(36,25), F(7,5)) < F(54,37), "all other regimes below 54/37")
# is 54/37 optimal for this LP given e<=k s, mu2<=1.5 s, mu_delta<= e + 6 r?  min over (s,r)
# of max_n min(1.5s, ks+6r) at s+r=n: equality 1.5s = ks+6(n-s) -> s = 6n/(7.5-k): value 9n/(7.5-k)
A(F(3,2)*6/(F(15,2)-F(4,3)) == F(54,37), "LP is tight: adversary s = 36n/37 attains 54/37")

print("[II] Region II proximity constants (tau >= sqrt3/2 + 3beta)")
tau_lo = S3lo/2 + 3*beta
s2_hi = 1 - tau_lo**2                            # s^2 <= this
def s_lt(c):  # certify s < c  (c>0)
    return s2_hi < c*c
A(s_lt(F(4441, 10000)), f"s_max < 0.4441 (s^2 <= {float(s2_hi):.6f})")
asb = asin_hi(beta)
A(s_lt((1 - 2*beta)/2), "R1 at v:  2s < 1")
A(s_lt((1 - 2*beta)/2), "R1 at z:  2s + 2beta < 1")
A(s_lt((1 - 2*beta - asb)/2), "R2: 2s + 2beta + arcsin(beta) < 1")
A(s_lt((1 - 4*beta - asb)/2), "R2-sym: 2s + 4beta + arcsin(beta) < 1")
A(asb <= 2*beta and s_lt((1 - 6*beta)/2), "R2-sym as written: 2s + 6beta < 1")
A(cos_lo(beta/2) > S3hi/2 + 3*beta, "cos(beta/2) > sqrt3/2 + 3beta (rhombi only in top sub-regime)")
A(tau_lo - asb >= F(886, 1000), "Lemma 7.1: t - arcsin(beta) >= 0.886 (t >= tau when t<=1)")
A(2*PIhi*10/F(886,1000) < 71, "#mixed-T < 71")
A(1 - asb < PIlo/3, "Lemma 7.1 needs Theta < pi/3: t - arcsin b <= 1 - arcsin b < pi/3")
# pair ratio
A(max(F(4+m, 2+m) for m in range(4, 50)) == F(4,3) and max(F(3+m,2+m) for m in range(2,50)) == F(5,4),
  "pair ratios: max (4+m)/(2+m), m>=4 is 4/3; (3+m)/(2+m), m>=2 is 5/4")

print("[III] Region III corner lemma thresholds")
# need sqrt3/2+3beta < cos(pi/7)  and  sqrt3/2-2beta > cos(3pi/14)
A(S3hi/2 + 3*beta < cos_lo(PIhi/7), "tau < cos(pi/7) => 2 theta0 > 2pi/7")
A(S3lo/2 - 2*beta > cos_hi(3*PIlo/14), "tau > cos(3pi/14) => 90deg - theta0 > 2pi/7")
A(7 * (2*PIlo/7) >= 2*PIlo, "normal cones > 2pi/7 each => at most 6 corners")

print("[I] Region I window (cos(A+B) > 1/2 with sinA = sqrt3/2-2beta, sinB = beta)")
x = S3hi/2 - 2*beta; y = beta
# cos(A+B) = sqrt(1-x^2) sqrt(1-y^2) - x y > 1/2  <=>  sqrt((1-x^2)(1-y^2)) > 1/2 + xy
A((1 - x*x)*(1 - y*y) > (F(1,2) + x*y)**2, "arcsin(sqrt3/2-2b)+arcsin(b) < 60deg")
x = S3hi/2 - beta
A(x*x < F(3,4), "D-point window arcsin(sqrt3/2 - beta) < 60deg")

print("[5] Lens constants")
c = F(97, 100)
A(2/(1 - c) <= F(667, 10), "rho0^2 = 2/(1-cos phi0) <= 66.7 < 8.2^2")
# cos(phi0/2) = sqrt((1+c)/2); need 2/(sqrt((1+c)/2)-c) <= 89.0 : sqrt(0.985) > 0.97 + 2/89
A(((1 + c)/2) > (c + F(2, 90))**2, "KK lens hypothesis threshold <= 90 (write-up says 89.0; true value 89.01; harmless since R=Delta2>=1e4)")
A(12*PIhi*(4*F(82,10)+1)/beta < F(128000), "#KK-bad < 1.28e5")
A(12*PIhi*9/beta < 34000, "#DD-bad < 3.4e4")
A(24*PIhi/beta < 7600, "#(c1) < 7600")
L = 6/beta
A(48*PIhi*(2*L+1)/beta < F(182, 10)*10**6, "#(c2) < 1.82e7")
tot = 12*PIhi*(4*F(82,10)+1)/beta + 12*PIhi*9/beta + 24*PIhi/beta + 48*PIhi*(2*L+1)/beta + 71 + 12
A(tot < F(183, 10)*10**6, f"C_bad + 71 + 12 < 1.83e7  (= {float(tot):.4e})")
# (c2) step 3: cos alpha >= (1 + rho^2 - 1.94^2)/(2 rho) at rho = 1 - 1e-4
rho = 1 - F(1, 10**4)
ca = (1 + rho*rho - F(194,100)**2)/(2*rho)
A(ca > F(-8822, 10000), f"cos alpha >= {float(ca):.5f} > -0.8822")
# sin alpha >= sin(beta/2) on [beta/2, alpha_max]: need sin(alpha_max) >= sin(beta/2); sin^2 = 1 - cos^2
A(1 - ca*ca > (beta/2)**2, "sin(alpha_max) > sin(beta/2)")
A(-sin_lo(beta/2) + 2*(beta/8) < -beta/5, "-sin(b/2) + 2 sin(b/8) < -b/5")
D2 = F(10**4)
A((D2 - 1)**2 + F(2,5)*(D2 - 1)*L*beta > D2**2, "walk exits the disc at L = 600 (worst d0 = 1, Delta2=1e4)")
A(F(2)/10**4 <= beta/2, "2/Delta2 <= beta/2")
A((2*F(194,100)*10**4 + 1)**2 < F(151, 100)*10**9, "packing N0 < 1.51e9")

print("[8] Degenerate-regime constants, q = (Delta2/Delta)^2 < 1/1.94^2")
q = 1 / F(194, 100)**2
A(1 + 3*q < 2, "Step1: 1 + 3q < 2")
A(2 - S3hi > q, "Step1: (2 sin 15deg)^2 = 2 - sqrt3 > q")
A(q < F(1, 3), "Step2: Delta2^2 < Delta^2/3")
# lens D(y,D2) cap D(a,D2), |ya| = Delta: width 2D2 - Delta, height 2 sqrt(D2^2 - Delta^2/4)
# in units D2: width < 2 - 1.94 = 0.06 ; height^2 < 4 - 1.94^2
A(F(6,100)**2 + (4 - F(194,100)**2) < 1, "Step3: lens bounding-box diagonal^2 < 0.24 Delta2^2 < Delta2^2")
# chord <= Delta2 on circle radius Delta subtends 2 arcsin(Delta2/(2Delta)) < 120deg: (D2/2D)^2 < 3/4
A(q/4 < F(3,4), "Step3: A-chords subtend < 120deg at y")

print(f"\nALL {ok} RATIONAL ASSERTIONS PASSED")

# ---------------- adversarial (floating, informational) ----------------
print("\n[adversarial float search for R1/R2/R2-sym maxima; not used for any conclusion]")
b = 0.01; asb_f = math.asin(b)
def rot(a): return (math.cos(a), math.sin(a))
def o(a, sg, tau):
    s = math.sqrt(1 - tau*tau); u = rot(a); up = (-u[1], u[0])
    return (-tau*u[0] + sg*s*up[0], -tau*u[1] + sg*s*up[1])
def tstep(a, eps):  # right T-step at normal angle a, elevation eps
    u = rot(a); r = (u[1], -u[0])
    return (math.cos(eps)*r[0] + math.sin(eps)*u[0], math.cos(eps)*r[1] + math.sin(eps)*u[1])
def nrm(v): return math.hypot(*v)
random.seed(1)
best = {"R2": 0, "R2sym": 0, "R1z": 0}
tau = math.sqrt(3)/2 + 3*b
for it in range(400000):
    av0 = 0.0; az0 = random.uniform(-b, b); av1 = random.uniform(-b, b)
    e1 = random.uniform(0, asb_f); e2 = random.uniform(0, asb_f)
    s0, s1 = random.choice((-1, 1)), random.choice((-1, 1))
    E1, E2 = tstep(av0, e1), tstep(az0, e2)
    o0, o1 = o(av0, s0, tau), o(av1, s1, tau)
    zp_minus_z1 = (E1[0]-E2[0]+o1[0]-o0[0], E1[1]-E2[1]+o1[1]-o0[1])
    best["R2"] = max(best["R2"], nrm(zp_minus_z1))
    az1 = az0 + random.uniform(-b, b); avp = az1 + random.uniform(-b, b)
    if abs(avp - av0) <= 3*b:
        op = o(avp, s1, tau)
        vv = (E2[0]-E1[0]-(op[0]-o0[0]), E2[1]-E1[1]-(op[1]-o0[1]))
        best["R2sym"] = max(best["R2sym"], nrm(vv))
    a2 = az0 + random.uniform(-b, b)
    oo = o(a2, -s0, tau)
    best["R1z"] = max(best["R1z"], nrm((oo[0]-o0[0], oo[1]-o0[1])))
print({k: round(v, 4) for k, v in best.items()}, "(all must be < 1; proofs use 0.908/0.918/0.948)")
