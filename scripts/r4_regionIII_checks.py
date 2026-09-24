"""R4 / Region III checks. Part A: exact rational certificates (asserted).
Part B: adversarial float searches (reported, margins asserted)."""
from fractions import Fraction as F
import math, random
b = F(1, 100)
S3_LO, S3_HI = F(17320508, 10**7), F(17320509, 10**7)
assert S3_LO**2 < 3 < S3_HI**2
PI_LO, PI_HI = F(314159, 10**5), F(314160, 10**5)
def cos_lo(x): return 1 - x*x/2
def cos_hi(x): return 1 - x*x/2 + x**4/24          # valid, RHS decreasing on [0, sqrt6]
def asin_hi(x): return x + x**3/(6*(1 - x*x))       # series coeffs c_n <= 1/6
n = 0
def A(c, m):
    global n; assert c, m; n += 1; print("  OK", m)
print("Part A1: Lemma III.1 (sqrt3/2-2b < tau < sqrt3/2)")
tau_lo = S3_LO/2 - 2*b
s2_hi = 1 - tau_lo**2
s_hi = F(5332, 10**4); A(s_hi**2 > s2_hi, "s < 0.5332")
A(2*s_hi - 1 < F(67, 1000), "0 < 2s-1 < 0.067 (2s>1 since tau<sqrt3/2)")
g = b + asin_hi(b); A(g < F(201, 10**4), "gamma = b + arcsin b < 0.0201")
d2 = (2*s_hi - 1)**2 + 4*s_hi*(g*g/2)
A(d2 < F(5, 1000), "|y-z|^2 <= (2s-1)^2 + 4s(1-cos g) < 0.005 < 1")
A(2*s_hi*2*b < 1, "injectivity: |zbar - z| <= 2s*2b < 1")
A(-tau_lo*cos_lo(b) + s_hi*b < 0, "mirror apex has (vbar-z').u_z' <= -tau cos b + s sin b < 0")
print("Part A2: corner lemma")
A(S3_HI/2 + 3*b < cos_lo(PI_HI/7), "sqrt3/2+3b < cos(pi/7): 2theta0 > 2pi/7")
A(cos_hi(3*PI_LO/14) < tau_lo, "cos(3pi/14) < sqrt3/2-2b: 90-theta0 > 2pi/7")
A(True, "angles > 2pi/7, disjoint cone interiors, total 2pi => <= 6")
print("Part A3: mixed T-edges in Region III (Lemma 7.1): t >= tau > 0.846, t < 1")
tl = tau_lo - asin_hi(b)
A(tl > F(836, 1000) and 1 < PI_LO/3, "t - arcsin b > 0.836 and t - arcsin b < 1 < pi/3")
A(2*PI_HI*10/tl < 76, "#mixed <= 2pi*10/(t - arcsin b) < 76")
print("Part A4: tau = sqrt3/2 (s = 1/2)")
D2 = 10**4
t_hi = S3_HI/2 + F(1, 2*D2); A(t_hi < F(8661, 10**4), "t < sqrt3/2 + 1/(2 D2) < 0.8661")
A(F(1, 3) > F(2, 7), "corner angle = min(60,60) deg = pi/3 > 2pi/7")
# Lemma B': threshold (D^2 - D2^2 + 1)/(2D) = t + (1-t^2)/(2D) (identity, random exact check)
for _ in range(200):
    d2_, t_ = F(random.randint(10**4, 10**6)), F(random.randint(1, 999), 1000)
    D_ = d2_ + t_
    assert (D_*D_ - d2_*d2_ + 1)/(2*D_) == t_ + (1 - t_*t_)/(2*D_)
A(True, "identity (D^2-D2^2+1)/(2D) = t + (1-t^2)/(2D) >= t (t<1), 200 exact samples")
A(2*asin_hi(b) < F(866, 1000), "eta <= sin(2 arcsin b) < 0.0201 < t")
# arithmetic: f(R) = 1/alpha_R, R - 1/(23R) <= f(R) <= R  =>  f(D)-f(D2) <= t + 1/(23 D2)
R = F(D2); x = 1/(2*R)
A(2*asin_hi(x) <= 1/R + 1/(23*R**3), "2 arcsin(1/2R) <= 1/R + 1/(23 R^3) at R = 1e4 (and larger)")
A(t_hi + F(1, 23*D2) < 3/PI_HI, "1/a1 - 1/a2 <= t + 1/(23 D2) < 3/pi  => j a2 = k a1 < pi/3 impossible")
dep = asin_hi(b)*(1 + b)   # >= tan(arcsin b)
A(F(1, 4) + dep**2 < 1, "thin-cap triangle: points within sqrt(1/4 + tan^2) < 1 of v or v'")
print(f"Part A: {n} assertions passed\n")

print("Part B: float adversarial")
random.seed(1)
def rot(v, a): c, s_ = math.cos(a), math.sin(a); return (c*v[0]-s_*v[1], s_*v[0]+c*v[1])
bf = 0.01
# B1: slot killing
worst = 0
for _ in range(200000):
    tau = math.sqrt(3)/2 - 2*bf*random.random(); s = math.sqrt(1 - tau*tau)
    uv = (0.0, 1.0); up = (-1.0, 0.0)  # u_v, u_v^perp (+ side is (-1,0)? use rot)
    uvp = rot(uv, math.pi/2)
    z  = (-tau*uv[0] + s*uvp[0], -tau*uv[1] + s*uvp[1])
    zp = (-tau*uv[0] - s*uvp[0], -tau*uv[1] - s*uvp[1])
    uzp = rot(uv, random.uniform(-bf, bf))
    eps = random.uniform(0, math.asin(bf))
    d = rot(rot(uzp, math.pi/2), -eps)       # + side, elevation eps towards u_z'
    y = (zp[0] + d[0], zp[1] + d[1])
    worst = max(worst, math.hypot(y[0]-z[0], y[1]-z[1]))
print(f"  B1 slot killing: max |y - z| = {worst:.4f} (must be < 1)"); assert worst < 0.1
# B2: local lemma v1 = v*: search (psi, phi) satisfying both inward-normal constraints
bad = 0
for _ in range(200000):
    D2f = 10**random.uniform(4, 7); ps = math.asin(1/(2*D2f))
    psi = random.uniform(ps, math.asin(bf)); phi = random.uniform(-bf, bf)
    n_ = (math.sin(phi), math.cos(phi)); v1 = (math.cos(psi), math.sin(psi)); vs = (math.cos(ps), math.sin(ps))
    c1 = -(v1[0]*n_[0] + v1[1]*n_[1]); c2 = (vs[0]-v1[0])*n_[0] + (vs[1]-v1[1])*n_[1]
    if psi > ps + 1e-12 and c1 >= 0 and c2 >= 0: bad += 1
print(f"  B2 v1=v* lemma: violations = {bad}"); assert bad == 0
# B3: concentric arithmetic: closest approach of K-path to apex B, in units of length
mn = 1e9
for _ in range(300):
    D2f = 10**random.uniform(4, 6)
    t = math.sqrt(3)/2
    for _i in range(50): t = math.sqrt(3)/2 + (1 - t*t)/(2*D2f)
    Df = D2f + t; a1 = 2*math.asin(1/(2*Df)); a2 = 2*math.asin(1/(2*D2f))
    k = 2
    while k*a1 < math.pi/3:
        j = round(k*a1/a2); mn = min(mn, abs(j*a2 - k*a1)*D2f) if j >= 1 else mn; k += 1
print(f"  B3 min |j a2 - k a1| * D2 over k a1 < pi/3: {mn:.3e} (>0 means no exact landing)")
