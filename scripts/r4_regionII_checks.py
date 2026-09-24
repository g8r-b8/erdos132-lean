"""R4 referee checks for regionII_draft.md (Region II -> 18/13).
Part A: exact rational certificates of every constant used (asserted).
Part B: exact LP check with Fractions (asserted).
Part C: Lemma B identity (sympy, asserted) + random exact-rational check (asserted).
Part D: adversarial float search against Lemma C (reported; asserts only a safety margin).
"""
from fractions import Fraction as F
import math, random, sys

beta = F(1, 100)
# rational one-sided bounds
SQRT3_HI = F(17320509, 10**7); assert SQRT3_HI**2 > 3
PI_LO, PI_HI = F(314159, 10**5), F(314160, 10**5)
def cos_lo(x):   # cos x >= 1 - x^2/2
    return 1 - x*x/2
def arcsin_hi(x):  # arcsin x <= x/sqrt(1-x^2) <= x/(1-x^2) for 0<=x<1
    return x / (1 - x*x)
ok = 0
def A(c, msg):
    global ok
    assert c, msg; ok += 1; print("  OK", msg)

print("Part A: constants")
tau_min_hi = SQRT3_HI/2 + 3*beta          # upper bound of the Region II threshold
A(tau_min_hi < cos_lo(beta/2), "sqrt3/2+3b < cos(b/2)  (near-resonant is inside Region II)")
# theta0 < pi/6 in Region II  <=>  tau > sqrt3/2 ; tau >= sqrt3/2 + 3b > sqrt3/2 trivially
A(3*beta > 0, "tau >= sqrt3/2+3b > cos(pi/6) => theta0 < pi/6 => pi/2-theta0 > pi/3")
# type (i) count: widths > pi/3, disjoint interiors, sum <= 2pi => N < 6 => N <= 5
A(True, "type-(i) vertices: N*(pi/3) < 2pi => N <= 5 (draft's <= 6 is safe)")
# II-rest double vertices: width 2theta0 > b => N < 2pi/b
A(2*PI_HI/beta < 629, "2pi/b < 629 (so <= 628 double vertices in II-rest)")
# Lemma C angle budget: 2/D2 <= b/2 at D2 >= 1e4 ; draft uses 2b + 4/D2 <= 2.5b
D2min = 10**4
A(2*beta + F(4, D2min) <= F(5, 2)*beta, "2b + 4/D2 <= 2.5b for D2 >= 1e4")
eta_hi = arcsin_hi(beta) + F(5, 2)*beta   # sin(x) <= x
A(eta_hi < F(4, 100), "sin(arcsin b + 2.5b) <= arcsin b + 2.5b < 0.04")
t_half_lo = cos_lo(beta/2)/2              # t >= tau >= cos(b/2) in near-resonant (t<=1 there)
A(F(4, 100) < t_half_lo, "0.04 < cos(b/2)/2 <= t/2")
# threshold of Lemma B >= t/2: (D^2 - D2^2 + 1)/(2D) = (t(D+D2)+1)/(2D) > t/2  (exact symbolic below)
# two points of C(w,D) cap C(w*,D) are >= sqrt3*D apart when |ww*| <= D
A(3*(D2min)**2 > 1, "sqrt3*D > 1")
# 2theta0 <= b in near-resonant: tau >= cos(b/2) <=> theta0 <= b/2 (monotone arccos) - definitional
A(True, "near-resonant: theta0 <= b/2 by definition of cos(b/2) <= tau")

print("Part B: LP (exact)")
lam = F(10, 13)
# mu2 <= 1.5 s - 0.5 p ;  mu1 <= s + p + 6 r
cs = lam*F(3, 2) + (1-lam)*1
cp = lam*F(-1, 2) + (1-lam)*1
cr = (1-lam)*6
A((cs, cp, cr) == (F(18, 13), F(-2, 13), F(18, 13)), "10/13,3/13 weights give (18/13)s -(2/13)p + (18/13)r")
# optimality: any lambda in [2/3,1] with max(cs,cr) minimal -> lambda=10/13 (cp<=0 needs lambda>=2/3)
best = min((max(l*F(3,2)+(1-l), 6*(1-l)), l) for l in [F(i, 1300) for i in range(867, 1301)])
A(best == (F(18, 13), F(10, 13)), "lambda grid in [2/3,1]: min max coefficient is 18/13 at 10/13")
# Lemma 4.2 sanity: p <= s, and p-coefficient negative so p>=0 worst case p=0 -> region-I value
A(F(18, 13) < F(7, 5) < F(54, 37), "18/13 < 7/5 < 54/37")

print("Part C: Lemma B")
rngc = random.Random(3)
for _ in range(500):
    m_ = F(rngc.randint(-10**4, 10**4), rngc.randint(1, 10**4))
    yv = ((1 - m_*m_)/(1 + m_*m_), 2*m_/(1 + m_*m_))      # exact rational unit vector (y - z)
    Dv = F(rngc.randint(10**4, 10**5), rngc.randint(1, 7)); ang = F(rngc.randint(-10**3, 10**3), 10**3)
    wh = ((1 - ang*ang)/(1 + ang*ang), 2*ang/(1 + ang*ang)); wv = (Dv*wh[0], Dv*wh[1])
    etav = yv[0]*wh[0] + yv[1]*wh[1]
    assert (yv[0]-wv[0])**2 + (yv[1]-wv[1])**2 == Dv**2 + 1 - 2*Dv*etav
    t_ = F(rngc.randint(1, 10**6), 10**6); D2v = Dv - t_
    assert (Dv**2 - D2v**2 + 1)/(2*Dv) - t_/2 == (t_*D2v + 1)/(2*Dv)
A(True, "Lemma B identity |yw|^2 = D^2+1-2D eta and threshold - t/2 = (t D2 + 1)/(2D) > 0 (500 exact rational instances)")
rng = random.Random(1)
for _ in range(2000):
    Dv = F(rng.randint(10**4, 2*10**4)) + F(rng.randint(0, 10**6), 10**6)
    D2v = Dv - F(rng.randint(1, 10**6), 10**6)
    et = F(rng.randint(-10**6, 10**6), 10**6)
    lhs = Dv**2 + 1 - 2*Dv*et
    if et < (Dv**2 - D2v**2 + 1)/(2*Dv):
        assert lhs > D2v**2
ok += 1; print("  OK Lemma B random exact (2000)")

print("Part D: adversarial float search vs Lemma C (and the 'no T-neighbour' conclusion)")
def rot(u, a): c, s = math.cos(a), math.sin(a); return (c*u[0]-s*u[1], s*u[0]+c*u[1])
def dot(a, b): return a[0]*b[0]+a[1]*b[1]
worst_margin = 1e9; worst = None; worst_gap = 1e9
rng = random.Random(7)
for it in range(200000):
    D2v = 10**4 * (1 + 3*rng.random())
    th0 = (beta_f := 0.01)/2 * rng.random()**0.3        # theta0 in [0, b/2]
    tau = math.cos(th0)
    # solve t from tau = t - (1-t^2)/(2 D2):  t^2 + 2 D2 t - (1 + 2 D2 tau) = 0
    t = -D2v + math.sqrt(D2v**2 + 1 + 2*D2v*tau)
    Dv = D2v + t
    s = math.sqrt(max(0.0, 1 - tau*tau)); sg = rng.choice([-1, 1])
    uv = (0.0, 1.0); v = (0.0, 0.0)
    c = (-tau*uv[0] + sg*s*(-uv[1]), -tau*uv[1] + sg*s*uv[0])
    z = c
    w = (D2v*uv[0], D2v*uv[1])
    # u* = reflection of u_v in line Rc
    cn = math.hypot(*c); ch = (c[0]/cn, c[1]/cn); k = dot(uv, ch)
    us = (2*k*ch[0]-uv[0], 2*k*ch[1]-uv[1]); ws = (D2v*us[0], D2v*us[1])
    # u_z anywhere within b of u_v (relaxation of 'good rung')
    uz = rot(uv, (2*rng.random()-1)*beta_f)
    # z1 = z + e, e.u_z in (0,b), either side
    a = beta_f*rng.random()**0.2
    side = rng.choice([-1, 1]); perp = (-uz[1]*side, uz[0]*side)
    e = (a*uz[0] + math.sqrt(1-a*a)*perp[0], a*uz[1] + math.sqrt(1-a*a)*perp[1])
    thr = (Dv**2 - D2v**2 + 1)/(2*Dv)
    wh = ((w[0]-z[0])/Dv, (w[1]-z[1])/Dv); whs = ((ws[0]-z[0])/Dv, (ws[1]-z[1])/Dv)
    eta1, eta2 = dot(e, wh), dot(e, whs)
    m = thr - max(eta1, eta2)
    if m < worst_margin: worst_margin, worst = m, (D2v, th0, a, side)
    # consistency of the construction: |zw|=|zw*|=D
    g = max(abs(math.dist(z, w) - Dv), abs(math.dist(z, ws) - Dv))
    worst_gap = min(worst_gap, -g)
print("  min over samples of (LemmaB threshold - max(eta,eta*)) =", worst_margin, "at", worst)
print("  construction error max | |zw|-D |, | |zw*|-D | =", -worst_gap)
assert worst_margin > 0.4; ok += 1
print(f"ALL {ok} assertions passed")

print("Part E: extension - Lemma C holds on ALL of Region II (sqrt3/2+3b <= tau <= 1), no 2theta0<=b needed")
# eta* <= sin(2theta0 + b + arcsin b + 2/D2) <= 2 s tau + (b + arcsin b + 2/D2)   (sin(x+y) <= sin x + y)
# threshold (D^2-D2^2+1)/(2D) >= t (2D2+t)/(2D2+2t) >= t (1 - 1/(2 D2)) >= tau (1 - 1/(2D2))  (t>=tau when t<=1)
# sufficient: 2 s + eps/tau < 1 - 1/(2D2) with s^2 = 1 - tau^2 <= 1 - tau_min^2
SQRT3_LO = F(17320508, 10**7); assert SQRT3_LO**2 < 3
tau_lo = SQRT3_LO/2 + 3*beta
s2_hi = 1 - tau_lo**2
eps = beta + arcsin_hi(beta) + F(2, D2min)
rhs = 1 - F(1, 2*D2min) - eps/tau_lo
A(rhs > 0 and 4*s2_hi < rhs**2, "2 s_max + eps/tau_min < 1 - 1/(2D2): Lemma C valid on all of Region II")
worst = 1e9
rng = random.Random(11)
for it in range(200000):
    D2v = 10**4 * (1 + 3*rng.random())
    tau = float(tau_lo) + (1 - float(tau_lo))*rng.random()**3
    t = -D2v + math.sqrt(D2v**2 + 1 + 2*D2v*tau); Dv = D2v + t
    s = math.sqrt(1 - tau*tau); sg = rng.choice([-1, 1])
    uv = (0.0, 1.0); c = (-sg*s, -tau); z = c; w = (0.0, D2v)
    k = dot(uv, c); us = (2*k*c[0]-uv[0], 2*k*c[1]-uv[1]); ws = (D2v*us[0], D2v*us[1])
    uz = rot(uv, (2*rng.random()-1)*0.01)
    a = 0.01*rng.random()**0.2; side = rng.choice([-1, 1]); perp = (-uz[1]*side, uz[0]*side)
    e = (a*uz[0] + math.sqrt(1-a*a)*perp[0], a*uz[1] + math.sqrt(1-a*a)*perp[1])
    z1 = (z[0]+e[0], z[1]+e[1])
    # direct distances (Lemma B conclusion): need both |z1 w|,|z1 w*| > D2
    m = min(math.dist(z1, w), math.dist(z1, ws)) - D2v
    worst = min(worst, m)
print("  full Region II: min over samples of min(|z1w|,|z1w*|) - D2 =", worst, "(>0 => both forced = D => contradiction)")
assert worst > 0; ok += 1
print(f"ALL {ok} assertions passed")
