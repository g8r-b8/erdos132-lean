"""Rigorous checks for every numeric inequality used in WRITEUP_A2.md.

No bare floats are used in any decision. All quantities are exact Fractions or
closed rational intervals [lo, hi] that provably contain the true real value:
  * sqrt       -- integer isqrt, floor/ceil, so the enclosure is rigorous;
  * pi         -- Machin's formula, alternating arctan series with explicit tails;
  * cos, sin   -- alternating Taylor series (|x| <= 2), with the next-term tail bound;
  * arcsin(x)  -- enclosed by x <= arcsin x <= x / sqrt(1 - x^2)   (0 <= x < 1).
Every check is an `assert` on an interval comparison (all of [lo, hi] must be on
the required side). Floats appear only in the printed "~" values.

Section labels (C1, C2, ...) match the "[check Ck]" tags in WRITEUP_A2.md.
Run:  python3 scripts/writeup_a2_checks.py
"""
from fractions import Fraction as F
from math import isqrt

DIG = 40                     # decimal digits of working precision for sqrt
SC = 10 ** DIG


class I:
    """Closed interval [lo, hi] of rationals."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = F(lo); hi = lo if hi is None else F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi

    @staticmethod
    def c(x):
        return x if isinstance(x, I) else I(x)

    def __add__(a, b): b = I.c(b); return I(a.lo + b.lo, a.hi + b.hi)
    __radd__ = __add__
    def __neg__(a): return I(-a.hi, -a.lo)
    def __sub__(a, b): return a + (-I.c(b))
    def __rsub__(a, b): return I.c(b) - a

    def __mul__(a, b):
        b = I.c(b); p = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
        return I(min(p), max(p))
    __rmul__ = __mul__

    def __truediv__(a, b):
        b = I.c(b); assert b.lo > 0 or b.hi < 0, "division by interval containing 0"
        return a * I(1 / b.hi, 1 / b.lo) if b.lo > 0 else a * I(1 / b.hi, 1 / b.lo)

    def __rtruediv__(a, b): return I.c(b) / a

    def __lt__(a, b): b = I.c(b); return a.hi < b.lo      # certainly less
    def __gt__(a, b): b = I.c(b); return a.lo > b.hi      # certainly greater
    def __le__(a, b): b = I.c(b); return a.hi <= b.lo
    def __ge__(a, b): b = I.c(b); return a.lo >= b.hi

    def f(self): return float((self.lo + self.hi) / 2)
    def __repr__(self): return f"~{self.f():.10g} [w={float(self.hi - self.lo):.1e}]"


def _sqrt_lo(q):  # rational lower bound of sqrt(q), q >= 0
    q = F(q); return F(isqrt(q.numerator * SC * SC // q.denominator), SC)


def _sqrt_hi(q):
    q = F(q); n = -((-q.numerator * SC * SC) // q.denominator)   # ceil
    r = isqrt(n); r = r if r * r == n else r + 1
    return F(r, SC)


def sqrt(x):
    x = I.c(x); assert x.lo >= 0
    return I(_sqrt_lo(x.lo), _sqrt_hi(x.hi))


def _atan_series(q, terms=60):  # q rational in (0, 1/2]; alternating series
    s = F(0); p = q; k = 0
    for k in range(terms):
        s += (-1) ** k * p / (2 * k + 1); p *= q * q
    tail = p / (2 * terms + 1)      # |next term| bounds the error (alternating, decreasing)
    return I(s - tail, s + tail)


PI = 16 * _atan_series(F(1, 5)) - 4 * _atan_series(F(1, 239))


def _cos_pt(q, terms=40):  # q rational, |q| <= 2: alternating decreasing after first term
    s = F(0); t = F(1)
    for k in range(terms):
        s += t; t = -t * q * q / ((2 * k + 1) * (2 * k + 2))
    return I(s - abs(t), s + abs(t))


def _sin_pt(q, terms=40):
    s = F(0); t = F(q)
    for k in range(terms):
        s += t; t = -t * q * q / ((2 * k + 2) * (2 * k + 3))
    return I(s - abs(t), s + abs(t))


def cos(x):  # x interval inside [0, 2] (cos decreasing there)
    x = I.c(x); assert 0 <= x.lo and x.hi <= 2
    return I(_cos_pt(x.hi).lo, _cos_pt(x.lo).hi)


def sin(x):  # x interval inside [0, 1.5] (sin increasing there)
    x = I.c(x); assert 0 <= x.lo and x.hi <= F(3, 2)
    return I(_sin_pt(x.lo).lo, _sin_pt(x.hi).hi)


def asin(x):  # 0 <= x < 1 :  x <= asin x <= x/sqrt(1-x^2)
    x = I.c(x); assert 0 <= x.lo and x.hi < 1
    return I(x.lo, (x.hi / sqrt(1 - x.hi * x.hi)).hi)


N_OK = 0


def check(name, cond, info=""):
    global N_OK
    assert cond, "FAILED: " + name
    N_OK += 1
    print(f"  [ok] {name}" + (f"   {info}" if info else ""))


# ---------------------------------------------------------------- constants
beta = F(1, 100)
R3 = sqrt(3) / 2                      # sqrt(3)/2
tauI = R3 - 2 * beta                  # Region I upper end
tauII = R3 + 3 * beta                 # Region II lower end
LAM = F(194, 100)                     # nondegeneracy constant 1.94
D2MIN = F(10) ** 4                    # Delta_2 >= 10^4 in the nondegenerate regime
check("pi enclosure sane", I(F(314159, 100000)) < PI and PI < I(F(314160, 100000)), repr(PI))

print("\n== C1  Lemma 1.1 / LP certificates (exact rationals)")
for k, target in [(F(1), F(18, 13)), (F(5, 4), F(36, 25)), (F(4, 3), F(54, 37)), (F(7, 5), F(90, 61))]:
    lam = (6 - k) / (F(15, 2) - k)                 # weight on the Vesztergombi bound
    cs = lam * F(3, 2) + (1 - lam) * k             # coefficient of s
    cr = (1 - lam) * 6                             # coefficient of r
    check(f"k={k}: lam={lam}, coeff(s)=coeff(r)={cs}={target}", cs == cr == target == 9 / (F(15, 2) - k))
check("54/37 < 3/2 and 18/13, 36/25, 7/5 <= 54/37",
      F(54, 37) < F(3, 2) and max(F(18, 13), F(36, 25), F(7, 5)) <= F(54, 37))
# Region III: 0.8*(1.5s-0.5p) + 0.2*(s+2p+6r) = 1.4 s + 1.2 r (p cancels)
a, b = F(4, 5), F(1, 5)
check("Region III multipliers: p cancels, coeff(s)=7/5, coeff(r)=6/5 <= 7/5",
      a * F(-1, 2) + b * 2 == 0 and a * F(3, 2) + b == F(7, 5) and b * 6 == F(6, 5))
# Lemma 1.1 lambda <= 1 so the additive constant is multiplied by (1-lam) <= 1
check("1 - lam in [0,1] for k=4/3", 0 <= 1 - (6 - F(4, 3)) / (F(15, 2) - F(4, 3)) <= 1)

print("\n== C2  rung identity (exact polynomial identity, checked on a rational grid)")
bad = 0
for tq in [F(i, 53) for i in range(-10, 120)]:
    for d2 in [F(3), F(101, 7), F(10 ** 4), F(123457, 11)]:
        D = d2 + tq
        if (1 + d2 ** 2 - D ** 2) / (2 * d2) != -(tq - (1 - tq ** 2) / (2 * d2)):
            bad += 1
check("(1 + D2^2 - D^2)/(2 D2) == -tau for D = D2 + t (degree-2 identity in t, 520 points)", bad == 0)
# tau vs t: for 0<=t<=1, tau<=t; tau>1 iff t>1 (tau-t = (t^2-1)/(2 D2))
check("tau - t = (t^2-1)/(2 D2) (exact)", all(
    (tq - (1 - tq ** 2) / (2 * d2)) - tq == (tq ** 2 - 1) / (2 * d2)
    for tq in [F(i, 7) for i in range(15)] for d2 in [F(5), F(10 ** 4)]))

print("\n== C3  small-angle facts used with Delta_2 >= 10^4")
check("2/Delta_2 <= beta/2", F(2) / D2MIN <= beta / 2)
x = I(F(1) / (D2MIN))                                   # 1/Delta <= 1/Delta_2
check("arcsin(1/Delta) <= arcsin(1/Delta_2) <= 2/Delta_2", asin(x) <= I(F(2) / D2MIN))
check("2 arcsin(1/(2 Delta_2)) < beta (same-centre edges are good)", 2 * asin(I(1 / (2 * D2MIN))) < I(beta))
check("arcsin(beta) <= beta/sqrt(1-beta^2) < 1.0001 beta", asin(I(beta)) < I(beta * F(10001, 10000)))

print("\n== C4  Region I (tau <= sqrt3/2 - 2 beta): one good neighbour per side")
# S\D: angular window width arcsin(tauI) + arcsin(beta) < pi/3  <=>  cos(A+B) > 1/2
A_s, B_s = tauI, I(beta)
cosAB = sqrt(1 - A_s * A_s) * sqrt(1 - B_s * B_s) - A_s * B_s
check("cos(arcsin(sqrt3/2-2b) + arcsin b) > 1/2", cosAB > I(F(1, 2)), f"cos={cosAB}  (~58.35 deg)")
check("D-side: tau+beta <= sqrt3/2 - beta < sqrt3/2 so arcsin(tau+beta) < 60 deg", tauI + beta < R3)
check("tau <= 0 sub-case: |tau| <= 1/(2 D2) and arcsin(1/(2D2)) + arcsin b < pi/3 (sin-sum < sqrt3/2)",
      I(1 / (2 * D2MIN)) + I(beta) * F(10001, 10000) < R3)

print("\n== C5  Region II (tau >= sqrt3/2 + 3 beta), s = sqrt(1 - tau^2)")
s2max = 1 - tauII * tauII
smax = sqrt(s2max)
check("tauII > 2 beta (good-edge dichotomy)", tauII > I(2 * beta))
check("s <= smax, smax ~ 0.444", smax < I(F(445, 1000)), repr(smax))
asb = asin(I(beta))
check("(R1-v) 2s < 1", 2 * smax < I(1))
check("(R1-z) |v - v'| <= 2s + 2 beta < 1", 2 * smax + 2 * beta < I(1), repr(2 * smax + 2 * beta))
check("(R2)   |z' - z1| <= 2s + 2 beta + arcsin beta < 1",
      2 * smax + 2 * beta + asb < I(1), repr(2 * smax + 2 * beta + asb))
check("(R2-sym) |v' - v1| <= 2s + 4 beta + arcsin beta <= 2s + 6 beta < 1",
      2 * smax + 4 * beta + asb <= 2 * smax + 6 * beta and 2 * smax + 6 * beta < I(1),
      repr(2 * smax + 6 * beta))
check("notes' bound 2s + 4.5 beta < 1 (also fine)", 2 * smax + F(9, 2) * beta < I(1))
cb2 = cos(I(beta / 2))
check("near-resonant threshold cos(beta/2) > sqrt3/2 + 3 beta (so it lies inside Region II)", cb2 > tauII)
check("(R3) rhombus => theta0 <= beta/2; theta0 <= pi/2 since tau >= 0", tauII > I(0))
# mixed T-edges (Region II only): t >= tau >= tauII; turning >= t - arcsin(beta)
turn = tauII - asb
check("5.1: t - arcsin(beta) >= 0.886 and < pi/3", turn > I(F(886, 1000)) and I(F(886, 1000)) < PI / 3, repr(turn))
check("5.1: #mixed-T <= 2 pi * 10 / 0.886 < 71", 20 * PI / F(886, 1000) < I(71), repr(20 * PI / F(886, 1000)))
check("pair ratio (3+1+4)/(2+4) = 4/3 ; non-both-reach successor (3+2)/(2+2) = 5/4 ; (k,d>=2) 5/4",
      F(8, 6) == F(4, 3) and F(5, 4) <= F(4, 3) and F(1 + 4, 4) == F(5, 4))
# (4+m)/(2+m) decreasing in m >= 4, (3+m)/(2+m) decreasing in m >= 2
check("pair-ratio monotone: (4+m)/(2+m) <= 4/3 for m>=4, (3+m)/(2+m) <= 5/4 for m>=2 (m<=10^4 exact)",
      all(F(4 + m, 2 + m) <= F(4, 3) for m in range(4, 10001)) and all(F(3 + m, 2 + m) <= F(5, 4) for m in range(2, 10001)))

print("\n== C6  Region III corner lemma: theta0 = arccos(tau), tau in (sqrt3/2-2b, sqrt3/2+3b)")
c7 = cos(PI / 7); c314 = cos(3 * PI / 14)
check("2 theta0 > 2pi/7  <=  tau < sqrt3/2+3b < cos(pi/7)", tauII < c7, f"cos(pi/7)={c7}")
check("90deg - theta0 > 2pi/7  <=  tau > sqrt3/2-2b > cos(3pi/14)", tauI > c314, f"cos(3pi/14)={c314}")
check("Region III: tau > 2 beta (dichotomy)", tauI > I(2 * beta))

print("\n== C7  lens lemma constants")
def g(c):  # cos(phi0/2) - cos(phi0) with c = cos(phi0)
    return sqrt((1 + I.c(c)) / 2) - c
cKK = LAM / 2                                       # cos(phi0) <= d/(2R) <= 0.97
check("KK: rho0^2 = 1/sin^2(phi0/2) <= 2/(1-0.97) < 8.2^2", F(2) / (1 - cKK) < F(82, 10) ** 2,
      f"rho0 <= {float(F(2) / (1 - cKK)) ** 0.5:.4f}")
check("KK: hypothesis R >= 2/g(0.97) holds for R >= 10^4", I(2) / g(cKK) < I(D2MIN), repr(I(2) / g(cKK)))
check("DD: cos(phi0) <= 1/2 => rho0^2 <= 2/(1-1/2) = 4 = 2^2", F(2) / (1 - F(1, 2)) == 4)
check("DD: hypothesis R >= 2/g(1/2) ~ 5.46 (R = Delta >= 10^4)", I(2) / g(F(1, 2)) < I(D2MIN))
# g decreasing in c on [0,1): g'(c) = 1/(4 sqrt((1+c)/2)) - 1 < 0 since sqrt((1+c)/2) >= sqrt(1/2) > 1/4
check("g decreasing: sqrt(1/2) > 1/4", sqrt(F(1, 2)) > I(F(1, 4)))
check("opposite-sign exclusion: 2 R sin(phi0/2) > 1 for R >= 10^4, sin^2(phi0/2) >= (1-0.97)/2",
      2 * D2MIN * sqrt((1 - cKK) / 2) > I(1))

print("\n== C8  (c2) angle alpha = angle(u_v, g)")
# cos(alpha) >= (1 + rho^2 - LAM^2)/(2 rho), rho = (D2 - d0)/D2 in [1 - 1e-4, 1]; increasing in rho
rho_lo = 1 - F(1) / D2MIN
cos_alpha_lo = (1 + rho_lo ** 2 - LAM ** 2) / (2 * rho_lo)
check("function (1+rho^2-L^2)/(2 rho) increasing in rho (derivative 1/2 + (L^2-1)/(2 rho^2) > 0)", LAM ** 2 > 1)
check("cos(alpha) >= -0.8821  (alpha <= ~151.9 deg)", cos_alpha_lo >= F(-8821, 10000), f"{float(cos_alpha_lo):.6f}")
sin_alpha_hi_end = sqrt(1 - F(8821, 10000) ** 2)
check("sin at the large end sqrt(1-0.8821^2) > sin(beta/2)", sin_alpha_hi_end > sin(I(beta / 2)), repr(sin_alpha_hi_end))
# walking bound: gamma'.g <= -sin(alpha) + 2 sin(beta/8) <= -sin(beta/2) + 2 sin(beta/8) < -beta/5
lhs = -sin(I(beta / 2)) + 2 * sin(I(beta / 8))
check("-sin(beta/2) + 2 sin(beta/8) < -beta/5", lhs < I(-beta / 5), repr(lhs))
Lc2 = 6 / beta
check("L = 6/beta = 600 exceeds 5 d0 D2/(beta (D2 - d0)) for d0<=1, D2>=10^4",
      5 * D2MIN / (beta * (D2MIN - 1)) < Lc2)
# explicit contradiction inequality at s = L, d0 = 1 (worst; LHS-RHS increasing... check d0 grid exactly)
okc = all((F(2, 5) * (D2MIN - d0) * Lc2 * beta) > (2 * D2MIN * d0 - d0 ** 2) for d0 in [F(i, 100) for i in range(0, 101)])
check("(2/5)(D2-d0) L beta > 2 D2 d0 - d0^2 on d0 grid (and it is linear-vs-concave, endpoints suffice)", okc)

print("\n== C9  bad-edge totals (beta = 1/100)")
rho = F(82, 10)
KK = 12 * PI * (4 * rho + 1) / beta
KKnotes = 12 * PI * (4 * rho + 5) / beta
DD = 12 * PI * (4 * 2 + 1) / beta
C1 = 6 * 4 * PI / beta
C2 = 48 * PI * (2 * Lc2 + 1) / beta
MIX = I(71)
tot = KK + DD + C1 + C2 + MIX + 12
check("KK <= 12 pi (4 rho0 + 1)/beta < 1.3e5", KK < I(130000), repr(KK))
check("notes' formula 12 pi (4 rho0 + 5)/beta ~ 1.43e5 (NOT 4.4e4)", I(140000) < KKnotes and KKnotes < I(145000), repr(KKnotes))
check("DD <= 12 pi * 9 / beta < 3.4e4", DD < I(34000), repr(DD))
check("(c1) <= 24 pi / beta < 7600", C1 < I(7600), repr(C1))
check("(c2) <= 48 pi (2L+1)/beta < 1.82e7", C2 < I(18200000), repr(C2))
check("total C_bad + mixed + 12 < 10^8", tot < I(10 ** 8), repr(tot))

print("\n== C10 degenerate regime  Delta > 1.94 Delta_2  (put q = (Delta_2/Delta)^2 < 1/1.94^2)")
q = 1 / LAM ** 2
check("parallelogram: 1 + 3q < 2", 1 + 3 * q < 2, f"1+3q={float(1 + 3 * q):.4f}")
check("15-degree: (2 sin 15)^2 = 2 - sqrt3 > q   <=>  (2 - q)^2 > 3 (2-q>0)", (2 - q) ** 2 > 3 and 2 - q > 0,
      f"(2-q)^2={float((2 - q) ** 2):.6f}")
check("  same, interval form: 2 - sqrt3 > q", 2 - sqrt(3) > I(q))
check("triangle: circumradius^2 = Delta^2/3 > Delta_2^2  <=> 1/3 > q", F(1, 3) > q)
# lens of D(y,D2) and D(a,D2), |ya| = Delta > 1.94 D2: width 2D2 - Delta < 0.06 D2,
# half-height^2 = D2^2 - Delta^2/4 < D2^2 (1 - 0.9409);  bbox diagonal^2 < D2^2
w = 2 - LAM; hh2 = 1 - LAM ** 2 / 4
check("lens bounding-box diagonal^2 / D2^2 = w^2 + 4 hh2 < 1", w ** 2 + 4 * hh2 < 1, f"{float(w ** 2 + 4 * hh2):.4f}")
check("A-arc: chords <= D2 < Delta/1.94 <=> angular < 120 deg (sin 60 = sqrt3/2 > 1/(2*1.94))", R3 > I(1 / (2 * LAM)))

print("\n== C11 small cases: Delta_2 < 10^4 (nondegenerate) => n <= (2 Delta + 1)^2")
N0 = (2 * LAM * D2MIN + 1) ** 2
check("N0 = (2*1.94e4+1)^2 < 1.51e9", N0 < F(151, 100) * 10 ** 9, f"N0={float(N0):.4e}")

print(f"\nALL {N_OK} CHECKS PASSED")
