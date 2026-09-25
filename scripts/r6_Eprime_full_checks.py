"""R6 / Theorem E' (angle_R6.md section 5): exact checks of every numerical inequality in the
complete corrected proof.  All comparisons are between Fractions; sin is enclosed by alternating
Taylor partial sums (valid for 0 <= x <= 2, where the terms decrease); pi is enclosed by
333/106 < pi < 355/113; square roots are removed by squaring.  No floating point is used as proof.

Run:  .venv/bin/python problems/132/scripts/r6_Eprime_full_checks.py
Notation: h = shell depth (rho + 1/2), D2 = Delta_2 (the second distance), n = |X|.
"""
from fractions import Fraction as F

PI_LO, PI_HI = F(333, 106), F(355, 113)
ok = 0


def check(cond, msg):
    global ok
    assert cond, msg
    ok += 1
    print("PASS", msg)


def sin_hi(x):  # partial sum ending with a + term: upper bound for 0 <= x <= 2
    return x - x**3 / 6 + x**5 / 120 - x**7 / 5040 + x**9 / 362880


# ---------------------------------------------------------------- Lemma F (fatness)
# 2*sqrt(1 - 9 w0^2/L^2) <= 1.94 + w0/D2 <= 1.96 when w0 <= 0.02 D2  =>  sqrt(...) <= 0.98
c = (F(194, 100) + F(2, 100)) / 2
check(c == F(98, 100), "Lemma F: (1.94 + 0.02)/2 = 0.98")
check(1 - c**2 == F(396, 10000), "Lemma F: 1 - 0.98^2 = 0.0396")
# 9 w0^2 / L^2 >= 0.0396  =>  L/w0 <= 3/sqrt(0.0396) < 15.1   (square: 9/0.0396 < 15.1^2)
check(9 / F(396, 10000) < F(151, 10)**2, "Lemma F: 3/sqrt(0.0396) < 15.1")
check(1 + F(151, 10)**2 < 100**2, "Lemma F: diam <= sqrt(1 + 15.1^2) w0 < 100 w0")
check(2 == 100 * F(2, 100), "Lemma F: w0 > 0.02 D2 => diam K <= 2 D2 < 100 w0")

# ---------------------------------------------------------------- parameters
# rho0 = floor(min(n^(1/3), D2/400)) >= 1  =>  h <= 2 rho0 - 1/2 <= D2/200 - 1/2 < D2/200
hr = F(1, 200)  # upper bound for h/D2
check(2 * F(1, 400) == hr, "params: 2*rho0 <= D2/200")

# ---------------------------------------------------------------- Step 2 (collapse length), G4
s_star = F(97, 100) / (1 - hr)          # sin(psi_c/2) <= 0.97 D2/(D2 - h) <= 0.97/(1 - 1/200)
check(s_star == F(194, 199), "Step 2: sin(psi/2) <= 0.97/(1-1/200) = 194/199")
check(s_star < 1, "Step 2: 194/199 < 1, so psi_c < pi and the kite is bounded")
theta_L = F(1343, 1000)
check(sin_hi(theta_L) < s_star, "Step 2: sin(1.343) < 194/199, so theta* := arcsin(194/199) > 1.343")
# tan(theta*) = s*/sqrt(1 - s*^2) = 194/sqrt(1965)
check(1 - s_star**2 == F(1965, 199**2), "Step 2: 1 - (194/199)^2 = 1965/199^2")
# tan(x)/x increasing on (0, pi/2): tan(x) <= (tan(theta*)/theta*) x <= (194/sqrt(1965))/1.343 x
# claim 194/sqrt(1965) <= 3.26 * 1.343   <=>   194^2 <= (3.26*1.343)^2 * 1965
check(F(194)**2 <= (F(326, 100) * theta_L)**2 * 1965, "Step 2 (G4): tan(theta*)/theta* <= 3.26, so tan(psi/2) <= 3.26 (psi/2) = 1.63 psi")
# sum over corners: sum len Z_c <= 2h * 1.63 * sum psi_c <= 2h * 1.63 * 2 pi <= 21 h
check(2 * F(163, 100) * 2 * PI_HI < 21, "Step 2: 2 * 1.63 * 2pi < 21, so sum_c len Z_c <= 21 h")

# ---------------------------------------------------------------- case (i)
# Def(H_out) >= |A| - 3 + per K' ,  per K' >= per K - (h/D2) per K - 21h >= per K - 2 pi h - 21 h,
# per K >= |A| - 1  =>  Def(H_out) >= 2|A| - (21 + 2 pi) h - 4
check(21 + 2 * PI_HI < 28, "case (i): (21 + 2pi) < 28")

# ---------------------------------------------------------------- Step 5 (window), G1
off = 2 / (1 - hr)                      # 2 D2/(D2 - h)
check(off == F(400, 199), "Step 5: 2 D2/(D2-h) <= 400/199")
check(off < F(202, 100) and off < 3, "Step 5 (G1): len U_c <= 21h + 2.02 <= 21h + 3, so N <= 21h + 4")
# |F_c| <= 2N - 3 <= 2(21h + 4) - 3 = 42h + 5   (identity of linear polynomials: check coefficients)
check((2 * 21, 2 * 4 - 3) == (42, 5), "Step 5: 2(21h+4) - 3 = 42h + 5")

# ---------------------------------------------------------------- G2 fallback: per K >= 100 h => per K' > 2
h_min = F(3, 2)                          # h = rho + 1/2 >= 3/2 since rho >= 1
perKp = (1 - hr) * (100 - 21) * h_min    # per K' >= (1 - h/D2)(per K - 21h) >= (199/200) * 79 h
check(perKp > 2, "G2: per K >= 100h and h >= 3/2 give per K' >= (199/200)*79h > 2, so B_c != boundary of K'")

# ---------------------------------------------------------------- Step 6 (total, case (ii))
# sum e(alpha) <= |A| h/D2 + 21h (42h + 5),  |A| <= 2 pi D2 + 1  =>  |A| h / D2 <= 2 pi h + 1/200
# 2 sum e <= 1764 h^2 + (210 + 4 pi) h + 1/100
check(2 * 21 * 42 == 1764 and 2 * 21 * 5 == 210, "Step 6: 2*21*(42h+5) = 1764h + 210 per h")
check(210 + 4 * PI_HI < 223, "Step 6: 210 + 4pi < 223")
check(2 * hr < 4, "Step 6: constant 1/100 <= 4")
# E(h) := 1764 h^2 + 223 h + 4 dominates case (i): (21+2pi) h + 4 <= 223 h + 4
check(21 + 2 * PI_HI <= 223, "E(h) covers case (i)")

# ---------------------------------------------------------------- Step 7 (parameters), G3
# E(h) with h <= 2 n^(1/3): 1764*4 n^(2/3) + 223*2 n^(1/3) + 4 <= 7506 n^(2/3)   (n >= 1)
check(1764 * 4 + 223 * 2 + 4 == 7506, "Step 7: E(2 n^(1/3)) <= 7506 n^(2/3)")
# shells, rho0 = floor(n^(1/3)) >= n^(1/3)/2: 3n/rho0 <= 6 n^(2/3)
# shells, rho0 = floor(D2/400) >= D2/800: 3n/rho0 <= 2400 n/D2;  D2 >= (sqrt n - 1)/3.88 >= sqrt(n)/7.76 (n>=4)
check(2 * F(194, 100) == F(388, 100), "Step 7: n <= (2 Delta + 1)^2 and Delta <= 1.94 D2 give D2 >= (sqrt n - 1)/3.88")
check(3 * 800 == 2400 and 2400 * F(776, 100) == 18624, "Step 7: 2400 * 7.76 = 18624")
check(3 * 4 == 12, "Step 7: n < 4 gives 3n/rho0 <= 12 <= 12 n^(2/3)")
shells = 18624 + 12
check(shells >= 6, "Step 7: 3n/rho0 <= 18636 n^(2/3) in both sub-cases")
# fallback rho0 = 0 (D2 < 400): Delta < 776, n <= 1553^2 < 2.42e6 < 135^3, 2|A| <= 2n <= 270 n^(2/3)
check(F(194, 100) * 400 == 776 and 2 * 776 + 1 == 1553, "G3: D2 < 400 gives 2 Delta + 1 < 1553")
check(1553**2 < 2420000 < 135**3, "G3: n < 1553^2 < 2.42e6 < 135^3")
check(2 * 135 == 270, "G3: 2n <= 270 n^(2/3)")
# fallback r_in(K) <= h: |A| <= per K + 1 <= pi diam K + 1 <= 300 pi h + 1, h <= 2 n^(1/3)
check(2 * 300 * 2 * PI_HI + 2 <= 3772, "fallback r_in <= h: 2|A| <= 1200 pi n^(1/3) + 2 <= 3772 n^(2/3)")
# fallback per K < 100 h: 2|A| <= 200 h + 2 <= 402 n^(2/3)
check(200 * 2 + 2 == 402, "fallback per K < 100h: 2|A| <= 402 n^(2/3)")
total = 7506 + shells
check(total == 26142 and total < 30000 and max(270, 3772, 402) < 30000,
      "Theorem E': Def(G[X minus D]) >= 2|S minus D| - 3*10^4 n^(2/3) for all n >= 1")

# ---------------------------------------------------------------- tau > 1 corollary (LP)
# max over s of min(1.5 s, 3n - 2s) = 9n/7 at s = 6n/7
n = F(7)
s = 6 * n / 7
check(F(3, 2) * s == 3 * n - 2 * s == 9 * n / 7, "LP: at s = 6n/7 both terms equal 9n/7")
check(F(3, 2) > 0 and -2 < 0, "LP: 1.5s increasing, 3n-2s decreasing, so the max of the min is at the crossing")

print(f"\nall {ok} assertions passed")
