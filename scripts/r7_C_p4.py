"""R7/C: Lemma P4 (G = 1 strip runs have length <= 2), rigorous via elimination.

Strip at G = 1 (A3 closed forms): w = 0, v_j = R e(j a), z_j = Delta e((j+1/2) a), a = alpha_2, p = sqrt(4R^2-1),
Delta = (p + sqrt3)/2.  Shift so that z_0 = Delta e(-a/2), z_1 = Delta e(a/2), v_0 = R e(-a).
A Delta_2-partner y of an interior z_1 of a run (z_0, z_1, z_2 in the run, v_0 and v_3 present) must, by the cone lemma,
be diametral to z_0 or z_2 (mirror cases).  y in C(z_0, Delta) cap C(z_1, R) = {y-, y+}:
   Y = R (Delta^2 - R^2)/(2 Delta),  X = Delta c -+ sqrt(rad),  rad = R^2 - (Y - Delta/(2R))^2, c = p/(2R).
Claims, for every R >= 10^4:
  (P4a) |y+| > Delta  (so y+ is not in X, as w in X);
  (P4b) R^2 < |y- - v_0|^2 < Delta^2  (distance in (R, Delta): impossible).
Proof method: E(R) := Delta^2 - |y- - v_0|^2 = A + B sqrt(rad) with A, B in Q(sqrt3)[R, p].  If E(R0) = 0 then
A^2 - B^2 rad = 0; eliminating sqrt3 and p by resultants gives a nonzero polynomial Pi(R) with Pi(R0) = 0.  We compute
all real roots of Pi, check none is >= 10^4, and evaluate E(10^4) > 0 rigorously (60-digit intervals); E is continuous
on [10^4, oo), hence E > 0 there.  Similarly |y- - v0|^2 - R^2 and |y+|^2 - Delta^2 (trivial margins, same method).
Series (sympy): E = 3 - 4 sqrt3/R + 24/R^2 + O(R^-3); |y+|^2 - Delta^2 = 2R^2 + O(R).
"""
import sympy as sp
from mpmath import iv, mp
R, p, q, rho = sp.symbols('R p q rho', real=True)   # q = sqrt3, rho = sqrt(rad)
D = (p + q) / 2
c = p / (2 * R); s1 = 1 / (2 * R)
Y = R * (D ** 2 - R ** 2) / (2 * D)
rad = R ** 2 - (Y - D * s1) ** 2
cosA = c ** 2 - s1 ** 2; sinA = 2 * s1 * c
v0 = (R * cosA, -R * sinA)
def elim(expr_num):
    """expr = A + B rho (rational in R,p,q); return polynomial in R vanishing wherever expr vanishes."""
    ex = sp.together(sp.expand(expr_num))
    num, den = sp.fraction(ex)
    num = sp.expand(num)
    polyr = sp.Poly(num, rho)
    coeffs = polyr.all_coeffs()
    # num is quadratic in rho at most; replace rho^2 by rad
    num2 = sp.expand(num.subs(rho ** 2, rad))
    num2 = sp.together(num2); n2, d2 = sp.fraction(num2); n2 = sp.expand(n2)
    A = n2.coeff(rho, 0); B = n2.coeff(rho, 1)
    F = sp.expand(A ** 2 - B ** 2 * sp.fraction(sp.together(rad))[0] / sp.fraction(sp.together(rad))[1])
    F = sp.fraction(sp.together(F))[0]
    F = sp.expand(F)
    r1 = sp.resultant(F, q ** 2 - 3, q)
    r2 = sp.resultant(sp.expand(r1), p ** 2 - (4 * R ** 2 - 1), p)
    return sp.Poly(sp.expand(r2), R)
X_minus = D * c - rho
X_plus = D * c + rho
exprs = {
    'E = Delta^2 - |y- - v0|^2': D ** 2 - ((X_minus - v0[0]) ** 2 + (Y - v0[1]) ** 2),
    'F = |y- - v0|^2 - R^2': ((X_minus - v0[0]) ** 2 + (Y - v0[1]) ** 2) - R ** 2,
    'H = |y+|^2 - Delta^2': (X_plus ** 2 + Y ** 2) - D ** 2,
}
iv.dps = 60
def ev(expr, Rv):
    Ri = iv.mpf(Rv); pi_ = iv.sqrt(4 * Ri ** 2 - 1); qi = iv.sqrt(3)
    Di = (pi_ + qi) / 2; ci = pi_ / (2 * Ri); s1i = 1 / (2 * Ri)
    Yi = Ri * (Di ** 2 - Ri ** 2) / (2 * Di)
    radi = Ri ** 2 - (Yi - Di * s1i) ** 2
    rhoi = iv.sqrt(radi)
    f = sp.lambdify((R, p, q, rho), expr, modules=[{'sqrt': iv.sqrt, 'mpf': iv.mpf}, 'mpmath'])
    return f(Ri, pi_, qi, rhoi)
for name, ex in exprs.items():
    P = elim(ex)
    P = sp.Poly(sp.factor_list(P.as_expr())[1][0][0] if False else P.as_expr(), R)
    roots = [r for r in sp.Poly(P.as_expr(), R).real_roots()] if P.degree() > 0 else []
    big = [float(r) for r in roots if r >= 10 ** 4]
    val = ev(ex, 10 ** 4)
    print('%s: eliminant degree %d, nonzero: %s, real roots >= 1e4: %s, value at R=1e4 in [%s, %s]'
          % (name, P.degree(), not P.is_zero, big, mp.nstr(val.a, 8), mp.nstr(val.b, 8)))
    assert not P.is_zero and not big and val.a > 0
print('r7_C_p4: P4a, P4b hold for all R >= 10^4')
