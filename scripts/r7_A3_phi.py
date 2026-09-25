"""R7 / A3 referee: rigorous checks of the angle inequalities used by B2 (Regions II/III).

Notation (B2): R = Delta_2 >= 1e4, x := 1/R in (0, 1e-4], tau in Region II/III, t from tau via
tau = t - (1-t^2)/(2R)  <=>  t = (x + 2 tau)/(1 + sqrt(1 + x^2 + 2 tau x)),  Delta = R + t,
s = sqrt(1 - tau^2), alpha_2 = 2 asin(1/(2R)), alpha_1 = 2 asin(1/(2 Delta)), phi = atan(s/(R+tau)).

(1) EXACT identity (sympy): sin(phi) = s/Delta.  Hence
      2 phi < alpha_1  <=>  s < 1/2  <=>  tau > sqrt3/2           (so FALSE on the lower half of Region III)
      2 phi / alpha_1 <= 2 s        (asin(y)/y increasing)          (Region II: <= 2 s_max < 0.8881)
      2 phi < alpha_1 + alpha_2     (asin superadditive on [0,1])   (what Region III needs)
(2) RIGOROUS interval enclosures (mpmath.iv), using the proved inequality
      1 <= asin(y)/y <= 1 + y^2/(6(1-y^2))   (0 <= y < 1; Taylor coefficients of asin are <= 1/6),
    over a cover of tau in [sqrt3/2 - 2 beta, 1] by subintervals and x in [0, 1e-4]:
      (a) R*alpha_2 in [1, 1 + 1e-8]
      (b) R^2 (alpha_2 - alpha_1) <= 0.8962  in Region III   (i.e. R(alpha_2-alpha_1) <= 0.8962/R)
      (c) R |2 R phi - 2 s| <= 1             in Region III
      (d) l = -2 is impossible in (*) for an unbroken opposite-sign gap:  since k alpha_1 <= pi/3,
          k R (alpha_2 - alpha_1) <= (pi/3)(alpha_2/alpha_1 - 1) R  <  2 R alpha_2 - 2 R phi   (Region III)
      (e) Region II: 2 phi < alpha_1 with ratio < 0.8881; Region III: 2 phi < alpha_1 + alpha_2 with margin.
"""
import sympy as sp
from mpmath import iv, mp, mpf

mp.dps = 50
iv.dps = 50

# ---------------- (1) exact identity -----------------
R, tau, sg = sp.symbols('R tau sigma', positive=True)
s = sp.sqrt(1 - tau ** 2)
# u = (1,0) (direction from v to w), w = 0, v = -R u, z = w - (R+tau) u + sigma s u_perp
v = sp.Matrix([-R, 0])
z = sp.Matrix([-(R + tau), s])            # sigma = +1
Delta2 = sp.expand(z.dot(z))              # |z - w|^2
cross = v[0] * z[1] - v[1] * z[0]
sinphi_sq = sp.simplify(cross ** 2 / (v.dot(v) * Delta2))
assert sp.simplify(sinphi_sq - s ** 2 / Delta2) == 0
# and Delta^2 = R^2 + 2 R tau + 1 (= (R+t)^2 by the tau-t identity)
assert sp.expand(Delta2 - (R ** 2 + 2 * R * tau + 1)) == 0
t_ = sp.symbols('t', positive=True)
tau_of_t = t_ - (1 - t_ ** 2) / (2 * R)
assert sp.expand((R ** 2 + 2 * R * tau_of_t + 1) - (R + t_) ** 2) == 0
print('(1) exact: sin(phi) = s/Delta, Delta^2 = R^2 + 2R tau + 1 = (R+t)^2  [sympy]')


# ---------------- (2) rigorous enclosures -----------------
def g(y):
    """enclosure of asin(y)/y for an interval y subset [0, 1)."""
    hi = y.b
    return iv.mpf([1, 1 + hi ** 2 / (6 * (1 - hi ** 2))])


def enclose(tlo, thi, xhi=mpf('1e-4')):
    T = iv.mpf([tlo, thi])
    X = iv.mpf([0, xhi])
    t = (X + 2 * T) / (1 + iv.sqrt(1 + X ** 2 + 2 * T * X))
    S = iv.mpf([iv.sqrt(1 - iv.mpf(thi) ** 2).a if thi < 1 else 0, iv.sqrt(1 - iv.mpf(tlo) ** 2).b])
    one_tx = 1 + t * X                     # Delta / R
    Ra2 = g(X / 2)                         # R alpha_2
    Ra1 = g(X / (2 * one_tx)) / one_tx     # R alpha_1
    y_phi = S * X / one_tx                 # sin(phi) = s/Delta = s x/(1 + t x)
    R2phi = 2 * S * g(y_phi) / one_tx      # 2 R phi
    # R^2 (alpha_2 - alpha_1) = [R alpha_2 - R alpha_1] / x ; compute with a divided-difference-free bound:
    # R(alpha_2 - alpha_1) = 2R[asin(x/2) - asin(x/(2(1+tx)))] <= 2R * (x/2 - x/(2(1+tx))) / sqrt(1 - x^2/4)
    #                     = t x/(1+tx) / sqrt(1-x^2/4)          (mean value theorem, asin' <= 1/sqrt(1-y^2))
    R2da_hi = (t / one_tx / iv.sqrt(1 - X ** 2 / 4))       # upper bound for R^2 (alpha_2 - alpha_1)
    # R |2 R phi - 2 s|:  2Rphi - 2s = 2s [g(y)/(1+tx) - 1];  |.|/x <= 2s[ (g-1)/x + t ]  (g-1 <= y^2/(6(1-y^2)))
    # bound directly: 2s - 2Rphi <= 2s(1 - 1/(1+tx)) = 2s t x/(1+tx) ; 2Rphi - 2s <= 2s (g_hi - 1)/(1+tx) <= 2s y^2/(6(1-y^2))
    # so R|2Rphi - 2s| <= max(2 s t/(1+tx), 2 s * s^2 x/(6(1-y^2)))  (using y <= s x)
    R_err = iv.mpf([0, max((2 * S * t / one_tx).b, (2 * S * S * S * X / (6 * (1 - y_phi.b ** 2))).b)])
    return dict(t=t, S=S, Ra2=Ra2, Ra1=Ra1, R2phi=R2phi, R2da_hi=R2da_hi, R_err=R_err)


s3 = iv.sqrt(3) / 2
beta = mpf(1) / 100
lo3, hi3 = (s3 - 2 * beta).a, (s3 + 3 * beta).b     # Region III (outer enclosure)
lo2 = (s3 + 3 * beta).a                             # Region II starts here (inner end, conservative)

N = 400
worst = dict(Ra2=mpf(0), R2da=mpf(0), Rerr=mpf(0), lmargin=mpf(10), ratio2=mpf(0), m3=mpf(10))
for i in range(N):
    a = lo3 + (hi3 - lo3) * i / N
    b = lo3 + (hi3 - lo3) * (i + 1) / N
    E = enclose(a, b)
    worst['Ra2'] = max(worst['Ra2'], E['Ra2'].b)
    worst['R2da'] = max(worst['R2da'], E['R2da_hi'].b)
    worst['Rerr'] = max(worst['Rerr'], E['R_err'].b)
    # (d): (pi/3)(alpha2/alpha1 - 1) R  <  2 R alpha2 - 2 R phi
    # (alpha2/alpha1 - 1) R = R(alpha2-alpha1)/alpha1 = [R^2(alpha2-alpha1)] / [R alpha1]
    lhs = (iv.pi / 3) * E['R2da_hi'] / E['Ra1']
    rhs = 2 * E['Ra2'] - E['R2phi']
    marg = (rhs - lhs).a
    worst['lmargin'] = min(worst['lmargin'], marg)
    assert marg > 0, ('l=-2 not excluded', a, b, marg)
    # (e) Region III: 2phi < alpha1 + alpha2
    m3 = (E['Ra1'] + E['Ra2'] - E['R2phi']).a
    worst['m3'] = min(worst['m3'], m3)
    assert m3 > 0
print('(2a) R alpha_2 <= %s' % mp.nstr(worst['Ra2'], 12))
assert worst['Ra2'] <= 1 + mpf('1e-8')
print('(2b) Region III: R^2 (alpha_2 - alpha_1) <= %s' % mp.nstr(worst['R2da'], 8))
assert worst['R2da'] <= mpf('0.8962')
print('(2c) Region III: R |2R phi - 2s| <= %s' % mp.nstr(worst['Rerr'], 8))
assert worst['Rerr'] <= 1
print('(2d) Region III: l = -2 excluded; min margin (2R a2 - 2R phi) - (pi/3)(a2/a1 - 1)R = %s' % mp.nstr(worst['lmargin'], 6))
print('(2e) Region III: min R(alpha_1 + alpha_2 - 2 phi) = %s  (> 0)' % mp.nstr(worst['m3'], 6))

# Region II: 2 phi < alpha_1, ratio <= 2 s_max
N2 = 200
rmax = mpf(0)
for i in range(N2):
    a = lo2 + (1 - lo2) * i / N2
    b = lo2 + (1 - lo2) * (i + 1) / N2
    E = enclose(a, b)
    ratio = (E['R2phi'] / E['Ra1']).b
    rmax = max(rmax, ratio)
    assert ratio < 1
smax = iv.sqrt(1 - (s3 + 3 * beta) ** 2).b
print('(2e) Region II: max 2phi/alpha_1 <= %s ; analytic bound 2 s_max = %s' % (mp.nstr(rmax, 8), mp.nstr(2 * smax, 8)))
assert rmax < mpf('0.8882') and 2 * smax < mpf('0.8881')

# Lower Region III: 2 phi > alpha_1 whenever tau < sqrt3/2 (counterexample to "2phi < alpha_1 on Region III")
E = enclose(lo3, lo3 + mpf('1e-6'))
assert (E['R2phi'] - E['Ra1']).a > 0
print('(3) tau = sqrt3/2 - 2 beta: 2R phi - R alpha_1 >= %s > 0, so 2phi < alpha_1 FAILS there (as the identity predicts)'
      % mp.nstr((E['R2phi'] - E['Ra1']).a, 6))
print('all r7_A3_phi checks pass')
