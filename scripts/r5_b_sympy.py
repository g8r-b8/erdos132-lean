"""R5/B symbolic checks for the Trapezoid Lemma (Thm 2) computations.
Coordinates: x=(-s,0), p=(s,0), u=(-t,-d), b=(t,-d), w=(0,e*k) with k^2=1-s^2, d^2=1-(t-s)^2, e=+-1."""
import sympy as sp
s, t, d, k = sp.symbols('s t d k', positive=True)
x = sp.Matrix([-s, 0]); p = sp.Matrix([s, 0]); u = sp.Matrix([-t, -d]); b = sp.Matrix([t, -d])
cr = lambda o, a, c: (a[0]-o[0])*(c[1]-o[1]) - (a[1]-o[1])*(c[0]-o[0])
sq = lambda v: (v.T*v)[0]
rel = {k**2: 1 - s**2, d**2: 1 - (t - s)**2}
def red(e):
    e = sp.expand(e)
    e = e.subs(k**2, 1 - s**2).subs(d**2, 1 - (t - s)**2)
    return sp.simplify(sp.expand(e))
print('|xu|^2 =', red(sq(u - x)), ' (=1 by choice of d)')
print('|xb|^2 - (1+4st) =', red(sq(b - x) - (1 + 4*s*t)))
print('|pu|^2 - |xb|^2 =', red(sq(u - p) - sq(b - x)))
for e in (1, -1):
    w = sp.Matrix([0, e*k])
    print(f'--- e={e}')
    print(' |wx|^2 =', red(sq(w - x)), ' |wp|^2 =', red(sq(w - p)))
    print(' cross(x,w,p) =', sp.factor(cr(x, w, p)), '  cross(x,w,u) =', sp.expand(cr(x, w, u)))
    print(' cross(p,w,x) =', sp.factor(cr(p, w, x)), '  cross(p,w,b) =', sp.expand(cr(p, w, b)))
    print(' |wu|^2 =', red(sq(w - u)), '  |wb|^2 - |wu|^2 =', red(sq(w - b) - sq(w - u)))
# case (beta): 2t = D, 2s = D - 1/D :  RHS 2s(s+t) vs LHS 1 + 2kd
D = sp.symbols('D', positive=True)
sb = (D - 1/D)/2; tb = D/2
print('beta: t-s =', sp.simplify(tb - sb), ';  2s(s+t) =', sp.factor(sp.simplify(2*sb*(sb + tb))),
      '; check D^2 = 1+4st:', sp.simplify(1 + 4*sb*tb - D**2))
