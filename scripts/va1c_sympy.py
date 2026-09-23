"""Exact (sympy) verification of the two algebraic identities in VERIFY_A1c.md.

Lemma M.  p = 0, b = (1,0), a = (cos A, -sin A) with 0 < A < pi,
r = b + (cos F, sin F) with 0 <= F < pi (r on C(b,1), r != p, r not strictly
on a's side of line pb).  Then
    |r - a|^2 - 1 = 2(1 + cos F)(1 - cos A) + 2 sin F sin A   (> 0).

Lemma K (bisector step).  r = t*(cos(pi - g), sin(pi - g)), t > 0, and
|r - b| = 1  <=>  t = -2 cos g.
Chord monotonicity: |e(x) - e(y)|^2 = 2 - 2cos(x - y) = 4 sin^2((x-y)/2).
"""
import sympy as sp

A, F, g, t, x, y = sp.symbols('A F g t x y', real=True)

# Lemma M
b = sp.Matrix([1, 0])
a = sp.Matrix([sp.cos(A), -sp.sin(A)])
r = b + sp.Matrix([sp.cos(F), sp.sin(F)])
lhs = (r - a).dot(r - a) - 1
rhs = 2 * (1 + sp.cos(F)) * (1 - sp.cos(A)) + 2 * sp.sin(F) * sp.sin(A)
assert sp.simplify(sp.expand_trig(lhs - rhs)) == 0
print('Lemma M identity: OK')

# Lemma K
rr = t * sp.Matrix([sp.cos(sp.pi - g), sp.sin(sp.pi - g)])
eq = sp.expand(sp.simplify((rr - b).dot(rr - b) - 1))
sol = sp.solve(sp.Eq(eq, 0), t)
print('Lemma K: |r-b|^2-1 =', sp.factor(eq), ' roots t =', sol)
assert set(sp.simplify(s) for s in sol) == {0, -2 * sp.cos(g)}

# chord formula
ex = sp.Matrix([sp.cos(x), sp.sin(x)]) - sp.Matrix([sp.cos(y), sp.sin(y)])
assert sp.simplify(ex.dot(ex) - 4 * sp.sin((x - y) / 2) ** 2) == 0
print('chord formula: OK')

# bisector: points of C(0,1) at angles -a1, -a2 are equidistant from s*e(-g), g=(a1+a2)/2
a1, a2, s = sp.symbols('a1 a2 s', real=True)
gg = (a1 + a2) / 2
P = s * sp.Matrix([sp.cos(-gg), sp.sin(-gg)])
w1 = sp.Matrix([sp.cos(-a1), sp.sin(-a1)])
w2 = sp.Matrix([sp.cos(-a2), sp.sin(-a2)])
assert sp.simplify(sp.expand_trig((P - w1).dot(P - w1) - (P - w2).dot(P - w2))) == 0
print('bisector direction: OK')
