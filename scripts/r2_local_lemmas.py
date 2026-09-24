"""Exact (sympy) identities behind L1/L2 repairs for a deg-3 hull vertex p.
Frame A (middle): p=0, w2=(1,0), w1=e(-al), w3=e(be), 0<al,be<=60deg.
Frame B (outer):  p=0, w1=(1,0), w2=e(a), w3=e(a+b), 0<a,b<=60deg."""
import sympy as sp
al, be, ph, a, b, t, F, A = sp.symbols('alpha beta phi a b t F A', real=True)
e = lambda x: sp.Matrix([sp.cos(x), sp.sin(x)])
n2 = lambda v: sp.simplify((v.T*v)[0])
# Lemma M identity
p0 = sp.Matrix([0, 0]); B_ = sp.Matrix([1, 0]); aa = sp.Matrix([sp.cos(A), -sp.sin(A)]); rr = B_ + e(F)
lhs = n2(rr-aa) - 1; rhs = 2*(1+sp.cos(F))*(1-sp.cos(A)) + 2*sp.sin(F)*sp.sin(A)
print('LemmaM identity:', sp.simplify(sp.expand_trig(lhs-rhs)) == 0)
# F2: r above with |rw1|=|rw3| => r=2cos(th)e(th), th=(be-al)/2; then |r-w1|^2-|r|^2 = 1-2(cos al+cos be)
th = (be-al)/2; r = 2*sp.cos(th)*e(th); w1 = e(-al); w3 = e(be); w2 = sp.Matrix([1, 0])
print('F2 |r-w2|^2 = 1:', sp.simplify(sp.expand_trig(n2(r-w2)-1)) == 0)
print('F2 |r-w1|=|r-w3|:', sp.simplify(sp.expand_trig(n2(r-w1)-n2(r-w3))) == 0)
d = sp.simplify(sp.expand_trig(n2(r-w1) - n2(r) - (1-2*(sp.cos(al)+sp.cos(be)))))
print('F2 key identity:', d == 0)
# on-line case r=(2,0): |r-w1|^2 = 5-4cos(al)
print('online:', sp.simplify(n2(sp.Matrix([2, 0])-w1) - (5-4*sp.cos(al))) == 0)
# Case B: bisector of w2,w3 in frame B is t*e(g), g=a+b/2; meets C(w1,1) at t(t-2cos g)=0
g = a + b/2; W1 = sp.Matrix([1, 0]); r1 = t*e(g)
print('caseB bisector:', sp.simplify(n2(r1-e(a)) - n2(r1-e(a+b))) == 0)
print('caseB circle:', sp.factor(sp.simplify(sp.expand_trig(n2(r1-W1)-1))))
