"""Fourier-block analysis of the cokernel (self-stresses) of the edge-length map at the
symmetric seed.  Complex positions z; equilibrium written in the basis (z, zbar)."""
import sympy as sp
t, R, u = sp.symbols('t R u', real=True)  # u = mode angle: omega = e^{i u}
w = sp.exp(sp.I*u); E = sp.exp(sp.I*t)
z0 = sp.Rational(1,2); zk1 = -R*E; zkm1 = -R/E; zk = -sp.Rational(1,2); z2 = E**2/2; z1 = R*E
def cj(expr):  # conjugate of positions only (t,R real)
    return expr.subs(sp.I, -sp.I)
al, be, ga, de = sp.symbols('alpha beta gamma delta')
eqs = []
for f in (lambda x: x, cj):
    eqs.append(al*(f(z0)-f(zk1)) + be*(f(z0)-f(zkm1)) + ga*(f(z0)-f(zk)))
    eqs.append(al*(f(zk1)-f(z0)) + be*w*(f(zk1)-f(z2)) + de*(f(zk1)-f(z1)))
M4 = sp.Matrix([[sp.expand(e).coeff(v) for v in (al, be, ga, de)] for e in eqs])
det4 = sp.simplify(sp.expand(M4.det()))
print('det (even modes) =', sp.factor(det4))
Rsol = (-sp.cos(t) + sp.sqrt(sp.cos(t)**2 + 3))/2
import mpmath as mp
# numeric scan of |det| over u in [0,2pi), t in (0, pi/6]
f = sp.lambdify((t, u), det4.subs(R, Rsol), 'mpmath')
worst = min(abs(f(mp.pi/6*a/60, 2*mp.pi*b/200)) / (mp.pi/6*a/60)**4 for a in range(1, 61) for b in range(200))
print('min |det|/t^4 on grid:', worst)
M2 = M4[:, :2]
print('odd-mode 4x2 block rank generic:', M2.subs({R: Rsol}).subs({t: 0.3, u: 1.1}).evalf().rank())
M3 = M4[:, :3]
print('r=0 block (delta=0) at u=0:', sp.factor(sp.simplify(M3.subs(u, 0)[[0,1,2],:].det())), '| rows 0,1,3:', sp.factor(sp.simplify(M3.subs(u,0)[[0,1,3],:].det())))
