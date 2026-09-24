"""Type I quadruples {p,-p,q,-q}, |p|=|q|=r, p not parallel to q (two equal-length diameters).
Checks: gradient structure g_p = kappa_p p, g_{-p} = -kappa_p p, kappa_q = -kappa_p, and
the second derivative H(V) of det(p,-p,q+eV,-q+eV) is a nonzero quadratic form in V."""
import sympy as sp
r, b, e, Vx, Vy = sp.symbols('r beta epsilon V_x V_y', real=True)
xs = sp.symbols('x0:4'); ys = sp.symbols('y0:4')
rows = [[xs[i]-xs[3], ys[i]-ys[3], (xs[i]-xs[3])**2+(ys[i]-ys[3])**2] for i in range(3)]
DET = sp.Matrix(rows).det()
p = (r, 0); q = (r*sp.cos(b), r*sp.sin(b))
P = [p, (-p[0], -p[1]), q, (-q[0], -q[1])]
sub = {xs[i]: P[i][0] for i in range(4)}; sub.update({ys[i]: P[i][1] for i in range(4)})
g = [sp.simplify(sp.Matrix([sp.diff(DET, xs[i]), sp.diff(DET, ys[i])]).subs(sub)) for i in range(4)]
print('det at config:', sp.simplify(DET.subs(sub)))
kp = sp.simplify(g[0][0]/p[0]); print('g_p =', list(g[0]), ' kappa_p =', kp)
print('g_p + g_-p =', list(sp.simplify(g[0]+g[1])), ' g_q + g_-q =', list(sp.simplify(g[2]+g[3])))
kq = sp.simplify((g[2].T*sp.Matrix(q))[0]/r**2); print('kappa_q + kappa_p =', sp.simplify(kq+kp))
print('g_q parallel to q:', sp.simplify(g[2][0]*q[1]-g[2][1]*q[0]))
P2 = [p, (-p[0], -p[1]), (q[0]+e*Vx, q[1]+e*Vy), (-q[0]+e*Vx, -q[1]+e*Vy)]
sub2 = {xs[i]: P2[i][0] for i in range(4)}; sub2.update({ys[i]: P2[i][1] for i in range(4)})
f = sp.expand(DET.subs(sub2))
H = sp.factor(sp.simplify(sp.diff(f, e, 2).subs(e, 0)))
print('H(V) =', H)
print('H at V=(0,1):', sp.factor(sp.simplify(H.subs({Vx: 0, Vy: 1}))), ' at V=(1,0):', sp.factor(sp.simplify(H.subs({Vx: 1, Vy: 0}))))
