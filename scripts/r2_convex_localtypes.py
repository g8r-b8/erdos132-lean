"""Exact check of the finitely many 'local' 4-subsets (points on <= 4 consecutive diameters
S_y = [a_y, a_{y+k}] = [a_y, -a_y] at the seed) for all t in (0, pi/6]:
for each type, either the seed is not concyclic or some first-order derivative
n_j . G_j (j an internal link) is nonzero.
Elimination: expressions are polynomials in c=cos t, s=sin t, R with s^2=1-c^2 and
R^2 + c R - 3/4 = 0; A + sB = 0 => A^2-(1-c^2)B^2 = 0; then resultant in R.  Roots of the
gcd of the eliminated polynomials in [sqrt(3)/2, 1) are counted exactly (Sturm)."""
import sympy as sp, itertools
c, s, R = sp.symbols('c s R', real=True)
X = sp.symbols('x0:4'); Y = sp.symbols('y0:4')
def cosk(k):  # cos(k t), sin(k t) as polynomials in c, s
    e = sp.expand((c + sp.I*s)**k)
    return sp.re(e), sp.im(e)
def pt(y, sg):
    r = sp.Rational(1, 2) if y % 2 == 0 else R
    ck, sk = cosk(y)
    return (sg*r*ck, sg*r*sk)
rows = [[X[i]-X[3], Y[i]-Y[3], (X[i]-X[3])**2+(Y[i]-Y[3])**2] for i in range(3)]
DET = sp.Matrix(rows).det()
GR = [(sp.diff(DET, X[i]), sp.diff(DET, Y[i])) for i in range(4)]
def reduce_s(expr):
    expr = sp.expand(expr)
    p = sp.Poly(expr, s)
    A = 0; B = 0
    for (d,), co in p.terms():
        if d % 2 == 0: A += co*(1-c**2)**(d//2)
        else: B += co*(1-c**2)**(d//2)
    return sp.expand(A), sp.expand(B)
def eliminate(expr):
    A, B = reduce_s(expr)
    P = sp.expand(A**2 - (1-c**2)*B**2)
    if P == 0: return sp.Integer(0)
    res = sp.resultant(sp.Poly(P, R), sp.Poly(R**2 + c*R - sp.Rational(3, 4), R))
    return sp.expand(res.as_expr() if hasattr(res, 'as_expr') else res)
def roots_in_interval(poly):
    if poly == 0: return None
    P = sp.Poly(poly, c)
    if P.degree() <= 0: return 0
    return P.count_roots(sp.Rational(433, 500), 1) - (1 if P.eval(1) == 0 else 0)
def check(points, positions, y0):
    # points: list of (y, sign); positions sorted
    P = [pt(y, sg) for (y, sg) in points]
    sub = {}
    for i in range(4): sub[X[i]] = P[i][0]; sub[Y[i]] = P[i][1]
    c0 = sp.expand(DET.subs(sub))
    g = [(sp.expand(GR[i][0].subs(sub)), sp.expand(GR[i][1].subs(sub))) for i in range(4)]
    ders = []
    for j in range(min(positions), max(positions)):
        if j not in positions and False: pass
        after = [i for i, (y, _) in enumerate(points) if y > j]
        if not after or len(after) == 4: continue
        Gx = sum(g[i][0] for i in after); Gy = sum(g[i][1] for i in after)
        ax, ay = pt(j, 1); bx, by = pt(j+1, 1)
        ux, uy = ax+bx, ay+by   # n_j is perpendicular to (a_j + a_{j+1})
        ders.append(sp.expand(ux*Gy - uy*Gx))  # = |u| * (n_j . G) up to sign
    E0 = eliminate(c0)
    Es = [eliminate(d) for d in ders]
    Es = [e for e in Es if e != 0]
    polys = ([E0] if E0 != 0 else []) + Es
    if not polys:
        return 'FAIL(all identically zero)', None
    gg = polys[0]
    for q in polys[1:]:
        gg = sp.gcd(gg, q)
    nr = roots_in_interval(gg)
    return ('ok' if nr == 0 else 'CHECK roots=%s' % nr), (E0 == 0)
types = []
for y0 in (0, 1):
    for sg in itertools.product((1, -1), repeat=4):
        types.append(('L4', y0, [(y0+i, sg[i]) for i in range(4)]))
    for sg in itertools.product((1, -1), repeat=2):
        types.append(('L3mid', y0, [(y0, sg[0]), (y0+1, 1), (y0+1, -1), (y0+2, sg[1])]))
        types.append(('L3left', y0, [(y0, 1), (y0, -1), (y0+1, sg[0]), (y0+2, sg[1])]))
        types.append(('L3right', y0, [(y0, sg[0]), (y0+1, sg[1]), (y0+2, 1), (y0+2, -1)]))
    types.append(('L2', y0, [(y0, 1), (y0, -1), (y0+1, 1), (y0+1, -1)]))
bad = 0; conc = 0
for name, y0, pts in types:
    positions = sorted({y for y, _ in pts})
    st, c0zero = check(pts, positions, y0)
    conc += bool(c0zero)
    if st != 'ok':
        bad += 1; print(name, y0, pts, st)
print('types checked:', len(types), ' identically-concyclic types:', conc, ' unresolved:', bad)
