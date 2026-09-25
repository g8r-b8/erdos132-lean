import sympy as sp
x = sp.symbols('x', positive=True)  # x = 1/R
R = 1/x
p = sp.sqrt(4*R**2-1)
D = (p + sp.sqrt(3))/2
c = p/(2*R); s1 = 1/(2*R)
Y = R*(D**2-R**2)/(2*D)
rad = R**2 - (Y - D*s1)**2
X_minus = D*c - sp.sqrt(rad)
X_plus = D*c + sp.sqrt(rad)
cosA = c**2 - s1**2; sinA = 2*s1*c
v0 = (R*cosA, -R*sinA)
for name, X in [('minus', X_minus), ('plus', X_plus)]:
    E = D**2 - ((X - v0[0])**2 + (Y - v0[1])**2)
    Ew = D**2 - (X**2 + Y**2)
    print(name, 'E series:', sp.series(sp.simplify(E), x, 0, 3))
    print(name, 'D^2-|y|^2 series:', sp.series(sp.simplify(Ew), x, 0, 1))
