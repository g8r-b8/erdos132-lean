"""(1) symbolic identity behind the Lipschitz lemma; (2) random float sanity check;
(3) exact m=4 exclusion of the symmetric pattern [b-1, X, b, b, X, b-1]."""
import sympy as sp, random, math
R,rho,g=sp.symbols('R rho gamma',positive=True)
f2=R**2+rho**2-2*R*rho*sp.cos(g)
expr=4*R**2*f2-f2**2-4*R**2*rho**2*sp.sin(g)**2
print("identity:", sp.simplify(sp.expand(expr-(R**2-rho**2)*(3*R**2+rho**2-4*R*rho*sp.cos(g))).rewrite(sp.cos)))
# (2) random: |beta(f(a1))-beta(f(a2))| < |a1-a2|
worst=0
for _ in range(200000):
    r=random.random()**0.5*0.999; ph=random.uniform(0,2*math.pi)
    a1=random.uniform(0,2*math.pi); a2=a1+random.uniform(-math.pi,math.pi)
    def B(a):
        f=math.hypot(math.cos(a)-r*math.cos(ph), math.sin(a)-r*math.sin(ph))
        return 2*math.asin(min(1,f/2))
    q=abs(B(a1)-B(a2))/max(1e-15,abs(a1-a2)); worst=max(worst,q)
print("max ratio (should be <1):", worst)
# (3) m=4, R_9, U = 0..5, axis through vertex 7 (cap vertex opposite midpoint of 2,3). w = t*e^{i*7*th}
th=2*sp.pi/9; t=sp.symbols('t',real=True)
def d2(j): return 1+t**2-2*t*sp.cos(sp.Rational(1)*(7-j)*th)
def c2(j): return 2-2*sp.cos(j*th)
for b in (2,3,4):
    sols=sp.solve(sp.Eq(d2(2)-d2(0), c2(b)-c2(b-1)), t)
    for s in sols:
        v=sp.nsimplify(s)
        res=sp.N(d2(0).subs(t,s)-c2(b-1),30)
        print("b=",b," t=",sp.N(s,20)," residual d(u0)^2-c_{b-1}^2 =",res)
