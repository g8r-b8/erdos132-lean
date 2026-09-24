# Independent referee checks (ref4) for N1N2_proof.md. Exact Fractions; trig via rigorous Taylor bounds.
from fractions import Fraction as F
import itertools, math
# (6) LP: lam*(1.5s-0.5p) + (1-lam)*(s+p+5r) with lam=8/11
lam=F(8,11)
cs=lam*F(3,2)+(1-lam); cp=-lam*F(1,2)+(1-lam); cr=(1-lam)*5
print("LP N1 w/ p:", cs, cp, cr); assert cs==F(15,11) and cr==F(15,11) and cp<=0
# optimality: dual check -- any lam: max(1+lam/2, 5(1-lam)) minimized at 8/11 >= 2/3
assert lam>=F(2,3)
# Region I (no p): same
print("LP N1 no p:", lam*F(3,2)+(1-lam), (1-lam)*5)
# N2: c=4: lam with 1+lam/2 = 4(1-lam) -> lam=2/3
l2=F(2,3); print("LP N2:", 1+l2/2, 4*(1-l2), -l2/2+(1-l2)); assert 1+l2/2==F(4,3)==4*(1-l2)
# rigorous trig bounds
def sin_lo(x):  # x>=0 small, Fraction
    return x - x**3/6
def sin_hi(x): return x - x**3/6 + x**5/120
def cos_lo(x): return 1 - x**2/2
PI_LO=F(314159265,10**8); PI_HI=F(314159266,10**8)
d05_lo=F(1,2)*PI_LO/180; d05_hi=F(1,2)*PI_HI/180
# Lemma T (i): 2+2/sin(0.5deg) < 232
v=2+2/sin_lo(d05_lo); print("apex arc bound <", float(v)); assert v<232
# tan(0.5deg) upper: sin/cos
tan05=sin_hi(d05_hi)/cos_lo(d05_hi)
wy=2/cos_lo(d05_hi)
tanphi=2*wy/400+4*tan05
cosphi_lo=1/ (1+tanphi**2) # 1/sqrt(1+x^2) >= 1/(1+x^2)
lhs=2*cosphi_lo-4*tan05-wy/10**4
print("fatness lhs >", float(lhs)); assert lhs>F(194,100)
W=wy+800*tan05; print("W <",float(W)); assert W<9
# packing for Lemma T: K in box L x W (L<400,W<9): n <= (401*10)/(pi/4)
print("Lemma T packing <=", float(F(401*10)*4/PI_LO), " vs 410^2=",410**2)
# diam-only bound would be 4*409.5^2:
print("diam-only packing 4*409.5^2 =", 4*409.5**2, "> 410^2 -> 410^2 needs box argument")
# BT multiplicity & count
M=(2*233.5)**2; print("M<=",M, "<=468^2", M<=468**2, "count<", 2*math.pi*468**2*50)
# N1 exceptional totals: max(465^2,410^2)+BT
print("N1 C1 approx", 2*math.pi*468**2*50+465**2, "< 7e7+2e5:", 2*math.pi*468**2*50+465**2 < 7e7+2e5)
# Lemma F arc: coarse 'cos psi > -eps' gives arc 180+2asin(eps); <240 needs eps<1/2, i.e. eps0<26.57deg, not pi/6
e0=math.pi/6-1e-9; print("eps0->pi/6: arc =",180+2*math.degrees(math.asin(math.tan(e0))), "deg (>240!)")
print("sharp form |psi|<90+eps0 gives arc", 180+2*30, "deg at eps0=pi/6 (open) -> OK")
# N2 (ii): min of 2 sin(a) sin(b), a in [30,91.15], b in [30,45.6]
eps=math.tan(1/50)
mn=min(2*math.sin(math.radians(a))*math.sin(math.radians(b)) for a in [30,90+math.degrees(math.asin(eps))] for b in [30,45.6])
print("N2(ii) min diff", mn, "> eps", eps)
