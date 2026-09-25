# exploratory: G=1 strip, z_2's possible Delta2-partners (must be diametral to z_1 or z_3)
from mpmath import mp, mpf, sqrt, cos, sin, asin, pi
mp.dps = 50
def d(a,b): return sqrt((a[0]-b[0])**2+(a[1]-b[1])**2)
def circ_inter(c1, r1, c2, r2):
    dd = d(c1,c2); a = (r1*r1 - r2*r2 + dd*dd)/(2*dd); h = sqrt(r1*r1 - a*a)
    ex = ((c2[0]-c1[0])/dd, (c2[1]-c1[1])/dd)
    p = (c1[0]+a*ex[0], c1[1]+a*ex[1])
    return [(p[0]-h*ex[1], p[1]+h*ex[0]), (p[0]+h*ex[1], p[1]-h*ex[0])]
for R in [mpf(10)**4, mpf(10)**6]:
    p_ = sqrt(4*R*R-1); Dl = (p_+sqrt(3))/2; a2 = 2*asin(1/(2*R))
    w = (mpf(0), mpf(0))
    V = [(R*cos(j*a2), R*sin(j*a2)) for j in range(6)]
    Z = [(Dl*cos((j+mpf(1)/2)*a2), Dl*sin((j+mpf(1)/2)*a2)) for j in range(5)]
    for (i, k) in [(1,0),(1,2),(0,1),(2,1)]:
        for y in circ_inter(Z[i], R, Z[k], Dl):
            dw = d(y,w)
            ds = [d(y,z) for z in Z]; dv = [d(y,v) for v in V]
            bad = [('z',j,float(x-R)) for j,x in enumerate(ds) if R < x < Dl - mpf(10)**-30] + [('v',j,float(x-R)) for j,x in enumerate(dv) if R < x < Dl- mpf(10)**-30]
            print('R=%.0e partner of z%d diam to z%d: |yw|=%.3f (<=D? %s) viol(in (R,D)):'%(R,i,k,float(dw), dw<=Dl), bad[:6])
