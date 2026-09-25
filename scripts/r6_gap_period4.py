"""Coordinator sanity check (floats): curved 'period-4' first-layer ledger configuration.
A-points on circle radius R; path p1..p4 unit chords; rungs: p1->{qL, a12}, p2->a12, p3->a34, p4->{a34, qR};
qR = p4 + rot(a34-p4, -60deg) (clockwise, toward the gap); next path = mirror image across line O-qR."""
import math, cmath, sys
R = float(sys.argv[1]) if len(sys.argv) > 1 else 50.0
th = 2*math.asin(1/(2*R))
P = [R*cmath.exp(-1j*th*k) for k in range(4)]          # going clockwise (left->right on top of circle)
def apex(a, b):  # inward apex of equilateral triangle on a->b (inward = toward origin)
    c1 = a + (b-a)*cmath.exp(1j*math.pi/3); c2 = a + (b-a)*cmath.exp(-1j*math.pi/3)
    return c1 if abs(c1) < abs(c2) else c2
a12, a34 = apex(P[0], P[1]), apex(P[2], P[3])
v = a34 - P[3]
qR = P[3] + v*cmath.exp(1j*math.pi/3); qR2 = P[3] + v*cmath.exp(-1j*math.pi/3)
qR = qR if (qR - P[3]).real*0 + abs(qR - P[2]) > abs(qR2 - P[2]) else qR2   # away from p3
# mirror across line through 0 and qR
u = qR/abs(qR)
mir = lambda z: u*u*z.conjugate()
P2 = [mir(z) for z in reversed(P)]; b12, b34 = mir(a34), mir(a12)
pts = {'p1':P[0],'p2':P[1],'p3':P[2],'p4':P[3],'a12':a12,'a34':a34,'qR':qR,
       "p1'":P2[0],"p2'":P2[1],"p3'":P2[2],"p4'":P2[3],"b12":b12,"b34":b34}
names = list(pts)
print('gap d =', abs(P[3]-P2[0]), ' |a12-a34| =', abs(a12-a34), ' inside circle:', all(abs(pts[n])<R+1e-9 for n in names))
for i,x in enumerate(names):
    for y in names[i+1:]:
        d = abs(pts[x]-pts[y])
        if d < 1-1e-9: print('VIOLATION', x, y, d)
        elif abs(d-1) < 1e-9: print('edge', x, y)
