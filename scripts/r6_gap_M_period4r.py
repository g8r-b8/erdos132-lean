"""Coordinator's period-4 example + the second-layer point r (unit distance from a12 and a34, inner side).
Report: |a12-a34|, depth of r below the chord, reflex turning at r (a12 -> r -> a34), distances r to A,
turning of the layer-1 walk qL -> a12 -> r and r -> a34 -> qR, i.e. convexity of layer 1. mpmath 40 digits."""
import sys
from mpmath import mp, mpf, exp, asin, sqrt, arg, pi, conj
mp.dps = 40
def apex(a, b):
    c1 = a + (b-a)*exp(1j*pi/3); c2 = a + (b-a)*exp(-1j*pi/3)
    return c1 if abs(c1) < abs(c2) else c2
for R in [mpf(50), mpf(10**4), mpf(10**6)]:
    th = 2*asin(1/(2*R)); P = [R*exp(-1j*th*k) for k in range(4)]
    a12, a34 = apex(P[0], P[1]), apex(P[2], P[3])
    v = a34-P[3]; c1 = P[3]+v*exp(1j*pi/3); c2 = P[3]+v*exp(-1j*pi/3)
    qR = c1 if abs(c1-P[2]) > abs(c2-P[2]) else c2
    u = qR/abs(qR); mir = lambda z: u*u*conj(z)
    qL = mir(mir(qR))  # placeholder
    # qL = mirror of qR across the symmetry axis of the path (bisector of p2p3)
    w = (P[1]+P[2])/2; w = w/abs(w); qL = w*w*conj(qR)
    d = abs(a34-a12); m = (a12+a34)/2; h = sqrt(1-(d/2)**2); n = -m/abs(m); r = m + h*n
    turn = lambda x, y, z: -arg((z-y)/(y-x))   # >0 convex (clockwise traversal)
    print(f'R={float(R):.0e} |a12a34|={float(d):.9f} depth h={float(h):.6f} h*sqrt(R)={float(h*sqrt(R)):.4f}')
    print('   turning at r (neg=reflex):', float(turn(a12, r, a34)), ' x sqrt(R):', float(turn(a12, r, a34)*sqrt(R)))
    print('   turning at a12:', float(turn(qL, a12, r)), ' at a34:', float(turn(r, a34, qR)))
    print('   |qL a12|', float(abs(qL-a12)), ' dist r to A:', [float(abs(r-p)) for p in P], ' |r qR|', float(abs(r-qR)))
