"""Pair-gap example: A on circle radius R, chords alternate 1 (T-edge) and L=1+eps (gap, non-edge).
c_j = inward apex (sides 1) over chord j. Tune eps so |c_j c_{j+1}| = 1. Report c-row turning at c_T, c_G.
mpmath high precision (floats only as sanity)."""
from mpmath import mp, mpf, mpc, exp, asin, sqrt, findroot, arg, pi, fabs
mp.dps = 40
import sys
R = mpf(sys.argv[1]) if len(sys.argv)>1 else mpf(10000)
def build(L):
    a1 = 2*asin(mpf(1)/(2*R)); aL = 2*asin(L/(2*R))
    angs = [0, -a1, -a1-aL, -2*a1-aL, -2*a1-2*aL]   # clockwise along top
    P = [R*exp(1j*t) for t in angs]
    def apex(p,q,):
        m=(p+q)/2; d=abs(q-p); h=sqrt(1-(d/2)**2); n=-m/abs(m); return m+h*n
    C=[apex(P[i],P[i+1]) for i in range(4)]
    return P,C
def f(L):
    P,C=build(L); return abs(C[1]-C[0])-1
L = findroot(f, mpf('1.0002'))
P,C=build(L)
print('R',R,'eps=L-1',L-1,' eps*R',(L-1)*R)
print('|c0c1|',abs(C[1]-C[0]),'|c1c2|',abs(C[2]-C[1]),'|c2c3|',abs(C[3]-C[2]))
def turn(a,b,c):  # exterior turning at b, positive = convex (clockwise traversal => right turn)
    return -arg((c-b)/(b-a))
print('A turning (x R):', turn(P[0],P[1],P[2])*R, turn(P[1],P[2],P[3])*R)
print('c-row turning at c1 (gap chord apex) xR:', turn(C[0],C[1],C[2])*R, ' at c2 (T apex) xR:', turn(C[1],C[2],C[3])*R)
# distances c to non-adjacent A
for j,c in enumerate(C):
    print('c%d dists to A:'%j, [float(abs(c-p)) for p in P])
