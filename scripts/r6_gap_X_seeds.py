"""Seeds for the symmetric band builder: first layers whose period closes exactly (R solved by bisection).
Family 'tri(N)': T-path p1..pN (unit chords on Gamma), inward equilateral apexes on edges 1,3,5,...;
the last point pN gets its extra rung qR = pN + rot(apex_last - pN, 60deg away from path) when N even
(when N odd the last edge has no apex; pN's two rungs form a triangle pN,x,qR with x = pN + rot(qR-pN)).
Next path = mirror image across line O-qR  =>  rotational period = 2*(arg(mid of path) - arg qR)."""
import cmath, math
def apex(a, b):
    c1 = a + (b-a)*cmath.exp(1j*math.pi/3); c2 = a + (b-a)*cmath.exp(-1j*math.pi/3)
    return c1 if abs(c1) < abs(c2) else c2
def away(p, v, awayfrom):
    z1 = p + v*cmath.exp(1j*math.pi/3); z2 = p + v*cmath.exp(-1j*math.pi/3)
    return z1 if abs(z1-awayfrom) > abs(z2-awayfrom) else z2
def tri_path(R, N):
    th = 2*math.asin(1/(2*R))
    P = [R*cmath.exp(-1j*th*k) for k in range(N)]
    B = []
    for k in range(0, N-1, 2):
        B.append(apex(P[k], P[k+1]))
    if N % 2 == 0:
        qR = away(P[-1], B[-1]-P[-1], P[-2])
    else:
        # last point: rung straight 'down-right-ish' triangle: x at 60deg below chord direction extension
        d = (P[-1]-P[-2])                      # chord direction
        x = P[-1] + d*cmath.exp(-1j*math.pi/3) if abs(P[-1] + d*cmath.exp(-1j*math.pi/3)) < R else P[-1] + d*cmath.exp(1j*math.pi/3)
        # x = inward direction at 60deg from the chord continuation: forms triangle-like wedge; make it a rung
        x = P[-1] + d*cmath.exp(-2j*math.pi/3) if abs(P[-1]+d*cmath.exp(-2j*math.pi/3)) < R else P[-1]+d*cmath.exp(2j*math.pi/3)
        B.append(x)
        qR = away(P[-1], x-P[-1], P[-2])
    mid = (P[0]+P[-1])/2
    period = 2*(cmath.phase(mid) - cmath.phase(qR))
    return P, B, qR, period
def solveR(N, M, lo=5.0, hi=5e4):
    f = lambda R: tri_path(R, N)[3] - 2*math.pi/M
    flo, fhi = f(lo), f(hi)
    for _ in range(200):
        mid = (lo*hi)**0.5
        fm = f(mid)
        if (fm > 0) == (flo > 0): lo, flo = mid, fm
        else: hi = mid
    return (lo*hi)**0.5
if __name__ == '__main__':
    for N in (2, 3, 4, 6):
        for R in (50, 500):
            P, B, qR, per = tri_path(R, N)
            print(N, R, 'period arc', per*R, 'gap', abs(P[-1]*cmath.exp(-1j*0)-P[0]*cmath.exp(-1j*per)))
