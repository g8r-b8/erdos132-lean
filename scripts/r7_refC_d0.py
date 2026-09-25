"""REF_C (R7): d = 0 (tau = sqrt3/2) double triangle in one E_w: z1..z4 consecutive (alpha1) on C(w,Delta),
apex v of base z1z2 on C(w,R).  If X cap C(w,Delta) has >= 4 points, the cone lemma forces every Delta_2-partner y of z2
(2nd point) to satisfy |y z1| = Delta.  Candidates y in C(z1,Delta) cap C(z2,R): check y+ is > Delta from w and
y- is at distance in (R, Delta) from the apex v.  Scaling of the margin |y- - v| - R with R (80 digits)."""
from mpmath import mp, mpf, sqrt, sin, cos, asin
mp.dps = 80
def pol(r, th): return (r * cos(th), r * sin(th))
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def nrm(a): return sqrt(a[0] ** 2 + a[1] ** 2)
def inter(c1, r1, c2, r2):
    d = nrm(sub(c2, c1)); a = (r1 * r1 - r2 * r2 + d * d) / (2 * d); h = sqrt(r1 * r1 - a * a)
    e = ((c2[0] - c1[0]) / d, (c2[1] - c1[1]) / d); m = (c1[0] + a * e[0], c1[1] + a * e[1])
    return [(m[0] - h * e[1], m[1] + h * e[0]), (m[0] + h * e[1], m[1] - h * e[0])]
for k in range(4, 16, 2):
    R = mpf(10) ** k; tau = sqrt(3) / 2
    t = -R + sqrt(R * R + 1 + 2 * R * tau); D = R + t
    a1 = 2 * asin(1 / (2 * D))
    z1, z2 = pol(D, a1), pol(D, 2 * a1); v = pol(R, mpf(3) / 2 * a1); w = (mpf(0), mpf(0))
    assert abs(nrm(sub(v, z1)) - 1) < mpf(10) ** -60 and abs(nrm(sub(v, z2)) - 1) < mpf(10) ** -60
    out = []
    for y in inter(z1, D, z2, R):
        out.append((nrm(sub(y, w)) - D, nrm(sub(y, v)) - R, D - nrm(sub(y, v))))
    out.sort(key=lambda x: -x[0])
    (pw, _, _), (mw, mvR, mvD) = out
    print('R=1e%-3d y+: |y-w|-Delta = %s ;  y-: |y-w|-Delta = %s, |y-v|-R = %s (R*that = %s), Delta-|y-v| = %s' % (
        k, mp.nstr(pw, 6), mp.nstr(mw, 6), mp.nstr(mvR, 8), mp.nstr(R * mvR, 10), mp.nstr(mvD, 6)))
