# exploratory (floats/mpmath): singleton gap geometry, centres w, w'
from mpmath import mp, mpf, sqrt, cos, sin, asin, acos, pi, findroot, matrix
mp.dps = 40
def rot(a, x): return (cos(a)*x[0]-sin(a)*x[1], sin(a)*x[0]+cos(a)*x[1])
def perp(x): return (-x[1], x[0])
def add(*xs): return (sum(x[0] for x in xs), sum(x[1] for x in xs))
def mul(c,x): return (c*x[0], c*x[1])
def nrm(x): return sqrt(x[0]**2+x[1]**2)
R = mpf(10)**4
for Rd in [0.3, 0.866, 1.0, 1.5, 1.8, 2.0, 2.5, 3, 4, 4.9, -0.5, -1, -2, -3, -4.9]:
    d = mpf(Rd)/R
    s = (1+d)/2
    tau = sqrt(1-s*s)
    th0 = acos(tau)
    for sig in [1, -1]:
        u = (mpf(0), mpf(1)); v = (mpf(0), mpf(0))
        z = add(v, mul(-tau,u), mul(sig*s, perp(u)))
        def f(g):
            up = rot(g, u)
            vp = add(z, mul(tau, up), mul(sig*s, perp(up)))  # z - v' = -tau u' - sig s u'^perp
            return nrm(add(vp, mul(-1, v))) - 1
        # search small g
        best = None
        for g0 in [mpf(k)/R for k in range(-20, 21)]:
            try:
                g = findroot(f, g0)
                if abs(g) < 0.01:
                    best = g; break
            except Exception: pass
        if best is None: print(Rd, sig, 'none'); continue
        g = best
        up = rot(g, u); vp = add(z, mul(tau, up), mul(sig*s, perp(up)))
        w = add(v, mul(R, u)); wp = add(vp, mul(R, up))
        ww = nrm(add(wp, mul(-1, w)))
        gg = 2*R*sin(abs(g)/2)
        a1 = nrm(add(vp, mul(-1, w))) - R; a2 = nrm(add(v, mul(-1, wp))) - R
        print('Rd=%5s sig=%2d gamma*R=%.6f  g=%.6f |ww\'|=%.6f  |v\'w|-R=%.3e |vw\'|-R=%.3e' % (Rd, sig, float(g*R), float(gg), float(ww), float(a1), float(a2)))
