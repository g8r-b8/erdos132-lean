# exploratory: rigid chain of distinct-centre singleton gaps (G >= 2); all pair distances
from mpmath import mp, mpf, sqrt, cos, sin, asin, pi
mp.dps = 50
def chain(R, G, n=4):
    x = asin(G/(2*R)); th0 = pi/6 + x; tau = cos(th0); s = sin(th0)
    t = sqrt(R*R + 2*R*tau + 1) - R; Dl = R + t
    gam = -2*x
    V, Z, W = [], [], []
    ang = pi/2  # u_0 direction
    v = (mpf(0), mpf(0))
    for j in range(n):
        u = (cos(ang), sin(ang)); iu = (-u[1], u[0])
        V.append(v); W.append((v[0]+R*u[0], v[1]+R*u[1]))
        z = (v[0]-tau*u[0]+s*iu[0], v[1]-tau*u[1]+s*iu[1])
        Z.append(z)
        ang2 = ang + gam
        u2 = (cos(ang2), sin(ang2)); iu2 = (-u2[1], u2[0])
        v = (z[0]+tau*u2[0]+s*iu2[0], z[1]+tau*u2[1]+s*iu2[1])  # z - v' = -tau u' - s iu'
        ang = ang2
    return V, Z, W, Dl, t, tau
def d(a,b): return sqrt((a[0]-b[0])**2+(a[1]-b[1])**2)
R = mpf(10)**4
for G in [2, 2.5, 3, 4, 5, 5.7]:
    V,Z,W,Dl,t,tau = chain(R, mpf(G), 5)
    print('G=%s Rd~%.3f t=%.6f tau-sqrt3/2=%.3e'%(G, float(R*(2*sin(pi/6+asin(mpf(G)/(2*R)))-1)), float(t), float(tau-sqrt(3)/2)))
    print('  |v0v1|=%.12f |z0v0|=%.12f |z0v1|=%.12f |z0z1|=%.6f |w0w1|=%.6f'%(d(V[0],V[1]),d(Z[0],V[0]),d(Z[0],V[1]),d(Z[0],Z[1]),d(W[0],W[1])))
    print('  |z0w0|-D=%.2e |z0w1|-D=%.2e |z0w2|-R=%.6f |z0w2|-D=%.6f |z1 w0|-R=%.6f |z0 w3|-R=%.4f'%(d(Z[0],W[0])-Dl, d(Z[0],W[1])-Dl, d(Z[0],W[2])-R, d(Z[0],W[2])-Dl, d(Z[1],W[0])-R, d(Z[0],W[3])-R))
    print('  |v0w1|-R=%.3e |v0w2|-R=%.3e |v2 w0|-R=%.3e'%(d(V[0],W[1])-R, d(V[0],W[2])-R, d(V[2],W[0])-R))
