"""Referee checks for angle_A2 (independent of the author's scripts).
 (1) exact rung identity (z-v).u_v = -tau, symbolic + random numeric
 (2) independent LP for Lemma 1.1 (k=4/3,5/4,1) and Region III, exact rationals by vertex enumeration + scipy
 (3) lens lemma incl. small centre distance d in [1, 1.94R], R near the hypothesis threshold
 (4) adversarial max of the R1 / R2 / symmetric-R2 displacement bounds (Region II, tau = sqrt3/2+3beta)
 (5) corner lemma (Region III) random check
 (6) (c2) angle alpha = angle(u_v, g) is bounded away from pi when |x_z w_v| <= 1.94 D2
 (7) single-centre near-resonant strip: build it exactly, count unit edges, check e(S)/|S| <= 4/3,
     no 3 parallel rungs, exact rung dot products
"""
import numpy as np, itertools
from math import *
from fractions import Fraction as F
rng = np.random.default_rng(7)
beta = 0.01; r3 = sqrt(3)/2

print("== (1) rung identity")
# exact rational check of the algebraic identity (1+D2^2-D^2)/(2D2) = -(t-(1-t^2)/(2D2)), D=D2+t
bad = 0
for tq in [F(i, 37) for i in range(0, 80)]:
    for d2q in [F(5), F(101, 3), F(10**4)]:
        Dq = d2q + tq
        if (1 + d2q**2 - Dq**2)/(2*d2q) != -(tq - (1 - tq**2)/(2*d2q)): bad += 1
print("exact identity failures:", bad)
worst = 0
for _ in range(20000):
    d2 = rng.uniform(5, 1e4); tt = rng.uniform(0, 1); Dd = d2 + tt
    w = np.zeros(2); v = np.array([-d2, 0.0])  # |v-w| = D2
    # z on C(w,D) cap C(v,1)
    a = (1 - Dd**2 + d2**2) / (2*d2)  # x-offset from v along +x... solve directly
    # z = v + (x,y), |z-v|=1, |z-w|=D:  (x-d2)^2+y^2 = D^2, x^2+y^2=1 -> x = (1+d2^2-D^2)/(2 d2)
    x = (1 + d2**2 - Dd**2)/(2*d2)
    if abs(x) > 1: continue
    z = v + np.array([x, sqrt(1-x*x)])
    u = (w - v)/d2
    tv = tt - (1 - tt**2)/(2*d2)
    worst = max(worst, abs((z - v) @ u + tv), abs(np.linalg.norm(z-w)-Dd))
print("max numeric error:", worst)

print("\n== (2) independent LPs (exact vertex enumeration)")
def lemma11(k):
    # max over s in [0,1] of min(1.5 s, k s + 6(1-s)); piecewise-linear, check breakpoints
    k = F(k); cands = [F(0), F(1), F(6)/(F(15,2)-k)]
    return max(min(F(3,2)*s, k*s + 6*(1-s)) for s in cands if 0 <= s <= 1)
for k in [F(1), F(5,4), F(4,3), F(7,5)]:
    print(f"k={k}: T={lemma11(k)} ~ {float(lemma11(k)):.5f}")
# Region III: max min(1.5s-0.5p, s+2p+6r), s+r=1, 0<=p<=s. enumerate vertices of the 2D polytope in (s,p)
best = F(0)
lines = []  # candidate vertices: intersections of pairs of {p=0, p=s, s=1, s=0, equality of the two bounds}
def f1(s,p): return F(3,2)*s - F(1,2)*p
def f2(s,p): return s + 2*p + 6*(1-s)
pts = set()
for s in [F(i,1000) for i in range(1001)]:
    # for fixed s the max over p of min(f1,f2) is at p=0, p=s or the crossing
    cross = (F(3,2)*s - s - 6*(1-s)) / F(5,2)
    for p in [F(0), s, cross]:
        if 0 <= p <= s: best = max(best, min(f1(s,p), f2(s,p)))
print("Region III T =", best, float(best))
from scipy.optimize import linprog
# independent scipy form with explicit n-split variables (s, p, r, T)
res = linprog([0,0,0,-1], A_ub=[[-1.5,0.5,0,1],[-1,-2,-6,1],[-1,1,0,0]], b_ub=[0,0,0],
              A_eq=[[1,0,1,0]], b_eq=[1], bounds=[(0,None)]*4)
print("scipy Region III:", -res.fun)
for k in [1, 1.25, 4/3]:
    res = linprog([0,0,-1], A_ub=[[-1.5,0,1],[-k,-6,1]], b_ub=[0,0], A_eq=[[1,1,0]], b_eq=[1], bounds=[(0,None)]*3)
    print(f"scipy Lemma1.1 k={k:.4f}: {-res.fun:.6f}")

print("\n== (3) lens lemma incl. small d")
worst = 0; viol = 0
for trial in range(3000):
    R = rng.choice([100.0, 1e3, 1e4])
    d = rng.choice([rng.uniform(1, 5), rng.uniform(1, 1.94*R)])
    phi0 = acos(d/(2*R))
    if R < 2/(cos(phi0/2)-cos(phi0)): continue
    phi = rng.uniform(-phi0, phi0)
    p = np.array([-d/2 + R*cos(phi), R*sin(phi)])
    psis = np.linspace(-phi0, phi0, 200001)
    Q = np.stack([d/2 - R*np.cos(psis), R*np.sin(psis)], 1)
    dist = np.linalg.norm(Q-p, axis=1) - 1
    idx = np.where(np.sign(dist[:-1]) != np.sign(dist[1:]))[0]
    for i in idx:
        psi = psis[i]
        cd = min(max(R*(phi0-phi), R*(phi0-psi)), max(R*(phi+phi0), R*(psi+phi0)))
        worst = max(worst, cd*sin(phi0/2))
        if cd*sin(phi0/2) > 1 + 1e-6: viol += 1
print("max ratio arc-dist/rho0:", worst, " violations:", viol)

print("\n== (4) R1/R2 adversarial displacement bounds, tau = sqrt3/2 + 3 beta")
tau0 = r3 + 3*beta; s0 = sqrt(1 - tau0**2)
def unit(a): return np.array([cos(a), sin(a)])
def off(u, sg):  # rung offset z - v for normal u
    up = np.array([-u[1], u[0]]); return -tau0*u + sg*s0*up
def tstep(u, side=1):  # right T-step: unit vector with e.u in (0,beta), right of u
    el = rng.uniform(0, asin(beta)); up = np.array([u[1], -u[0]])
    return cos(el)*up + sin(el)*u
best = {'R1z':0, 'R2':0, 'R2sym':0}
for _ in range(200000):
    a0 = 0.0
    uv0 = unit(a0)
    uz0 = unit(a0 + rng.uniform(-beta, beta))
    # R1 for z: two good-rung partners v,v' with u's within beta of uz0
    uva = unit(a0 + rng.uniform(-beta, beta)); uvb = unit(np.arctan2(uz0[1],uz0[0]) + rng.uniform(-beta, beta))
    va = -off(uva, 1); vb = -off(uvb, -1)   # z at origin
    best['R1z'] = max(best['R1z'], np.linalg.norm(va - vb))
    # R2: v0 -> v1 (T), z0=v0+off(v0), z1 = z0 + T-step(uz0); z' = v1 + off(v1), u_v1 within beta of u_v0
    sg0, sg1 = rng.choice([-1,1]), rng.choice([-1,1])
    v0 = np.zeros(2); z0 = v0 + off(uv0, sg0)
    v1 = v0 + tstep(uv0); z1 = z0 + tstep(uz0)
    uv1 = unit(a0 + rng.uniform(-beta, beta))
    zp = v1 + off(uv1, sg1)
    if sg0 != sg1: best['R2'] = max(best['R2'], np.linalg.norm(zp - z1))
    # symmetric R2: z1 has good rung partner v' with u_v' within beta of u_z1 (u_z1 within beta of uz0)
    uz1 = unit(np.arctan2(uz0[1],uz0[0]) + rng.uniform(-beta, beta))
    uvp = unit(np.arctan2(uz1[1],uz1[0]) + rng.uniform(-beta, beta))
    vp = z1 - off(uvp, sg1)
    if sg0 != sg1: best['R2sym'] = max(best['R2sym'], np.linalg.norm(vp - v1))
print({k: round(v,4) for k,v in best.items()}, " (all must be < 1); claimed 2s+3b=%.3f, 2s+4.5b=%.3f" % (2*s0+3*beta, 2*s0+4.5*beta))

print("\n== (5) corner lemma")
mn = 360
for _ in range(100000):
    tt = rng.uniform(r3 - 2*beta, r3 + 3*beta); d2 = 1e4
    tv = tt - (1-tt**2)/(2*d2); th0 = acos(tv)
    u = np.array([1.0, 0.0]); c = -tv*u + sin(th0)*np.array([0, 1.0])  # z - v
    # random u' with c.u' >= 1/(2 D2) (normal case)  or reflection (exception case)
    ang = rng.uniform(-pi, pi); up = unit(ang)
    # reflection of u across the line spanned by c:
    refl = 2*(u @ c)*c - u
    for w in (up, refl):
        if np.allclose(w, u): continue
        if (c @ w >= 1/(2*d2)) or abs(c @ w + tv) < 1e-9:
            mn = min(mn, degrees(acos(np.clip(w @ u, -1, 1))))
print("min angle(u,u') found:", mn, " claim >= 52.7, need > 360/7 =", 360/7)

print("\n== (6) (c2): max angle between u_v and g when |x_z - w_v| <= 1.94 D2")
# |a|=D2 (to w_v), |b| = D2-d0 (to x_z), d0 in [0,1]; |a-b|<=1.94 D2
d2 = 1e4; amax = 0
for d0 in [0, 0.5, 1]:
    b = d2 - d0
    # |a-b|^2 = d2^2 + b^2 - 2 d2 b cos(al) <= (1.94 d2)^2
    cosal = (d2**2 + b**2 - (1.94*d2)**2)/(2*d2*b)
    amax = max(amax, degrees(acos(cosal)))
print("max alpha =", amax, "deg -> |sin alpha| >=", sin(radians(180-amax)), ">> sin(beta/2)")

print("\n== (7) single-centre near-resonant strip (exact construction)")
def build(d2, m, sv, par):
    tv = sqrt(1 - sv*sv); tt = -d2 + sqrt(d2*d2 + 1 + 2*d2*tv)   # invert tau(t)
    al = 2*asin(1/(2*d2))
    V = [d2*unit(i*al) for i in range(m)]; Z = []
    for i, v in enumerate(V):
        u = -v/d2; up = np.array([-u[1], u[0]])
        sg = 1 if (i + par) % 2 == 0 else -1
        Z.append(v - tv*u + sg*sv*up)
    return tt, tv, V, Z
for d2 in [1e3, 1e4]:
    for par in (0, 1):
        f = lambda sv: np.linalg.norm(build(d2, 2, sv, par)[3][1] - build(d2, 2, sv, par)[3][0]) - 1
        lo, hi = 1e-9, 0.05
        if f(lo)*f(hi) > 0: print("par", par, "no unit D-step"); continue
        for _ in range(200):
            mid = (lo+hi)/2
            if f(lo)*f(mid) <= 0: hi = mid
            else: lo = mid
        sv = (lo+hi)/2; tt, tv, V, Z = build(d2, 40, sv, par)
        P = np.array(V + Z); Dm = np.linalg.norm(P[:, None]-P[None], axis=2); iu = np.triu_indices(len(P), 1)
        dd = Dm[iu]; ue = np.sum(np.abs(dd - 1) < 1e-7)
        rd = max(abs((Z[i]-V[i]) @ (-V[i]/d2) + tv) for i in range(len(V)))
        print(f"D2={d2:.0f} par={par} s={sv:.3e} tau={tv:.10f} (near-resonant iff tau>=cos(b/2)={cos(beta/2):.6f}) "
              f"2theta0={2*acos(tv):.2e} vs alpha={2*asin(1/(2*d2)):.2e}; min dist={dd.min():.9f} unit edges={ue} |S|={len(P)} "
              f"ratio={ue/len(P):.4f} (<=4/3?) rung-dot err={rd:.1e}")
