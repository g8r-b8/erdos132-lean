"""R3/OS angle, part A: exact-ish distance counts for candidate "far from cocircular" convex families.

Run with the repo venv (needs mpmath):  .venv/bin/python problems/132/scripts/r3_os_families.py [which]

All distances are computed at 60 significant digits with mpmath; two distances are identified when they agree to
1e-40 (relative).  Every family here is algebraic of bounded degree over Q(cos 2pi/N), so a spurious 1e-40
coincidence is not a realistic risk; still, the counts are "high-precision", not symbolic proofs.

Families
  reuleaux  : regular Reuleaux (2s+1)-gon, each arc cut into t equal steps (n = (2s+1)t).
  twoorbit  : R_N (radius 1) together with a rotated copy (angle pi/N) on radius rho in (cos(pi/N), 1);
              rho scanned over EVERY value at which some cross distance equals an outer or inner chord
              (the only rho where D can drop).  Reports min_rho D.
  arcs2     : two regular arcs of the SAME circle but different step angles (cocircular control).
  lattice   : convex hull vertices of Z^2 / Eisenstein integers in a disc (exact integer squared distances).
"""
import sys, itertools
from collections import Counter
import mpmath as mp
mp.mp.dps = 60
TOL = mp.mpf(10) ** -40


def D_profile(pts):
    """pts: list of (x, y) mpf. Returns (D, sorted multiplicity list by distance, #rare)."""
    n = len(pts)
    ds = sorted(mp.sqrt((a[0]-b[0])**2 + (a[1]-b[1])**2) for a, b in itertools.combinations(pts, 2))
    groups = []
    for d in ds:
        if groups and abs(d - groups[-1][0]) < TOL * max(1, d):
            groups[-1][1] += 1
        else:
            groups.append([d, 1])
    mult = [g[1] for g in groups]
    return len(groups), mult, sum(1 for x in mult if x <= n), [g[0] for g in groups]


def strictly_convex(pts):
    n = len(pts)
    s = []
    for i in range(n):
        a, b, c = pts[i], pts[(i+1) % n], pts[(i+2) % n]
        s.append((b[0]-a[0])*(c[1]-b[1]) - (b[1]-a[1])*(c[0]-b[0]))
    return all(x > 0 for x in s) or all(x < 0 for x in s)


def max_cocircular(pts):
    n = len(pts); best = 0
    if n > 40:
        return None
    for i, j, k in itertools.combinations(range(n), 3):
        (x1, y1), (x2, y2), (x3, y3) = pts[i], pts[j], pts[k]
        dd = 2*(x1*(y2-y3) + x2*(y3-y1) + x3*(y1-y2))
        if abs(dd) < TOL: continue
        ux = ((x1*x1+y1*y1)*(y2-y3) + (x2*x2+y2*y2)*(y3-y1) + (x3*x3+y3*y3)*(y1-y2)) / dd
        uy = ((x1*x1+y1*y1)*(x3-x2) + (x2*x2+y2*y2)*(x1-x3) + (x3*x3+y3*y3)*(x2-x1)) / dd
        r2 = (x1-ux)**2 + (y1-uy)**2
        c = sum(1 for p in pts if abs((p[0]-ux)**2 + (p[1]-uy)**2 - r2) < TOL*max(1, r2))
        best = max(best, c)
    return best


def reuleaux(s, t):
    M = 2*s + 1
    R = mp.mpf(1)/2 / mp.sin(mp.pi*s/M)
    V = [(R*mp.cos(2*mp.pi*i/M + mp.pi/2), R*mp.sin(2*mp.pi*i/M + mp.pi/2)) for i in range(M)]
    pts = []
    # boundary order: arc opposite vertex i runs from V[i+s] to V[i+s+1]; list arcs in order of their start
    arcs = []
    for i in range(M):
        a, b, c = V[(i+s) % M], V[(i+s+1) % M], V[i]
        th0 = mp.atan2(a[1]-c[1], a[0]-c[0]); th1 = mp.atan2(b[1]-c[1], b[0]-c[0])
        dth = th1 - th0
        while dth > mp.pi: dth -= 2*mp.pi
        while dth < -mp.pi: dth += 2*mp.pi
        arcs.append(((i+s) % M, [(c[0]+mp.cos(th0+dth*j/t), c[1]+mp.sin(th0+dth*j/t)) for j in range(t)]))
    arcs.sort()
    for _, a in arcs: pts += a
    return pts


def run_reuleaux():
    print("# Reuleaux (2s+1)-gon, arcs cut into t steps: n, D, D-n/2, k=#rare, max#cocircular")
    for s in range(1, 6):
        for t in range(1, 7):
            P = reuleaux(s, t); n = len(P)
            if n > 44: continue
            D, mult, k, _ = D_profile(P)
            print("s=%d t=%d n=%2d D=%3d D-n/2=%5.1f k=%3d cocirc=%s convex=%s" % (
                s, t, n, D, D - n/2, k, max_cocircular(P), strictly_convex(P)), flush=True)


def twoorbit(N, rho, phi=None):
    phi = mp.pi/N if phi is None else phi
    P = []
    for i in range(N):
        a = 2*mp.pi*i/N
        P.append((mp.cos(a), mp.sin(a)))
        P.append((rho*mp.cos(a+phi), rho*mp.sin(a+phi)))
    return P


def run_twoorbit(Nmax=40):
    print("# two dihedral orbits R_N + rho*R_N rotated pi/N, n=2N.  min over coincidence values of rho")
    for N in range(4, Nmax+1):
        lo = mp.cos(mp.pi/N); hi = mp.mpf(1)
        chords = [2*mp.sin(mp.pi*j/N) for j in range(1, N//2+1)]
        cands = set()
        # cross distance e_k^2 = 1 + rho^2 - 2 rho cos(theta_k), theta_k = (2k+1)pi/N
        for k in range(N):
            ct = mp.cos((2*k+1)*mp.pi/N)
            for c in chords:
                # e_k = c :  rho^2 - 2ct rho + 1 - c^2 = 0
                disc = ct*ct - 1 + c*c
                if disc >= 0:
                    for r in (ct + mp.sqrt(disc), ct - mp.sqrt(disc)):
                        if lo < r < hi: cands.add(mp.nstr(r, 45))
                # e_k = rho c : rho^2 (1 - c^2) - 2ct rho + 1 = 0
                A = 1 - c*c
                if abs(A) > TOL:
                    disc = ct*ct - A
                    if disc >= 0:
                        for r in ((ct + mp.sqrt(disc))/A, (ct - mp.sqrt(disc))/A):
                            if lo < r < hi: cands.add(mp.nstr(r, 45))
        for c1 in chords:
            for c2 in chords:
                r = c1/c2
                if lo < r < hi: cands.add(mp.nstr(r, 45))
        best = None
        for rs in cands:
            r = mp.mpf(rs)
            P = twoorbit(N, r)
            if not strictly_convex(P): continue
            D, mult, k, _ = D_profile(P)
            if best is None or D < best[0]: best = (D, k, r)
        # generic rho for reference
        Dg, _, kg, _ = D_profile(twoorbit(N, (lo+hi)/2 + mp.mpf(1)/(10**7 * 7)))
        print("N=%2d n=%2d  generic D=%3d (D-n/2=%3d)  best D=%3d (D-n/2=%3d, k=%3d) at rho=%s  #cands=%d" % (
            N, 2*N, Dg, Dg-N, best[0], best[0]-N, best[1], mp.nstr(best[2], 12), len(cands)), flush=True)


def run_lattice():
    print("# convex hull vertices of lattice points in a disc (exact integer arithmetic)")
    for name, basis in (("Z2", ((1, 0), (0, 1))), ("Eis", ((2, 0), (1, 1)))):  # Eisenstein scaled: x-axis 2, (1, sqrt3)->use norm form
        for R in (5, 10, 20, 40, 80):
            if name == "Z2":
                pts = [(x, y) for x in range(-R, R+1) for y in range(-R, R+1) if x*x + y*y <= R*R]
                q = lambda a, b: (a[0]-b[0])**2 + (a[1]-b[1])**2
                cart = lambda p: (p[0], p[1])
            else:
                # Eisenstein integer a + b w, norm a^2 - ab + b^2
                pts = [(a, b) for a in range(-2*R, 2*R+1) for b in range(-2*R, 2*R+1) if a*a - a*b + b*b <= R*R]
                q = lambda u, v: (u[0]-v[0])**2 - (u[0]-v[0])*(u[1]-v[1]) + (u[1]-v[1])**2
                cart = lambda p: (p[0] - p[1]/2.0, p[1]*3**0.5/2)
            # monotone chain hull, strict
            P = sorted(set(pts), key=lambda p: cart(p))
            def cross(o, a, b):
                o, a, b = cart(o), cart(a), cart(b)
                return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
            lower, upper = [], []
            for p in P:
                while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 1e-9: lower.pop()
                lower.append(p)
            for p in reversed(P):
                while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 1e-9: upper.pop()
                upper.append(p)
            H = lower[:-1] + upper[:-1]; n = len(H)
            c = Counter(q(a, b) for a, b in itertools.combinations(H, 2))
            D = len(c); k = sum(1 for v in c.values() if v <= n)
            print("%s R=%3d n=%3d D=%4d D-n/2=%6.1f k=%4d  max class=%d" % (name, R, n, D, D-n/2, k, max(c.values())), flush=True)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("reuleaux", "all"): run_reuleaux()
    if which in ("twoorbit", "all"): run_twoorbit(int(sys.argv[2]) if len(sys.argv) > 2 else 30)
    if which in ("lattice", "all"): run_lattice()
