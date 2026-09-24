"""R4-global: adversarial float sanity test of Theorem G.
C = regular k-gon with unit side (k=320: turning 2pi/k < 0.0201 per vertex, convex, deg<=3 automatic).
Grow a penny graph inside by random greedy placement at unit-circle intersections (min dist >= 1),
restricted to a band near C (width w), biased to maximise contacts.  Report Def(G0) - 2k where
G0 = component containing C, plus min over components P of G1 of Def(P) - p_P.  Floats: sanity only."""
import math, random, sys, numpy as np
from collections import defaultdict
TOL = 1e-7
def run(k, w, npts, seed, greedy):
    rnd = random.Random(seed)
    R = 0.5 / math.sin(math.pi / k)
    pts = [complex(R * math.cos(2 * math.pi * j / k), R * math.sin(2 * math.pi * j / k)) for j in range(k)]
    grid = defaultdict(list)
    def key(z): return (math.floor(z.real), math.floor(z.imag))
    for i, z in enumerate(pts): grid[key(z)].append(i)
    def near(z, r=2):
        a, b = key(z)
        for dx in range(-r, r + 1):
            for dy in range(-r, r + 1):
                yield from grid.get((a + dx, b + dy), ())
    apo = R * math.cos(math.pi / k)
    def inside(z):  # strictly inside polygon, and in band
        ang = math.atan2(z.imag, z.real) % (2 * math.pi / k) - math.pi / k
        rr = abs(z)
        return rr * math.cos(ang) < apo - 1e-6 and rr > R - w
    def ok(z):
        return inside(z) and all(abs(z - pts[j]) >= 1 - TOL for j in near(z))
    def cands_from(i):
        out = []
        for j in near(pts[i]):
            if j == i: continue
            d = abs(pts[j] - pts[i])
            if d < 2 - 1e-9 and d > 1e-9:
                a = d / 2; h = math.sqrt(1 - a * a); e = (pts[j] - pts[i]) / d
                base = pts[i] + a * e
                out += [base + 1j * h * e, base - 1j * h * e]
        return out
    for _ in range(npts):
        best = None
        for _t in range(40):
            i = rnd.randrange(len(pts))
            cs = cands_from(i)
            rnd.shuffle(cs)
            for z in cs:
                if ok(z):
                    c = sum(1 for j in near(z) if abs(abs(z - pts[j]) - 1) < TOL)
                    if best is None or c > best[0] or (not greedy and rnd.random() < 0.3):
                        best = (c, z)
                    break
        if best is None: break
        z = best[1]; grid[key(z)].append(len(pts)); pts.append(z)
    n = len(pts); P = np.array(pts)
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in near(pts[i]):
            if j > i and abs(abs(pts[j] - pts[i]) - 1) < TOL:
                adj[i].append(j); adj[j].append(i)
    # component of C
    seen = [-1] * n
    def comp(s, lab, allowed):
        st = [s]; seen[s] = lab; out = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if seen[y] == -1 and allowed(y):
                    seen[y] = lab; st.append(y); out.append(y)
        return out
    G0 = comp(0, 0, lambda y: True)
    E0 = sum(len(adj[x]) for x in G0) // 2
    Def0 = 3 * len(G0) - E0
    # components of G1 = G0 - C
    inG1 = set(G0) - set(range(k)); seen = [-1] * n
    worst = None; m = 0; lab = 0
    for x in sorted(inG1):
        if seen[x] == -1:
            lab += 1
            Pc = comp(x, lab, lambda y: y in inG1)
            E = sum(1 for a in Pc for b in adj[a] if b in inG1) // 2
            p = sum(1 for a in Pc for b in adj[a] if b < k)
            m += p
            val = 3 * len(Pc) - E - p
            worst = val if worst is None else min(worst, val)
    Cdeg = [len(adj[i]) for i in range(k)]
    return dict(k=k, n=n, G0=len(G0), m=m, maxCdeg=max(Cdeg), Def0=Def0, Def0_minus_2k=Def0 - 2 * k,
                ncomp_G1=lab, min_DefP_minus_p=worst)
if __name__ == '__main__':
    k = 320
    for w in [1.8, 2.6, 4.0, 7.0]:
        for seed in range(3):
            for greedy in [True, False]:
                r = run(k, w, 2500, seed, greedy)
                print(w, seed, greedy, r)
