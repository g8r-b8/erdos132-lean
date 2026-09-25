#!/usr/bin/env python3
"""r6_below_cluster_search.py -- adversarial search for small R-clusters with Phi > 0 (report section C/O).

Flat model: K-row = line z = 0, D-row = line z = t (pinned), R (= int K) = {z < 0}.
All points pairwise >= 1; D-points have degree <= 3 (all nbrs in an open half-plane).
Every D-point is labelled S (adversarial).  For the R-cluster C:
    Phi(C) = sum_{y in C} (deg y + m_y - 6) = 2 e(C) + 2 e(C,S) - 6|C|,
so average v over C is 6 + Phi/|C|.  Conjecture C1 (report): Phi <= 0 for every cluster (=> 9/7 in Region I).
Proved (report P): average v <= 7 + o(1), i.e. Phi <= |C| up to O(1).
Beam search over rigid growth moves (intersections of unit circles with each other and with the two rows).
FLOAT screening only.
"""
import math, sys, itertools, random

EPS = 1e-7


def classify(z, t):
    if abs(z) < EPS:
        return 'K'
    if abs(z - t) < EPS:
        return 'D'
    if z < -EPS:
        return 'R'
    return None


def unit(p, q):
    return abs(math.hypot(p[0] - q[0], p[1] - q[1]) - 1) < 1e-6


def phi_score(pts, t):
    R = [p for p in pts if p[2] == 'R']
    tot = 0
    for y in R:
        deg = m = 0
        for q in pts:
            if q is y:
                continue
            if unit(y, q):
                deg += 1
                if q[2] != 'R':
                    m += 1
        tot += deg + m - 6
    return tot, len(R)


def valid_add(pts, c, t):
    for q in pts:
        d = math.hypot(c[0] - q[0], c[1] - q[1])
        if d < 1 - 1e-6:
            return False
    # D-degree <= 3 for c and its D-nbrs
    newlist = pts + [c]
    for d in newlist:
        if d[2] == 'D':
            if sum(1 for q in newlist if q is not d and unit(d, q)) > 3:
                return False
    return True


def candidates(pts, t):
    out = []
    n = len(pts)
    for i in range(n):
        p = pts[i]
        for zl in (0.0, t):
            dz = zl - p[1]
            if abs(dz) <= 1:
                dx = math.sqrt(max(0.0, 1 - dz * dz))
                for s in ((1, -1) if dx > 1e-9 else (1,)):
                    out.append((p[0] + s * dx, zl))
        for j in range(i + 1, n):
            q = pts[j]
            dx, dz = q[0] - p[0], q[1] - p[1]
            d = math.hypot(dx, dz)
            if d > 2 + 1e-9 or d < 1e-9:
                continue
            a = d / 2
            hh = math.sqrt(max(0.0, 1 - a * a))
            mx, mz = p[0] + dx / 2, p[1] + dz / 2
            ux, uz = -dz / d, dx / d
            for s in ((1, -1) if hh > 1e-9 else (1,)):
                out.append((mx + s * hh * ux, mz + s * hh * uz))
    res = []
    seen = set()
    for (x, z) in out:
        typ = classify(z, t)
        if typ is None:
            continue
        key = (round(x, 6), round(z, 6))
        if key in seen:
            continue
        seen.add(key)
        res.append((x, z, typ))
    return res


def canon(pts):
    xs = min(p[0] for p in pts)
    return tuple(sorted((round(p[0] - xs, 5), round(p[1], 5), p[2]) for p in pts))


BESTR = {}

def search(t, h, maxR=5, maxS=9, width=40, steps=14, seed=0):
    rnd = random.Random(seed)
    start = [(0.0, -h, 'R')]
    beam = [start]
    best = (-99, None)
    seenall = set()
    for step in range(steps):
        new = []
        for pts in beam:
            nR = sum(1 for p in pts if p[2] == 'R')
            nS = len(pts) - nR
            for c in candidates(pts, t):
                if c[2] == 'R' and nR >= maxR:
                    continue
                if c[2] != 'R' and nS >= maxS:
                    continue
                if not valid_add(pts, c, t):
                    continue
                npts = pts + [c]
                k = canon(npts)
                if k in seenall:
                    continue
                seenall.add(k)
                sc, r = phi_score(npts, t)
                new.append((sc, r, npts))
                # best over clusters with >= 1 R point, measured by Phi (and Phi/r)
                if sc > best[0] or (sc == best[0] and best[1] is not None and r > best[1][1]):
                    best = (sc, (sc, r, npts))
                BESTR[r] = max(BESTR.get(r, -99), sc)
        if not new:
            break
        # rank: Phi plus optimism for S-additions (S points only help) -> use Phi + 0.5*(#S)
        new.sort(key=lambda x: (x[0] + 0.3 * (len(x[2]) - x[1]) + 0.01 * rnd.random()), reverse=True)
        beam = [x[2] for x in new[:width]]
    return best


def main():
    ts = [0.02, 0.15, 0.3, 0.45, 0.5, 0.55, 0.62, 0.7, 0.78, 0.84]
    D2R = math.pi / 180
    overall = -99
    for t in ts:
        hs = sorted(set([round(math.cos(a * D2R), 6) for a in range(30, 91, 3)] +
                        ([round(math.sqrt(3) / 2 - t, 6)] if t < 0.866 else [])))
        if t >= 0.5:   # Dtype depths: psiK in [acos(1-t), 30+asin t]
            lo = math.degrees(math.acos(1 - t)); hi = 30 + math.degrees(math.asin(min(1, t)))
            hs += [math.cos((lo + (hi - lo) * k / 4) * D2R) for k in range(5)]
        hs = [h for h in hs if 0 < h <= 1]
        if t < 0.5:
            hs.append(math.cos((30 + math.degrees(math.asin(t))) * D2R))
        bt = (-99, None)
        for h in hs:
            b = search(t, h, maxR=int(sys.argv[1]) if len(sys.argv) > 1 else 4)
            if b[0] > bt[0]:
                bt = b
        sc, r, pts = bt[1]
        overall = max(overall, sc)
        print(f"t={t:.2f}: best Phi = {sc} with |C| = {r}  (avg v = {6 + sc / r:.3f});  #S = {len(pts) - r}")
    print("overall max Phi found:", overall)
    print("max Phi by |C| over all t:", dict(sorted(BESTR.items())))


if __name__ == '__main__':
    main()
