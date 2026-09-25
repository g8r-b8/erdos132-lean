#!/usr/bin/env python3
"""r6_below_rule_check.py -- adversarial test of the Region-I discharging rules (report P4) in the flat model.

Generates configurations by the rigid growth moves of r6_below_cluster_search.py, but the beam now MAXIMISES
the largest final charge after discharging (and, as tie-break, the number of heavy points).  For every visited
configuration the rules are applied and we check  final(y) <= 7  for every R-point y.
Rules (flat model; directions psi measured from the upward normal at the sender):
  A    (K at +-30, deg 6)           : 1/2 to each nbr at +-150
  B    (S cap D at +-30, deg 6)     : 1/2 to each nbr at +-150
  C    (D at phi, K at phi-60, deg 6; mirror): 1/2 to the nbrs at phi+120 and phi+180
  A'   (K at +-60, R-D at 0 [absent here], deg 6, m 2): 1 to the nbr at 180
  cap  (K at +-60, D at 0, deg 6, m 3): 1 to 180, 1/2 to each of +-120
  Dtype(deg 5, m 3 = K,K,D)          : 1/2 to each of its two R-nbrs
  forward: an R point with v = 7 that received charge passes all of it to its nbr opposite its unique K-nbr.
FLOAT screening only.
"""
import math, sys, random
import importlib.util, os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("cs", os.path.join(HERE, "r6_below_cluster_search.py"))
cs = importlib.util.module_from_spec(spec); spec.loader.exec_module(cs)

TOLA = 1.0   # degrees tolerance for slot recognition (flat model is exact; 1 deg is generous)


def ang(y, q):
    return math.degrees(math.atan2(q[0] - y[0], q[1] - y[1]))   # 0 = up (+z), positive = +x side


def near(a, b, tol=TOLA):
    d = abs((a - b + 180) % 360 - 180)
    return d <= tol


def run_rules(pts, t):
    R = [p for p in pts if p[2] == 'R']
    nbrs = {id(p): [q for q in pts if q is not p and cs.unit(p, q)] for p in pts}
    v = {}
    for y in R:
        nb = nbrs[id(y)]
        v[id(y)] = len(nb) + sum(1 for q in nb if q[2] != 'R')
    charge = dict(v)
    recv = {id(y): 0.0 for y in R}
    unknown = []

    def send(y, direction, amt):
        for q in nbrs[id(y)]:
            if q[2] == 'R' and near(ang(y, q), direction):
                charge[id(y)] -= amt; charge[id(q)] += amt; recv[id(q)] += amt
                return True
        return False

    for y in R:
        if v[id(y)] < 8:
            continue
        nb = nbrs[id(y)]
        K = [ang(y, q) for q in nb if q[2] == 'K']
        Dd = [ang(y, q) for q in nb if q[2] == 'D']
        deg = len(nb)
        ok = False
        if deg == 6 and len(K) == 2 and all(near(abs(k), 30) for k in K):
            ok = send(y, 150, .5) & send(y, -150, .5)
        elif deg == 6 and len(Dd) == 2 and not K and all(near(abs(d), 30) for d in Dd):
            ok = send(y, 150, .5) & send(y, -150, .5)
        elif deg == 6 and len(K) == 1 and len(Dd) == 1:
            phi, k = Dd[0], K[0]
            if near(k, phi - 60):
                ok = send(y, phi + 120, .5) & send(y, phi + 180, .5)
            elif near(k, phi + 60):
                ok = send(y, phi - 120, .5) & send(y, phi + 180, .5)
        elif deg == 6 and len(K) == 2 and all(near(abs(k), 60) for k in K) and len(Dd) == 1:
            ok = send(y, 180, 1) & send(y, 120, .5) & send(y, -120, .5)
        elif deg == 6 and len(K) == 2 and all(near(abs(k), 60) for k in K) and not Dd:
            ok = send(y, 180, 1)
        elif deg == 5 and len(K) == 2 and len(Dd) == 1:
            rr = [q for q in nb if q[2] == 'R']
            for q in rr:
                charge[id(y)] -= .5; charge[id(q)] += .5; recv[id(q)] += .5
            ok = len(rr) == 2
        if not ok:
            unknown.append((round(t, 3), v[id(y)], deg, [round(k) for k in K], [round(d) for d in Dd]))
    # forwarding (one round suffices: targets have depth > 1.3, m = 0, v <= 6)
    for y in R:
        if v[id(y)] == 7 and recv[id(y)] > 1e-12:
            nb = nbrs[id(y)]
            K = [ang(y, q) for q in nb if q[2] == 'K']
            if len(K) != 1 or len(nb) != 6:
                unknown.append(('fwd', v[id(y)], len(nb), K)); continue
            amt = recv[id(y)]
            if not send(y, K[0] + 180, amt):
                unknown.append(('fwd-miss',))
    mx = max((charge[id(y)] for y in R), default=0)
    nheavy = sum(1 for y in R if v[id(y)] >= 8)
    return mx, nheavy, unknown


STATS = {'heavycfg': 0, 'maxheavy': 0, 'types': 0}

def search(t, h, maxR, maxS=11, width=50, steps=17, seed=1):
    rnd = random.Random(seed)
    beam = [[(0.0, -h, 'R')]]
    seen = set(); worst = (0, None); unk = []
    for step in range(steps):
        new = []
        for pts in beam:
            nR = sum(1 for p in pts if p[2] == 'R'); nS = len(pts) - nR
            for c in cs.candidates(pts, t):
                if (c[2] == 'R' and nR >= maxR) or (c[2] != 'R' and nS >= maxS):
                    continue
                if not cs.valid_add(pts, c, t):
                    continue
                npts = pts + [c]
                k = cs.canon(npts)
                if k in seen:
                    continue
                seen.add(k)
                mx, nh, u = run_rules(npts, t)
                STATS['heavycfg'] += (nh > 0); STATS['maxheavy'] = max(STATS['maxheavy'], nh)
                STATS['types'] += 0
                unk += u
                if mx > worst[0]:
                    worst = (mx, npts)
                new.append((mx + 0.2 * nh + 0.05 * (len(npts) - nR) + 0.01 * rnd.random(), npts))
        if not new:
            break
        new.sort(key=lambda x: x[0], reverse=True)
        beam = [x[1] for x in new[:width]]
    return worst, unk, len(seen)


def main():
    maxR = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    D2R = math.pi / 180
    tot_worst = 0; tot_seen = 0; allunk = []
    for t in [0.02, 0.2, 0.35, 0.45, 0.49, 0.5, 0.51, 0.56, 0.63, 0.7, 0.77, 0.84]:
        hs = [math.cos(a * D2R) for a in range(30, 91, 6)] + [math.sqrt(3) / 2 - t if t < 0.86 else 0.5]
        if t >= 0.5:
            lo = math.degrees(math.acos(1 - t)); hi = 30 + math.degrees(math.asin(min(1, t)))
            hs += [math.cos((lo + (hi - lo) * k / 3) * D2R) for k in range(4)]
        else:
            hs.append(math.cos((30 + math.degrees(math.asin(t))) * D2R))
        wt = 0
        for h in hs:
            if not (0 < h <= 1):
                continue
            (w, pts), unk, ns = search(t, h, maxR)
            wt = max(wt, w); tot_seen += ns; allunk += unk
        tot_worst = max(tot_worst, wt)
        print(f"t={t:.2f}: max final charge over visited configs = {wt:.3f}")
    print("configs visited:", tot_seen, " max final charge:", tot_worst)
    print("configs with >=1 heavy point:", STATS["heavycfg"], " max #heavy in one config:", STATS["maxheavy"])
    print("unclassified heavy / forwarding anomalies:", len(allunk), allunk[:8])


if __name__ == '__main__':
    main()
