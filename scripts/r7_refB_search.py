#!/usr/bin/env python3
"""r7_refB_search.py -- REF_B adversarial beam search on the OFF-LATTICE flat model of Region II (float screen).

Independent engine (no reuse of B/B1 code). Flat model at given t in [sqrt3/2 + 0.03, 1]:
  rows: K-row z = 0 (labels 'K' in S, 'Rb' = R on dK), D-row z = t (pinned; 'DS' in S, 'DR' = R cap D),
  interior z < 0 ('R'); nothing with 0 < z < t or z > t. Points pairwise >= 1; unit pairs = edges.
Growth: add points at unit distance from two existing points (circle-circle) or from one point on a row line,
random labels; beam keeps configurations maximising (max final charge, #forwarding 7-points, total load pressure).
Rules = branch B section 3: A (deg 6, S-nbrs = K at +-30) sends 1/2 to +-150 nbrs; D_II (deg 5, m 3, K,K,DS) sends
1/2 to its two R-nbrs; a v = 7 R-point that received forwards everything to the nbr opposite its unique S-nbr.
Anomalies recorded: unclassified heavy (v >= 8), heavy receiver, forwarding shape failure (not deg 6 / S-nbr not K /
no opposite nbr), forward target that is itself a forwarder, final charge > 7.
"""
import math, random, sys, collections
EPS = 1e-9
MODE = sys.argv[3] if len(sys.argv) > 3 else 'heavy'
STATS = {'maxload': 0.0, 'maxload7': 0.0}
SQ3 = math.sqrt(3)


def psi(p, q):  # direction of q seen from p, degrees from vertical (+z), clockwise positive toward +x
    return math.degrees(math.atan2(q[0] - p[0], q[1] - p[1]))


def angdiff(a, b):
    d = abs((a - b) % 360.0)
    return min(d, 360 - d)


def run(pts, t):
    """pts: list of (x, z, label). returns (maxfinal, anomalies, stats)"""
    n = len(pts)
    nb = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            d = math.hypot(pts[i][0] - pts[j][0], pts[i][1] - pts[j][1])
            if abs(d - 1) < 1e-7:
                nb[i].append(j); nb[j].append(i)
    isS = [p[2] in ('K', 'DS') for p in pts]
    Rs = [i for i in range(n) if not isS[i]]
    v = {i: len(nb[i]) + sum(1 for j in nb[i] if isS[j]) for i in Rs}
    ch = {i: float(v[i]) for i in Rs}
    recv = collections.defaultdict(float)
    an = []; heavy = collections.Counter()
    for i in Rs:
        if v[i] < 8:
            continue
        if pts[i][2] == 'DR':
            an.append(('heavy R cap D', i)); continue
        Kn = [j for j in nb[i] if pts[j][2] == 'K']
        Dn = [j for j in nb[i] if pts[j][2] == 'DS']
        Ka = sorted(psi(pts[i], pts[j]) for j in Kn)
        if len(nb[i]) == 6 and len(Kn) == 2 and len(Dn) == 0 and abs(Ka[0] + 30) < 0.2 and abs(Ka[1] - 30) < 0.2:
            heavy['A'] += 1
            tg = [j for j in nb[i] if angdiff(psi(pts[i], pts[j]), 150) < 0.3 or angdiff(psi(pts[i], pts[j]), -150) < 0.3]
            if len(tg) != 2 or any(isS[j] for j in tg):
                an.append(('A targets', i)); continue
            for j in tg:
                ch[i] -= .5; ch[j] += .5; recv[j] += .5
        elif len(nb[i]) == 5 and len(Kn) == 2 and len(Dn) == 1:
            heavy['D_II'] += 1
            tg = [j for j in nb[i] if not isS[j]]
            if len(tg) != 2 or any(pts[j][2] != 'R' for j in tg):
                an.append(('D_II targets', i, [pts[j][2] for j in tg])); continue
            for j in tg:
                ch[i] -= .5; ch[j] += .5; recv[j] += .5
        else:
            an.append(('unclassified heavy', i, v[i], len(nb[i]), Ka, [psi(pts[i], pts[j]) for j in Dn]))
    fwd = 0
    forwarders = set()
    for i in Rs:
        if recv[i] > 0 and v[i] >= 8:
            an.append(('heavy receiver', i))
        if recv[i] > 0 and v[i] == 7:
            forwarders.add(i)
    for i in forwarders:
        Sn = [j for j in nb[i] if isS[j]]
        if len(nb[i]) != 6 or len(Sn) != 1 or pts[Sn[0]][2] != 'K':
            an.append(('fwd shape', i)); continue
        b = psi(pts[i], pts[Sn[0]])
        tg = [j for j in nb[i] if angdiff(psi(pts[i], pts[j]), b + 180) < 0.3]
        if len(tg) != 1:
            an.append(('fwd no target', i)); continue
        if tg[0] in forwarders or isS[tg[0]]:
            an.append(('fwd target bad', i)); continue
        amt = recv[i]; ch[i] -= amt; ch[tg[0]] += amt; fwd += 1
        if amt > 0.5 + EPS:
            an.append(('7-point received > 1/2', i, amt))
    mx = max(ch.values()) if ch else 0
    if mx > 7 + 1e-9:
        an.append(('FINAL > 7', mx))
    load = max((ch[i] - v[i] for i in Rs if recv[i] > 0 and i not in forwarders), default=0)
    load7 = max((recv[i] for i in forwarders), default=0)
    STATS['maxload'] = max(STATS['maxload'], load); STATS['maxload7'] = max(STATS['maxload7'], load7)
    return mx, an, heavy, fwd, (load, load7) if MODE == 'load' else load


def admissible(p, pts, t):
    x, z = p
    for q in pts:
        if (q[0] - x) ** 2 + (q[1] - z) ** 2 < (1 - 1e-7) ** 2:
            return False
    return True


def row_label(z, t, rnd):
    if abs(z) < 1e-9:
        return rnd.choice(['K', 'K', 'Rb'])
    if abs(z - t) < 1e-9:
        return rnd.choice(['DS', 'DS', 'DR'])
    if z < -1e-9:
        return 'R'
    return None


def candidates(pts, t, rnd, cx, rad=float(sys.argv[4]) if len(sys.argv) > 4 else 3.2):
    out = []
    P = [p for p in pts if abs(p[0] - cx) < rad + 1]
    for i in range(len(P)):
        a = P[i]
        # unit circle of a with rows
        for zr in (0.0, t):
            dz = zr - a[1]
            if abs(dz) <= 1:
                dx = math.sqrt(max(0.0, 1 - dz * dz))
                out.append((a[0] + dx, zr)); out.append((a[0] - dx, zr))
        # random interior direction (downward-ish)
        ang = rnd.uniform(90, 270)
        out.append((a[0] + math.sin(math.radians(ang)), a[1] + math.cos(math.radians(ang))))
        for j in range(i + 1, len(P)):
            b = P[j]
            dx, dz = b[0] - a[0], b[1] - a[1]
            d2 = dx * dx + dz * dz
            if d2 > 4 or d2 < 1e-12:
                continue
            d = math.sqrt(d2); hgt = math.sqrt(max(0.0, 1 - d2 / 4))
            mx, mz = a[0] + dx / 2, a[1] + dz / 2
            out.append((mx - dz / d * hgt, mz + dx / d * hgt)); out.append((mx + dz / d * hgt, mz - dx / d * hgt))
    res = []
    for (x, z) in out:
        if abs(x - cx) > rad or z < -3.2:
            continue
        if abs(z) < 1e-7: z = 0.0
        if abs(z - t) < 1e-7: z = t
        if not (z <= 0 or z == t):
            continue
        res.append((x, z))
    return res


def seed(t, kind, h, sgn):
    pts = []
    if kind == 'D_II':
        y = (0.0, -h)
        pK = math.degrees(math.acos(h))
        for s in (1, -1):
            pts.append((math.sin(math.radians(s * pK)), 0.0, 'K'))
        cD = h + t
        aD = sgn * math.degrees(math.acos(min(1.0, cD)))
        pts.append((math.sin(math.radians(aD)), -h + math.cos(math.radians(aD)), 'DS'))
        pts.append((y[0], y[1], 'Rb' if h == 0 else 'R'))
        # its two receivers: extremes of I or symmetric
        for a in (pK + 60, 300 - pK):
            pts.append((math.sin(math.radians(a)), -h + math.cos(math.radians(a)), 'R'))
    else:  # A
        h = SQ3 / 2
        for a in (-30, 30):
            pts.append((math.sin(math.radians(a)), 0.0, 'K'))
        pts.append((0.0, -h, 'R'))
        for a in (90, -90, 150, -150):
            pts.append((math.sin(math.radians(a)), -h + math.cos(math.radians(a)), 'R'))
    return pts


def score(pts, t):
    mx, an, heavy, fwd, load = run(pts, t)
    if MODE == 'load':
        return (mx, load, sum(heavy.values()), fwd), an, heavy
    return (mx, sum(heavy.values()), fwd, load), an, heavy


def main():
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    STEPS = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    rnd = random.Random(2026)
    tmin = SQ3 / 2 + 0.03
    tot = collections.Counter(); ANS = []; best = 0; nconf = 0; maxheavy = 0; maxfwd = 0
    for t in (tmin, 0.92, 0.95, 0.98, 1.0):
        for kind, h, sg in ([('A', None, 1)] + [('D_II', hh, s) for hh in (0.0, (1 - t) / 2, 1 - t) for s in (1, -1)]):
            start = seed(t, kind, h, sg)
            beam = [start]
            for step in range(STEPS):
                pool = []
                for conf in beam:
                    cands = candidates(conf, t, rnd, 0.0)
                    rnd.shuffle(cands)
                    for (x, z) in cands[:25]:
                        if not admissible((x, z), conf, t):
                            continue
                        lab = row_label(z, t, rnd)
                        if lab is None:
                            continue
                        new = conf + [(x, z, lab)]
                        sc, an, hv = score(new, t)
                        nconf += 1; tot.update(hv)
                        maxheavy = max(maxheavy, sum(hv.values())); maxfwd = max(maxfwd, sc[2] if MODE != 'load' else sc[3])
                        if an:
                            ANS.append((t, kind, an[:3]))
                        best = max(best, sc[0])
                        pool.append((sc, rnd.random(), new))
                pool.sort(key=lambda q: (q[0], q[1]), reverse=True)
                beam = [q[2] for q in pool[:W]] or beam
        print(f"t={t:.4f}: running max final charge {best:.6f}, configs {nconf}", flush=True)
    print("configs evaluated:", nconf, " max final charge:", best, " max #heavy/config:", maxheavy,
          " max #forwarders/config:", maxfwd)
    print("heavy occurrences:", dict(tot), " max receiver load (non-forwarder):", STATS['maxload'],
          " max 7-point receipt:", STATS['maxload7'])
    kinds = collections.Counter(a[0] for x in ANS for a in x[2])
    print("anomalies:", len(ANS), dict(kinds))
    for x in ANS[:5]:
        print("  ", x)


if __name__ == '__main__':
    main()
