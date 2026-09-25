#!/usr/bin/env python3
"""r7_B_lattice_t1.py -- EXACT integer model of the Region II flat limit at t = 1 (tau = 1, top of Region II).

Sites: x = a/2 (integer a), rows: D-row z = 1 (row -1), K-row z = 0 (row 0), interior rows z = -j*sqrt3/2 (j >= 1),
parity a = j (mod 2) for j >= 1, a even for rows -1, 0.  Unit pairs are exact: same row |dx| = 1; rows j, j+1 with
j >= 0 and |dx| = 1/2; D-row/K-row with dx = 0 (a radial rung, allowed exactly at tau = 1).  D-row to interior
distances are irrational, hence never 1.  All points are >= 1 apart automatically.  D-points have degree <= 3.
Labels: K-row: 'K' (S cap dK) or 'Rb' (R on dK) or empty; D-row: 'DS' (S cap D) or 'DR' (R cap D) or empty;
interior: 'R' or empty.  Directions psi (from the upward normal) are exact lattice directions.
Rules (report section 3): A (deg 6, K at +-30) sends 1/2 to +-150;  D_II (deg 5, m 3, K,K,D) sends 1/2 to each
of its two R-nbrs;  a v = 7 R-point that received charge forwards all of it to its nbr opposite its unique K.
Checks: max final charge <= 7, heavy types only A / D_II, v <= 8, receivers light, no forwarding anomaly.
"""
import random, sys, collections
from fractions import Fraction as F

DIRS = {(2, 0): 90, (-2, 0): -90, (1, 1): 30, (-1, 1): -30, (1, -1): 150, (-1, -1): -150, (0, 'up'): 0, (0, 'dn'): 180}

def nbr_dirs(p):
    a, j = p
    out = []
    for da in (2, -2):
        out.append(((a + da, j), 90 if da > 0 else -90))
    if j >= 0:     # down to row j+1
        for da in (1, -1):
            out.append(((a + da, j + 1), 150 if da > 0 else -150))
    if j >= 1:     # up to row j-1
        for da in (1, -1):
            out.append(((a + da, j - 1), 30 if da > 0 else -30))
    if j == 0:
        out.append(((a, -1), 0))
    if j == -1:
        out.append(((a, 0), 180))
    return out

def run(conf):
    S = {p for p, l in conf.items() if l in ('K', 'DS')}
    R = [p for p, l in conf.items() if l in ('Rb', 'DR', 'R')]
    nb = {p: [(q, d) for q, d in nbr_dirs(p) if q in conf] for p in conf}
    for p, l in conf.items():
        if l in ('DS', 'DR'):
            assert len(nb[p]) <= 3
    v = {y: len(nb[y]) + sum(1 for q, _ in nb[y] if q in S) for y in R}
    ch = {y: F(v[y]) for y in R}; recv = collections.defaultdict(F)
    anomalies = []; types = collections.Counter()
    def give(y, q, amt):
        ch[y] -= amt; ch[q] += amt; recv[q] += amt
    for y in R:
        if v[y] < 8:
            continue
        Kd = sorted(d for q, d in nb[y] if conf[q] == 'K'); Dd = [d for q, d in nb[y] if conf[q] == 'DS']
        if len(nb[y]) == 6 and Kd == [-30, 30]:
            types['A'] += 1
            for q, d in nb[y]:
                if d in (150, -150):
                    assert conf[q] == 'R'; give(y, q, F(1, 2))
        elif len(nb[y]) == 5 and len(Kd) == 2 and len(Dd) == 1:
            types['D_II'] += 1
            rr = [q for q, d in nb[y] if q not in S]
            assert len(rr) == 2 and all(conf[q] == 'R' for q in rr)
            for q in rr:
                give(y, q, F(1, 2))
        else:
            anomalies.append(('heavy', y, v[y], Kd, Dd))
    for y in R:
        if recv[y] > 0:
            if v[y] >= 8:
                anomalies.append(('heavy receiver', y))
            if v[y] == 7:
                Kn = [(q, d) for q, d in nb[y] if q in S]
                if len(nb[y]) != 6 or len(Kn) != 1 or conf[Kn[0][0]] != 'K':
                    anomalies.append(('fwd-shape', y)); continue
                opp = (Kn[0][1] + 360) % 360 - 180
                tgt = [q for q, d in nb[y] if d == opp]
                if len(tgt) != 1 or v[tgt[0]] >= 7:
                    anomalies.append(('fwd-target', y)); continue
                amt = recv[y]; ch[y] -= amt; ch[tgt[0]] += amt
    mx = max(ch.values(), default=0)
    return mx, types, anomalies, max(v.values(), default=0), sum(v.values()), len(R)

def random_conf(rnd, W, depth):
    conf = {}
    pK = rnd.choice([0.6, 0.75, 0.9]); pD = rnd.choice([0.2, 0.5, 0.8]); pR = rnd.choice([0.7, 0.85, 1.0])
    for a in range(0, 2 * W, 2):
        u = rnd.random()
        if u < pK: conf[(a, 0)] = 'K'
        elif u < pK + (1 - pK) * 0.7: conf[(a, 0)] = 'Rb'
        u = rnd.random()
        if u < pD: conf[(a, -1)] = 'DS' if rnd.random() < 0.85 else 'DR'
    for j in range(1, depth + 1):
        for a in range(j % 2, 2 * W, 2):
            if rnd.random() < pR: conf[(a, j)] = 'R'
    # D-degree <= 3 holds automatically; drop D-points with no S-neighbour? not required.
    return conf

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rnd = random.Random(7)
    worst = F(0); T = collections.Counter(); A = []; maxv = 0; maxheavy = 0; ratios = []
    for it in range(N):
        conf = random_conf(rnd, rnd.randint(4, 14), rnd.randint(1, 5))
        mx, types, an, mv, sv, nr = run(conf)
        worst = max(worst, mx); T.update(types); A += an; maxv = max(maxv, mv)
        maxheavy = max(maxheavy, sum(types.values()))
    # structured: periodic D_II pattern  ... K Rb K Rb ...  with DS above every Rb, full interior
    for W in (6, 10, 20):
        for depth in (1, 2, 3, 6):
            conf = {}
            for a in range(0, 4 * W, 2):
                conf[(a, 0)] = 'Rb' if (a // 2) % 2 else 'K'
                if (a // 2) % 2: conf[(a, -1)] = 'DS'
            for j in range(1, depth + 1):
                for a in range(j % 2, 4 * W, 2): conf[(a, j)] = 'R'
            mx, types, an, mv, sv, nr = run(conf)
            worst = max(worst, mx); T.update(types); A += an
            ratios.append((W, depth, F(sv, nr), mx))
    print("random configs:", N, " max raw v:", maxv, " max #heavy in one config:", maxheavy)
    print("heavy types:", dict(T))
    print("max final charge (exact):", worst)
    print("anomalies:", len(A), A[:5])
    print("periodic D_II lattice (W, depth, avg v, max final):", [(w, d, str(r), str(m)) for w, d, r, m in ratios])

if __name__ == '__main__':
    main()
