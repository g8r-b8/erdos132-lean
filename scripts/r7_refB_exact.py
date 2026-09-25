#!/usr/bin/env python3
"""r7_refB_exact.py -- REF_B EXACT adversarial test of branch B's Region II discharging (flat limit), in Q(sqrt3).

All coordinates lie in Q(sqrt3); distances^2 are compared with 1 EXACTLY (sign of a + b sqrt3 decided exactly).
Region II t-values with rational s = sqrt(1 - t^2) (so off-radial rungs are exact): t = 12/13, 24/25, 1, and
t = 24/25 - 100/2501 = 0.92... for the h > 0 gadget.
Families:
  F1  (h = 0 lattice, any Pythagorean t): K-row x in Z (labels K / Rb / empty), D-row points at (x +- s, t) above
      chosen K-row sites (labels DS / DR), interior rows z = -j sqrt3/2, x = j/2 mod 1 (random occupancy).
  F2  (h > 0 D_II gadget, psiK = arccos(100/2501) = 87.7 deg): y at depth h, K at (+-2499/2501, 0), DS at (7/25, t),
      receivers at the ends of I, then random EXACT growth by equilateral-triangle completion (rotation by +-60 deg,
      closed in Q(sqrt3)), K-row / D-row translations by +-1, with random labels.
  F3  (two D_II senders sharing a receiver region, A next to D_II): hand-built exact stress configurations.
Engine: exact version of B section 3 rules (A: deg 6, S-nbrs = two K at exactly +-30 deg; D_II: deg 5, m 3, K,K,DS;
forwarding of v = 7 receivers to the nbr opposite their unique S-nbr). Reports max final charge (exact Fraction),
heavy types, anomalies (unclassified heavy, heavy receivers, forwarding failures, 7-point receipt > 1/2, final > 7).
"""
import random, sys, collections, itertools
from fractions import Fraction as F


class Q3:
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = F(a); self.b = F(b)

    def __add__(s, o): o = o if isinstance(o, Q3) else Q3(o); return Q3(s.a + o.a, s.b + o.b)
    __radd__ = __add__

    def __sub__(s, o): o = o if isinstance(o, Q3) else Q3(o); return Q3(s.a - o.a, s.b - o.b)

    def __rsub__(s, o): return Q3(o) - s

    def __neg__(s): return Q3(-s.a, -s.b)

    def __mul__(s, o):
        o = o if isinstance(o, Q3) else Q3(o)
        return Q3(s.a * o.a + 3 * s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__

    def sign(s):
        a, b = s.a, s.b
        if b == 0: return (a > 0) - (a < 0)
        if a == 0: return (b > 0) - (b < 0)
        if a > 0 and b > 0: return 1
        if a < 0 and b < 0: return -1
        # opposite signs: compare a^2 with 3 b^2
        d = a * a - 3 * b * b
        return (1 if a > 0 else -1) * ((d > 0) - (d < 0))

    def __eq__(s, o): o = o if isinstance(o, Q3) else Q3(o); return s.a == o.a and s.b == o.b

    def __hash__(s): return hash((s.a, s.b))

    def f(s): return float(s.a) + float(s.b) * 1.7320508075688772


R3H = Q3(0, F(1, 2))  # sqrt3/2
HALF = Q3(F(1, 2))


def rot60(v, sgn):  # rotate vector by +-60 deg
    x, z = v; c = HALF; s = R3H if sgn > 0 else -R3H
    return (x * c - z * s, x * s + z * c)


def d2(p, q):
    dx = p[0] - q[0]; dz = p[1] - q[1]
    return dx * dx + dz * dz


def key(p): return (p[0], p[1])


def run(pts):
    """pts: dict (x,z) -> label. Exact."""
    P = list(pts.keys()); n = len(P); lab = [pts[p] for p in P]
    nb = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            s = (d2(P[i], P[j]) - 1).sign()
            if s < 0:
                raise ValueError('points closer than 1')
            if s == 0:
                nb[i].append(j); nb[j].append(i)
    isS = [l in ('K', 'DS') for l in lab]
    Rs = [i for i in range(n) if not isS[i]]
    v = {i: len(nb[i]) + sum(isS[j] for j in nb[i]) for i in Rs}
    ch = {i: F(v[i]) for i in Rs}; recv = collections.defaultdict(F)
    an = []; hv = collections.Counter()
    for i in Rs:
        if v[i] < 8: continue
        Kn = [j for j in nb[i] if lab[j] == 'K']; Dn = [j for j in nb[i] if lab[j] == 'DS']
        vec = lambda j: (P[j][0] - P[i][0], P[j][1] - P[i][1])
        if len(nb[i]) == 6 and len(Kn) == 2 and not Dn and sorted([vec(j)[0].f() for j in Kn]) == [-0.5, 0.5] \
                and all(vec(j)[1] == R3H for j in Kn):
            hv['A'] += 1
            tg = [j for j in nb[i] if vec(j)[1] == -R3H]
            if len(tg) != 2 or any(isS[j] for j in tg): an.append(('A targets', P[i])); continue
            for j in tg: ch[i] -= F(1, 2); ch[j] += F(1, 2); recv[j] += F(1, 2)
        elif len(nb[i]) == 5 and len(Kn) == 2 and len(Dn) == 1:
            hv['D_II'] += 1
            tg = [j for j in nb[i] if not isS[j]]
            if len(tg) != 2 or any(lab[j] != 'R' for j in tg): an.append(('D_II targets', P[i])); continue
            for j in tg: ch[i] -= F(1, 2); ch[j] += F(1, 2); recv[j] += F(1, 2)
        else:
            an.append(('unclassified heavy', P[i], v[i], len(nb[i]), len(Kn), len(Dn), lab[i]))
    fw = [i for i in Rs if recv[i] > 0 and v[i] == 7]
    for i in Rs:
        if recv[i] > 0 and v[i] >= 8: an.append(('heavy receiver', P[i]))
    nfw = 0
    for i in fw:
        Sn = [j for j in nb[i] if isS[j]]
        if len(nb[i]) != 6 or len(Sn) != 1 or lab[Sn[0]] != 'K': an.append(('fwd shape', P[i])); continue
        tgt = (2 * P[i][0] - P[Sn[0]][0], 2 * P[i][1] - P[Sn[0]][1])
        tj = [j for j in nb[i] if P[j] == tgt]
        if len(tj) != 1 or tj[0] in fw or isS[tj[0]]: an.append(('fwd target', P[i])); continue
        if recv[i] > F(1, 2): an.append(('7-pt receipt > 1/2', P[i], recv[i]))
        ch[i] -= recv[i]; ch[tj[0]] += recv[i]; nfw += 1
    mx = max(ch.values()) if ch else F(0)
    if mx > 7: an.append(('FINAL > 7', mx))
    load = max((recv[i] for i in Rs if recv[i] > 0 and i not in fw), default=F(0))
    # receivers' total incoming (including forwarded)
    tot_in = collections.defaultdict(F)
    for i in Rs:
        tot_in[i] = ch[i] - v[i] + (recv[i] if i in fw else 0)
    maxin = max(tot_in.values(), default=F(0))
    return mx, an, hv, nfw, maxin, sum(v.values()), len(Rs)


def admissible(p, pts):
    return all((d2(p, q) - 1).sign() >= 0 for q in pts)


def fam1(rnd, t, s):
    pts = {}
    W = rnd.randint(4, 12); depth = rnd.randint(1, 4)
    pK = rnd.choice([0.5, 0.65, 0.8])
    for x in range(W):
        u = rnd.random()
        if u < pK: pts[(Q3(x), Q3(0))] = 'K'
        elif u < pK + 0.8 * (1 - pK): pts[(Q3(x), Q3(0))] = 'Rb'
    Dsites = [x for x in range(W) if rnd.random() < 0.5]
    for x in Dsites:
        sg = rnd.choice([1, -1])
        p = (Q3(x) + sg * s, Q3(t))
        if admissible(p, pts):
            pts[p] = 'DS' if rnd.random() < 0.8 else 'DR'
    pR = rnd.choice([0.75, 0.9, 1.0])
    for j in range(1, depth + 1):
        for k in range(-1, W + 1):
            x = Q3(k) + (Q3(F(1, 2)) if j % 2 else Q3(0))
            p = (x, Q3(0, -F(j, 2)))
            if rnd.random() < pR and admissible(p, pts):
                pts[p] = 'R'
    return pts


def gadget2():
    h = F(100, 2501); sK = F(2499, 2501); t = F(24, 25) - h
    y = (Q3(0), Q3(-h))
    pts = {y: 'R', (Q3(sK), Q3(0)): 'K', (Q3(-sK), Q3(0)): 'K', (Q3(F(7, 25)), Q3(t)): 'DS'}
    # receivers at psiK + 60 and 300 - psiK: rotate the K vectors by +-60 (away from the top)
    vK = (Q3(sK), Q3(h)); vKm = (Q3(-sK), Q3(h))
    a1 = rot60(vK, -1)    # psi increases clockwise (from +z toward +x): psiK + 60
    a2 = rot60(vKm, +1)   # 300 - psiK
    for a in (a1, a2):
        if a[1].f() > 0:
            raise RuntimeError('orientation')
        pts[(y[0] + a[0], y[1] + a[1])] = 'R'
    return pts, t


def grow(rnd, pts, t, steps):
    for _ in range(steps):
        P = list(pts.keys())
        cands = []
        for p, q in itertools.combinations(P, 2):
            if (d2(p, q) - 1).sign() == 0:
                for sg in (1, -1):
                    v = rot60((q[0] - p[0], q[1] - p[1]), sg)
                    cands.append((p[0] + v[0], p[1] + v[1]))
        for p in P:
            if pts[p] in ('K', 'Rb', 'DS', 'DR'):
                for dx in (1, -1):
                    cands.append((p[0] + dx, p[1]))
        rnd.shuffle(cands)
        for c in cands[:30]:
            z = c[1]
            if z == Q3(t):
                lab = 'DS' if rnd.random() < 0.8 else 'DR'
            elif z == Q3(0):
                lab = rnd.choice(['K', 'K', 'Rb'])
            elif z.sign() < 0 and (z - Q3(-3)).sign() > 0 and abs(c[0].f()) < 4:
                lab = 'R'
            else:
                continue
            if c not in pts and admissible(c, pts):
                pts[c] = lab
                break
    return pts


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rnd = random.Random(11)
    worst = F(0); T = collections.Counter(); AN = []; maxin = F(0); maxfw = 0; maxhv = 0; n = 0
    for (t, s) in ((F(12, 13), F(5, 13)), (F(24, 25), F(7, 25)), (F(1), F(0))):
        for _ in range(N):
            pts = fam1(rnd, t, s)
            mx, an, hv, nfw, mi, sv, nr = run(pts); n += 1
            worst = max(worst, mx); T.update(hv); AN += an; maxin = max(maxin, mi); maxfw = max(maxfw, nfw)
            maxhv = max(maxhv, sum(hv.values()))
        print(f"F1 t={t}: worst so far {worst}", flush=True)
    for _ in range(max(1, N // 6)):
        pts, t = gadget2()
        pts = grow(rnd, pts, t, rnd.randint(5, 22))
        mx, an, hv, nfw, mi, sv, nr = run(pts); n += 1
        worst = max(worst, mx); T.update(hv); AN += an; maxin = max(maxin, mi); maxfw = max(maxfw, nfw)
        maxhv = max(maxhv, sum(hv.values()))
    print(f"F2 (h = 100/2501, t = {F(24,25) - F(100,2501)}): worst so far {worst}", flush=True)
    # F3: periodic h=0 D_II lattice with alternating D offsets and full interior, and A-block next to D_II block
    for (t, s) in ((F(12, 13), F(5, 13)), (F(24, 25), F(7, 25)), (F(1), F(0))):
        for Wd in (4, 8):
            pts = {}
            for x in range(-Wd, Wd + 1):
                pts[(Q3(x), Q3(0))] = 'K' if (x % 2 == 0 or x > Wd // 2) else 'Rb'
                if x % 2 and x <= Wd // 2:
                    p = (Q3(x) + (s if (x // 2) % 2 else -s), Q3(t))
                    if admissible(p, pts): pts[p] = 'DS'
            for j in range(1, 4):
                for k in range(-Wd - 1, Wd + 2):
                    p = (Q3(k) + (Q3(F(1, 2)) if j % 2 else Q3(0)), Q3(0, -F(j, 2)))
                    if admissible(p, pts): pts[p] = 'R'
            mx, an, hv, nfw, mi, sv, nr = run(pts); n += 1
            worst = max(worst, mx); T.update(hv); AN += an; maxin = max(maxin, mi); maxfw = max(maxfw, nfw)
            maxhv = max(maxhv, sum(hv.values()))
            print(f"F3 t={t} W={Wd}: max final {mx}, heavy {dict(hv)}, forwarders {nfw}, max incoming {mi}, "
                  f"avg v {F(sv, nr)} ({float(F(sv, nr)):.4f})")
    print("configs:", n, " heavy occurrences:", dict(T), " max #heavy/config:", maxhv, " max #forwarders:", maxfw)
    print("max final charge (exact):", worst, "   max total incoming at a point:", maxin)
    print("anomalies:", len(AN), AN[:5])


if __name__ == '__main__':
    main()
