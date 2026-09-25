#!/usr/bin/env python3
"""r6_below_classify.py -- flat-limit scan of heavy (v >= 8) good points, Region I and tau > 1.

Flat model (limit eps0 -> 0, Lambda -> oo, R -> oo) at a good point y of depth h in (0,1]:
  neighbour q = y + (sin psi, cos psi), c(q) := cos psi = height of q above y.
  K-row neighbour : c = h                (|psi| <= 90)
  D neighbour     : c = h + H,  H >= t;  H = t if a K-row point is within distance 3 (pinning, O2)
  int-K neighbour : c < h   (closure c <= h used, degenerate cases flagged)
  all neighbours pairwise >= 60 deg apart.
v = deg + m, m = #K-nbrs + #(S cap D)-nbrs.  (R cap D nbrs count in deg only.)
This is a FLOAT screening of the hand classification (report section P2); it is not a proof.
"""
import math, itertools, collections

TOL = 1e-9
DEG = math.pi / 180


def angdist(a, b):
    d = abs(a - b) % 360.0
    return min(d, 360.0 - d)


def max_free(fixed, h):
    """max number of int-K nbrs: directions psi with cos psi <= h, >= 60 from fixed and each other."""
    aK = math.degrees(math.acos(max(-1.0, min(1.0, h))))   # free arc = [aK, 360-aK]
    lo, hi = aK, 360.0 - aK
    # allowed = [lo,hi] minus open 60-balls around fixed points; fixed lie in [-aK, aK] (upper cap)
    # but D/K at exactly +-aK possible; compute on a fine grid of candidate starts (greedy is exact on an interval)
    forb = []
    for f in fixed:
        forb.append(f % 360.0)
    # build allowed intervals inside [lo,hi]
    pts = []
    x = lo
    # sweep allowed region: sample-based interval extraction with exact endpoints
    cuts = [lo, hi]
    for f in forb:
        for c in (f - 60.0, f + 60.0, f - 60.0 + 360, f + 60.0 + 360, f - 60.0 - 360, f + 60 - 360):
            if lo < c < hi:
                cuts.append(c)
    cuts = sorted(set(cuts))
    intervals = []
    for a, b in zip(cuts, cuts[1:]):
        mid = 0.5 * (a + b)
        if all(angdist(mid, f) >= 60.0 - TOL for f in forb):
            if intervals and abs(intervals[-1][1] - a) < 1e-12:
                intervals[-1][1] = b
            else:
                intervals.append([a, b])
    # also isolated allowed points (degenerate): endpoints exactly 60 from two fixed points
    for c in cuts:
        if all(angdist(c, f) >= 60.0 - TOL for f in forb) and not any(i[0] - 1e-9 <= c <= i[1] + 1e-9 for i in intervals):
            intervals.append([c, c])
    # greedy placement across intervals (they are disjoint, sorted); consecutive picks >= 60 apart
    intervals.sort()
    cnt, last = 0, -1e9
    for a, b in intervals:
        s = max(a, last + 60.0)
        while s <= b + TOL:
            cnt += 1
            last = s
            s = last + 60.0
    return cnt


def configs(h, t, H):
    """yield (v, deg, m, signature) for all S-choices."""
    out = []
    aK = math.degrees(math.acos(h)) if h <= 1 else None
    cD = h + H
    aD = math.degrees(math.acos(cD)) if cD <= 1 + TOL else None
    Kopts = [] if aK is None else [aK, -aK] if aK > 1e-12 else [0.0]
    Dopts = [] if aD is None else ([aD, -aD] if aD > 1e-9 else [0.0])
    for nK in range(len(Kopts) + 1):
        for Ks in itertools.combinations(Kopts, nK):
            for nD in range(len(Dopts) + 1):
                for Ds in itertools.combinations(Dopts, nD):
                    fixed = list(Ks) + list(Ds)
                    ok = all(angdist(a, b) >= 60 - TOL for a, b in itertools.combinations(fixed, 2))
                    if not ok:
                        continue
                    pinned_needed = (len(Ks) > 0 and len(Ds) > 0)
                    if pinned_needed and abs(H - t) > 1e-9:
                        continue
                    for labels in itertools.product(['S', 'R'], repeat=len(Ds)):
                        nfree = max_free(fixed, h)
                        deg = len(fixed) + nfree
                        deg = min(deg, 6)
                        m = len(Ks) + labels.count('S')
                        v = deg + m
                        sig = ('K', tuple(round(k, 2) for k in Ks), 'D', tuple(round(d, 2) for d in Ds), labels, 'free', nfree)
                        out.append((v, deg, m, sig))
    return out


def classify(h, t, H, Ks, Ds, labels, deg, m):
    """map to hand types."""
    nK, nDS = len(Ks), labels.count('S')
    if deg == 6 and m == 2 and nK == 2 and abs(abs(Ks[0]) - 30) < 0.5:
        return 'A'
    if deg == 6 and m == 2 and nK == 0 and nDS == 2 and abs(abs(Ds[0]) - 30) < 0.5:
        return 'B'
    if deg == 6 and m == 2 and nK == 1 and nDS == 1:
        return 'C'
    if deg == 6 and m == 2 and nK == 2 and abs(abs(Ks[0]) - 60) < 0.5:
        return "A'"
    if deg == 6 and m == 3 and nK == 2 and abs(abs(Ks[0]) - 60) < 0.5:
        return 'cap'
    if deg == 5 and m == 3 and nK == 2 and nDS == 1:
        return 'Dtype'
    return 'OTHER'


def main():
    res = collections.defaultdict(list)
    tgrid = [i / 100 for i in range(0, 85)] + [0.8461, 0.4999, 0.5001] + [1.0 + i / 50 for i in range(1, 15)]   # t in [0,0.845] u (1,1.3)
    hgrid = [i / 200 for i in range(1, 201)]
    special_h = [math.cos(a * DEG) for a in (30, 60, 90)] + [math.sqrt(3) / 2 - 0.0, 0.5]
    others = collections.Counter()
    for t in tgrid:
        Hs = [t] + [t + j / 10 for j in range(1, 10) if t + j / 10 < 1]
        hs = hgrid + special_h
        # add exact-type depths for C (h = cos(30+asin t)) and B (h = sqrt3/2 - H) and Dtype-range
        if t < 0.5:
            hs = hs + [math.cos((30 + math.degrees(math.asin(t))) * DEG)]
        for H in Hs:
            hs2 = hs + ([math.sqrt(3) / 2 - H] if H < math.sqrt(3) / 2 else [])
            for h in hs2:
                if h <= 0 or h > 1:
                    continue
                for v, deg, m, sig in configs(h, t, H):
                    if v >= 8:
                        Ks, Ds, labels = sig[1], sig[3], sig[4]
                        typ = classify(h, t, H, Ks, Ds, labels, deg, m)
                        res[typ].append((t, H, round(h, 4), v, sig))
                        if typ == 'OTHER':
                            others[(round(t, 3), round(h, 3), v, sig)] += 1
    for typ, L in sorted(res.items()):
        ts = [x[0] for x in L]
        vs = collections.Counter(x[3] for x in L)
        print(f"type {typ:6s}: {len(L):6d} hits, t in [{min(ts):.4f}, {max(ts):.4f}], v-counts {dict(vs)}")
        if typ in ('C', 'Dtype', "A'", 'cap'):
            # t-range details
            pass
    print("OTHER examples:", list(others.items())[:10])
    # C check: t = sin(30 - phi), D at phi, K at phi-60
    bad = 0
    for (t, H, h, v, sig) in res.get('C', []):
        Ks, Ds = sig[1], sig[3]
        phi = [d for d, l in zip(Ds, sig[4]) if l == 'S'][0]
        k = Ks[0]
        if not (abs(abs(k - phi) - 60) < 0.2 and abs(t - math.sin((30 - abs(phi)) * DEG)) < 2e-2):
            bad += 1
    print("C-type rows violating (K = D -+ 60, t = sin(30-|phi|)):", bad)
    # Dtype check: t in [sin(psiK-30), 1-cos psiK]
    bad = 0
    for (t, H, h, v, sig) in res.get('Dtype', []):
        psiK = abs(sig[1][0])
        if not (math.sin((psiK - 30) * DEG) - 1e-3 <= t <= 1 - math.cos(psiK * DEG) + 1e-3):
            bad += 1
    print("Dtype rows violating t in [sin(psiK-30), 1-cos psiK]:", bad)
    for typ in ("A'", 'cap'):
        L = res.get(typ, [])
        if L:
            print(typ, 't values:', sorted(set(round(x[0], 4) for x in L))[:10])
    # tau>1 slice
    print("t>1 types:", collections.Counter(typ for typ, L in res.items() for x in L if x[0] > 1))


if __name__ == '__main__':
    main()
