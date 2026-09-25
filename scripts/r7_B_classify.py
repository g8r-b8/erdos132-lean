#!/usr/bin/env python3
"""r7_B_classify.py -- flat-limit scan of heavy (v >= 8) good points in REGION II (t in [sqrt3/2+0.03, 1]).

Reuses B1's slot model (r6_below_classify.py, copied here as r6_below_classify_B1copy.py) with two extensions:
  * depth h ranges over [0, 1] (h = 0: y is an R-point ON dK, allowed by the good-point definition);
  * a K-row slot (c = h) may be occupied by an R-point on dK (label 'R': counts in deg, not in m);
  * D slots (c = h + H, H >= t, H = t when pinned) may be S cap D or R cap D.
FLOAT screening of the hand classification (report section 1); not a proof.
Expected: only type A (K at +-30, h = sqrt3/2) and Dtype (K at +-psiK, psiK in [84.0, 90], D at psiD) occur.
"""
import math, itertools, collections, importlib.util, os
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("b1", os.path.join(HERE, "r6_below_classify_B1copy.py"))
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)
TOL = 1e-9


def configs(h, t, H):
    out = []
    aK = math.degrees(math.acos(h))
    cD = h + H
    aD = math.degrees(math.acos(cD)) if cD <= 1 + TOL else None
    Kopts = [aK, -aK] if aK > 1e-12 else [0.0]
    Dopts = [] if aD is None else ([aD, -aD] if aD > 1e-9 else [0.0])
    for nK in range(len(Kopts) + 1):
        for Ks in itertools.combinations(Kopts, nK):
            for nD in range(len(Dopts) + 1):
                for Ds in itertools.combinations(Dopts, nD):
                    fixed = list(Ks) + list(Ds)
                    if not all(b1.angdist(a, b) >= 60 - TOL for a, b in itertools.combinations(fixed, 2)):
                        continue
                    if len(Ks) > 0 and len(Ds) > 0 and abs(H - t) > 1e-9:
                        continue        # pinning
                    nfree = b1.max_free(fixed, h - 1e-12)   # strictly below the K-line (int K)
                    deg = min(len(fixed) + nfree, 6)
                    for kl in itertools.product('SR', repeat=len(Ks)):
                        for dl in itertools.product('SR', repeat=len(Ds)):
                            m = kl.count('S') + dl.count('S')
                            out.append((deg + m, deg, m, (tuple(round(k, 3) for k in Ks), kl,
                                                          tuple(round(d, 3) for d in Ds), dl, nfree)))
    return out


def typ_of(v, deg, m, sig):
    Ks, kl, Ds, dl, nfree = sig
    KS = [k for k, l in zip(Ks, kl) if l == 'S']; DS = [d for d, l in zip(Ds, dl) if l == 'S']
    if deg == 6 and m == 2 and len(KS) == 2 and all(abs(abs(k) - 30) < 0.5 for k in KS):
        return 'A'
    if deg == 5 and m == 3 and len(KS) == 2 and len(DS) == 1:
        return 'Dtype'
    return 'OTHER'


def main():
    t0 = math.sqrt(3) / 2 + 0.03
    tgrid = [t0 + (1 - t0) * i / 60 for i in range(61)]
    hgrid = [i / 400 for i in range(0, 401)] + [math.sqrt(3) / 2, 0.5]
    res = collections.defaultdict(list)
    for t in tgrid:
        Hs = [t] + [t + j / 40 for j in range(1, 5) if t + j / 40 <= 1.0001]
        hs = hgrid + [1 - t, max(0.0, 1 - t - 1e-6)]
        for H in Hs:
            for h in hs:
                if not (0 <= h <= 1):
                    continue
                for v, deg, m, sig in configs(h, t, H):
                    if v >= 8:
                        res[typ_of(v, deg, m, sig)].append((t, H, h, v, deg, m, sig))
    for k, L in sorted(res.items()):
        vs = collections.Counter(x[3] for x in L)
        print(f"type {k:6s}: {len(L):6d} hits, t in [{min(x[0] for x in L):.4f},{max(x[0] for x in L):.4f}], "
              f"h in [{min(x[2] for x in L):.4f},{max(x[2] for x in L):.4f}], v-counts {dict(vs)}")
    if res.get('OTHER'):
        print("OTHER examples:", res['OTHER'][:10])
    psis = [abs(x[6][0][0]) for x in res.get('Dtype', [])]
    if psis:
        print(f"Dtype psiK range: [{min(psis):.3f}, {max(psis):.3f}] deg (hand: [84.03, 90])")
    bad = [x for x in res.get('Dtype', []) if not x[2] <= 1 - x[0] + 1e-9]
    print("Dtype rows violating h <= 1 - t:", len(bad))
    Ah = set(round(x[2], 4) for x in res.get('A', []))
    print("A depths:", sorted(Ah))
    print("max v:", max((x[3] for L in res.values() for x in L), default=None))


if __name__ == '__main__':
    main()
