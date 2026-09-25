#!/usr/bin/env python3
"""r7_refB_classify.py -- REF_B independent slot classifier for heavy (v >= 8) good points in Region II.

Independent code (no reuse of B / B1 scripts). Flat-limit neighbour model around a good y at depth h in [0,1]:
  * K-row slots: exactly the two angles +-psiK, psiK = arccos h (label 'K' in S, or 'Rb' = R on dK, or empty);
  * D slots: angle psi with cos psi >= h + t; PINNED (cos psi = h + t exactly) if any S-labelled K-slot is used,
    otherwise ANY cos psi >= h + t (relaxation covering unpinned D-points); label 'DS' (S) or 'DR' (R cap D);
    any number of D slots allowed a priori (geometry must kill >= 2);
  * int-K: any angle with cos psi <= h (closed: relaxation, also covers R on dK away from +-psiK);
  * all neighbours pairwise >= 60 deg apart (tolerance 1e-7).
For each (t, h) we enumerate all fixed K/D choices and labels, then fill int-K points maximally (1-D greedy per gap,
exact special angles added to the candidate grid), and record every configuration with v = deg + m >= 8.
FLOAT screen of Theorem 1 (the proof is by hand); not a proof.
Expected (Theorem 1): only A (deg 6, m 2, K at +-30, h = sqrt3/2) and D_II (deg 5, m 3, K,K,DS, h <= 1 - t).
"""
import math, itertools, collections, random, sys

TOL = 1e-7
GRID = [i * 0.05 for i in range(7200)]  # 0.05 deg


def ad(a, b):
    d = abs((a - b) % 360.0)
    return min(d, 360.0 - d)


def cosd(a):
    return math.cos(math.radians(a))


def fill(fixed, h):
    """max # of int-K points (cos psi <= h, closed relaxation), pairwise and from fixed >= 60 - TOL.
    Exact 1-D greedy (leftmost placement) on the union of allowed pieces inside each gap; fixed nonempty."""
    fs = sorted(x % 360.0 for x in fixed)
    psiK = math.degrees(math.acos(max(-1.0, min(1.0, h))))
    total = 0; placed = []
    for i, a in enumerate(fs):
        b = fs[(i + 1) % len(fs)]
        if len(fs) == 1:
            b = a + 360.0
        elif b <= a:
            b += 360.0
        lo, hi = a + 60 - TOL, b - 60 + TOL
        if hi < lo:
            continue
        pieces = []
        for k in (-360.0, 0.0, 360.0, 720.0):
            L, U = max(lo, psiK + k), min(hi, 360 - psiK + k)
            if L <= U:
                pieces.append((L, U))
        pieces.sort()
        last = None
        for L, U in pieces:
            x = L if last is None else max(L, last + 60 - TOL)
            while x <= U:
                total += 1; placed.append(x % 360); last = x
                x = last + 60 - TOL
    return total, placed


def configs(t, h):
    psiK = math.degrees(math.acos(h))
    Kang = [psiK, -psiK] if psiK > 1e-9 else [0.0]
    cD = h + t
    out = []
    for nK in range(len(Kang) + 1):
        for Ks in itertools.combinations(Kang, nK):
            for kl in itertools.product(('K', 'Rb'), repeat=nK):
                pinned = 'K' in kl
                if cD > 1 + 1e-12:
                    Dang = []
                elif pinned:
                    a = math.degrees(math.acos(min(1.0, cD)))
                    Dang = sorted(set([a, -a]))
                else:
                    a = math.degrees(math.acos(min(1.0, cD)))
                    Dang = [x * 0.25 for x in range(-int(a / 0.25), int(a / 0.25) + 1)] + [a, -a]
                for nD in range(0, 3):
                    if nD == 2 and Dang and (max(Dang) - min(Dang)) < 60 - TOL:
                        continue   # D arc narrower than 60 deg: no two D-slots (exactly the M2 fact, checked per (t,h))
                    for Ds in itertools.combinations(Dang, nD):
                        fixed = list(Ks) + list(Ds)
                        if any(ad(p, q) < 60 - TOL for p, q in itertools.combinations(fixed, 2)):
                            continue
                        for dl in itertools.product(('DS', 'DR'), repeat=nD):
                            m = kl.count('K') + dl.count('DS')
                            if m < 2:
                                continue
                            nf, placed = fill(fixed, h)
                            deg = len(fixed) + nf
                            if deg > 6:
                                raise RuntimeError(('deg>6', t, h, fixed, placed))
                            out.append((deg + m, deg, m, Ks, kl, Ds, dl, placed))
    return out


def typ(t, h, c):
    v, deg, m, Ks, kl, Ds, dl, placed = c
    KS = [k for k, l in zip(Ks, kl) if l == 'K']
    DS = [d for d, l in zip(Ds, dl) if l == 'DS']
    if deg == 6 and m == 2 and len(KS) == 2 and all(abs(abs(k) - 30) < 0.1 for k in KS) and abs(h - math.sqrt(3) / 2) < 1e-3:
        return 'A'
    if deg == 5 and m == 3 and len(KS) == 2 and len(DS) == 1 and h <= 1 - t + 1e-9:
        psiK = abs(KS[0])
        if all(psiK + 60 - 1e-6 <= (p % 360) <= 300 - psiK + 1e-6 for p in placed) and abs(DS[0]) <= psiK - 60 + 1e-6:
            return 'D_II'
    return 'OTHER'


def main():
    tmin = math.sqrt(3) / 2 + 0.03
    ts = [tmin + (1 - tmin) * i / 24 for i in range(25)] + [1 - 1e-6, tmin + 1e-6]
    rnd = random.Random(1)
    hits = collections.defaultdict(list); maxv = 0; n = 0
    for t in ts:
        hs = [i / 250 for i in range(251)] + [1 - t, max(0.0, 1 - t - 1e-9), math.sqrt(3) / 2, 0.5, 1e-9,
                                               math.cos(math.radians(84.5)), math.cos(math.radians(89.99))]
        hs += [rnd.random() for _ in range(100)] + [rnd.random() * (1 - t) for _ in range(100)]
        for h in hs:
            if not 0 <= h <= 1:
                continue
            for c in configs(t, h):
                n += 1
                maxv = max(maxv, c[0])
                if c[0] >= 8:
                    hits[typ(t, h, c)].append((t, h, c))
    print("configurations enumerated (m >= 2):", n, " max v:", maxv)
    for k, L in sorted(hits.items()):
        print(f"{k:6s}: {len(L)} hits; t in [{min(x[0] for x in L):.5f},{max(x[0] for x in L):.5f}]; "
              f"h in [{min(x[1] for x in L):.5f},{max(x[1] for x in L):.5f}]; v values {sorted(set(x[2][0] for x in L))}")
    if hits.get('D_II'):
        ps = [abs(x[2][3][0]) for x in hits['D_II']]
        print("D_II psiK range: [%.4f, %.4f]" % (min(ps), max(ps)))
    if hits.get('OTHER'):
        for x in hits['OTHER'][:10]:
            print("OTHER:", x)
    print("VERDICT:", "only A and D_II" if not hits.get('OTHER') else "UNCLASSIFIED HEAVY FOUND")


if __name__ == '__main__':
    main()
