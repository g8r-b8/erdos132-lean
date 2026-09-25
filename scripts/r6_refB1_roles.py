#!/usr/bin/env python3
"""r6_refB1_roles.py -- referee check of B1 P4.1/P4.3 (load lemma), RELAXED role model.

For a receiver x, every (sender type, sending slot) pair is a ROLE:
   d      = direction of the sender as seen from x (deg from x's upward normal),
   xdep   = interval of possible depths of x,
   amt    = amount sent.
A set of roles can act on one x only if their directions are pairwise >= 60 - TOLA apart and their
x-depth intervals intersect (within TOLD).  This forgets all other geometric constraints, so the max
load found is an UPPER bound for the real maximum.  7-point receivers (depth <= 1, K nbr at beta with
cos beta = depth) are computed first; they give forwarder roles (d = beta, xdep = 2*depth, amt = load).
Continuous families (B's h, Dtype's psi_K and psi_a) are sampled; FLOAT sanity check only.
Also records every 3-sender combination (the case never exercised by B1's beam search).
"""
import math, itertools

D = math.radians
TOLA, TOLD = 0.3, 0.006
S3 = math.sqrt(3) / 2


def cosd(a): return math.cos(D(a))


def wrap(a): return (a + 180) % 360 - 180


def roles_for(t, dtype_steps=7, psia_step=1.0):
    R = []
    # A: depth sqrt3/2, slots +-150
    for s in (150, -150):
        R.append(('A', wrap(s - 180), (S3 - cosd(s),) * 2, .5))
    # B: D pair at +-30 at height H in [t, sqrt3/2]; h = sqrt3/2 - H in [0, sqrt3/2 - t]
    if t <= S3:
        for s in (150, -150):
            R.append(('B', wrap(s - 180), (0 - cosd(s), S3 - t - cosd(s)), .5))
    # C_phi: t <= 1/2 (+tol): phi = 30 - asin t, K at phi-60, D at phi
    if t <= 0.5 + 1e-4:
        phi = 30 - math.degrees(math.asin(min(t, .5)))
        h = cosd(60 - phi)
        for sg in (1, -1):
            for s, amt in ((phi + 120, .5), (phi + 180, .5)):
                R.append(('C', wrap(sg * s - 180), (h - cosd(s),) * 2, amt))
    # cap / A': t = 1/2 +- delta0 (generous window 1e-3)
    if abs(t - .5) <= 1e-3:
        for s, amt in ((180, 1), (120, .5), (-120, .5)):
            R.append(('cap', wrap(s - 180), (.5 - cosd(s),) * 2, amt))
        R.append(("A'", 0.0, (1.5, 1.5), 1))
    # Dtype: psi_K in [acos(1-t), 30+asin t] (clipped to <= 90.001), psi_a in [psi_K+60, 300-psi_K]
    lo = math.degrees(math.acos(max(-1, 1 - t))) if t <= 2 else 999
    hi = 30 + math.degrees(math.asin(min(1, t)))
    hi = min(hi, 90.001)
    lo = max(lo, 60.0)   # P1.3: psi_K - |psi_D| >= 60
    if t > 1:
        lo = 90.0 if t <= 1 + 2e-6 else 999
    if lo <= hi + 1e-9:
        ks = [lo + (hi - lo) * i / max(1, dtype_steps - 1) for i in range(dtype_steps)] if hi > lo else [lo]
        for pk in ks:
            h = cosd(pk)
            a = pk + 60
            while a <= 300 - pk + 1e-9:
                R.append(('Dtype', wrap(a - 180), (h - cosd(a),) * 2, .5))
                a += psia_step
            R.append(('Dtype', wrap(300 - pk - 180), (h - cosd(300 - pk),) * 2, .5))
    return R


def sep_ok(ds):
    return all(abs(wrap(a - b)) >= 60 - TOLA for a, b in itertools.combinations(ds, 2))


def inter(ivs):
    lo = max(i[0] for i in ivs) - TOLD
    hi = min(i[1] for i in ivs) + TOLD
    return (lo, hi) if lo <= hi else None


def best_load(R, extra_dir=None, dep_window=None):
    """max total amount over role-sets (size <= 3) compatible; extra_dir = K-nbr direction to avoid.
    Returns (load, witness, list_of_3sets)."""
    best = (0, None); triples = []
    Rs = [r for r in R if extra_dir is None or abs(wrap(r[1] - extra_dir)) >= 60 - TOLA]
    if dep_window:
        Rs = [r for r in Rs if inter([r[2], dep_window])]
    n = len(Rs)
    for i in range(n):
        if Rs[i][3] > best[0]:
            best = (Rs[i][3], (Rs[i],))
        for j in range(i + 1, n):
            a, b = Rs[i], Rs[j]
            if not sep_ok([a[1], b[1]]):
                continue
            iv = inter([a[2], b[2]] + ([dep_window] if dep_window else []))
            if not iv:
                continue
            if a[3] + b[3] > best[0]:
                best = (a[3] + b[3], (a, b))
    # triples: directions must be ~ -60, 0, 60 (cone width <= 122)
    L = [r for r in Rs if r[1] <= -58]; M = [r for r in Rs if abs(r[1]) <= 2.5]; U = [r for r in Rs if r[1] >= 58]
    for a in L:
        for b in M:
            if not sep_ok([a[1], b[1]]) or not inter([a[2], b[2]]):
                continue
            for c in U:
                if sep_ok([a[1], b[1], c[1]]) and inter([a[2], b[2], c[2]] + ([dep_window] if dep_window else [])):
                    triples.append((a, b, c))
                    if a[3] + b[3] + c[3] > best[0]:
                        best = (a[3] + b[3] + c[3], (a, b, c))
    return best, triples


def run(t):
    R = roles_for(t)
    # 7-points: depth dd <= 1, K at beta = +-acos(dd); sample dd over the x-depths realised by roles
    fwd = []; worst7 = 0
    cand = sorted(set(round(r[2][0], 4) for r in R) | set(round(r[2][1], 4) for r in R))
    for dd in cand:
        if not (0 < dd <= 1 + 1e-4):
            continue
        beta = math.degrees(math.acos(min(1, dd)))
        for b in (beta, -beta):
            (ld, w), _ = best_load(R, extra_dir=b, dep_window=(dd, dd))
            if ld > 0:
                worst7 = max(worst7, ld)
                fwd.append(('fwd', b, (2 * dd, 2 * dd), ld))
    R2 = R + fwd
    (ld, w), triples = best_load(R2)
    return len(R2), worst7, ld, w, triples


def main():
    ts = [0.001, 0.05, 0.15, 0.25, 0.35, 0.45, 0.4899, 0.49, 0.495, 0.4999, 0.5, 0.5001, 0.505, 0.51,
          0.5101, 0.55, 0.62, 0.7, 0.78, 0.8461, 1.000001, 1.2]
    allok = True
    for t in ts:
        n, w7, ld, w, tr = run(t)
        ok = ld <= 1 + 1e-9 and w7 <= 1 + 1e-9
        allok &= ok
        wit = [(r[0], round(r[1], 1), round(r[3], 2)) for r in w] if w else None
        print(f"t={t:<9} roles={n:5d} max7load={w7:.2f} maxload={ld:.2f} 3-sender sets={len(tr):4d} "
              f"{'OK' if ok else 'VIOLATION'} witness={wit}")
        if tr:
            kinds = sorted(set(tuple(x[0] for x in s) for s in tr))
            print("    3-sender kinds:", kinds[:12])
    print("ALL LOADS <= 1:", allok)


if __name__ == '__main__':
    main()
