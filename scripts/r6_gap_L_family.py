"""R6-B-gap/L: high-precision (mpmath, 60 digits) check of the period-k first-layer-loss family.

A-points on a circle of radius R (K = disc).  One "period" = a T-path p1..pk of unit chords with
  p1 -> {qL, a12}  (a12 = inward apex of p1p2, qL = p1 + rot(a12-p1, +60deg) i.e. to the left)
  pj -> a12 + (pj - p2)  for j = 2..k      (parallel rungs; for k = 2 this is just a12)
  pk -> also qR = pk + rot(q_k - pk, -60deg)  (to the right)
The next path is the mirror image of the current one in the line O-qR (so qR is shared by pk and
the next path's first point: a gap-shared transition).  k = 1 is the special 'isolated point' case:
  p1 -> {qL, qR} with qR at 30deg from the inward normal (to the right), qL its mirror in line O-p1.
Checks: all distances >= 1 (edges = 1 up to 1e-50), the gap d versus 2cos(60deg - kappa), the
first-layer ledger per period (shared / neutral / gain, g/2), and the turning of the q-walk.
Usage: python r6_gap_L_family.py            (runs k = 1..6, R in 50, 500, 1e4)
"""
import mpmath as mp
mp.mp.dps = 60
EPS = mp.mpf(10) ** -45


def rot(v, deg):
    return v * mp.expj(mp.radians(deg))


def mirror_line(u):  # reflection in the line through 0 with direction u
    u = u / abs(u)
    return lambda z: u * u * mp.conj(z)


def build(k, R, nper=4):
    th = 2 * mp.asin(1 / (2 * R))
    if k == 1:
        p1 = mp.mpc(0, R)
        inward = mp.mpc(0, -1)
        qR = p1 + rot(inward, 30)       # rotate toward +x (right) : +30deg from -i is toward +x
        if qR.real < 0:
            qR = p1 + rot(inward, -30)
        m = mirror_line(p1)
        qL = m(qR)
        path = {'P': [p1], 'rungs': [(0, qL), (0, qR)], 'qL': qL, 'qR': qR}
    else:
        P = [R * mp.expj(mp.pi / 2 - th * j) for j in range(k)]   # left -> right on top of circle
        c1 = P[0] + (P[1] - P[0]) * mp.expj(mp.pi / 3)
        c2 = P[0] + (P[1] - P[0]) * mp.expj(-mp.pi / 3)
        a12 = c1 if abs(c1) < abs(c2) else c2
        Q = [None] + [a12 + (P[j] - P[1]) for j in range(1, k)]
        qL = P[0] + rot(a12 - P[0], 60)
        if abs(qL - P[1]) < abs(P[0] + rot(a12 - P[0], -60) - P[1]):
            qL = P[0] + rot(a12 - P[0], -60)
        qR = P[k - 1] + rot(Q[k - 1] - P[k - 1], -60)
        if abs(qR - P[k - 2]) < abs(P[k - 1] + rot(Q[k - 1] - P[k - 1], 60) - P[k - 2]):
            qR = P[k - 1] + rot(Q[k - 1] - P[k - 1], 60)
        rungs = [(0, qL), (0, a12)] + [(j, Q[j]) for j in range(1, k)] + [(k - 1, qR)]
        path = {'P': P, 'rungs': rungs, 'qL': qL, 'qR': qR}
    paths = [path]
    for _ in range(nper - 1):
        cur = paths[-1]
        m = mirror_line(cur['qR'])
        P2 = [m(z) for z in reversed(cur['P'])]
        n = len(cur['P'])
        r2 = [(n - 1 - i, m(q)) for (i, q) in reversed(cur['rungs'])]
        paths.append({'P': P2, 'rungs': r2, 'qL': cur['qR'], 'qR': m(cur['qL'])})
    return paths


def analyse(k, R, verbose=True):
    paths = build(k, R)
    A, rung_list = [], []
    for pi, pth in enumerate(paths):
        base = len(A)
        A += pth['P']
        for (i, q) in pth['rungs']:
            rung_list.append((base + i, q))
    # distinct B points
    B = []
    for (_, q) in rung_list:
        if all(abs(q - b) > EPS for b in B):
            B.append(q)
    pts = A + B
    mind, maxedge = mp.mpf(10), mp.mpf(0)
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            d = abs(pts[i] - pts[j])
            if abs(d - 1) < EPS:
                maxedge = max(maxedge, abs(d - 1))
            else:
                mind = min(mind, d)
    assert mind > 1, ('VIOLATION', k, R, mind)
    # A-A edges: T-edges (consecutive) ; gaps
    gaps = [abs(A[i + 1] - A[i]) for i in range(len(A) - 1) if abs(abs(A[i + 1] - A[i]) - 1) > EPS]
    # every rung really has length 1 and every A-B unit pair is a listed rung
    for (i, q) in rung_list:
        assert abs(abs(A[i] - q) - 1) < EPS
    nAB = sum(1 for a in A for b in B if abs(abs(a - b) - 1) < EPS)
    # transitions in walk order (rung_list is already in order along the boundary, then by angle)
    # classify on the middle two periods only (avoid boundary effects)
    per = len(paths[0]['rungs'])
    sh = ne = ga = intra = 0
    for t in range(per, 2 * per):
        (i, q), (i2, q2) = rung_list[t], rung_list[t + 1]
        dq = abs(q2 - q)
        if dq < EPS:
            sh += 1
        elif abs(dq - 1) < EPS:
            ne += 1
            intra += (i == i2)
        else:
            ga += int(mp.ceil(dq)) - 1
    # dedupe: consecutive entries of rung_list with same (i,q) across path boundary? (mirror gives
    # (0,qR) of next path == last rung of current path with different A index -> shared, fine)
    # predicted gap: kappa = turning between chord of the stretch start and the gap chord
    res = {'k': k, 'R': R, 'min_nonedge_minus1': mind - 1, 'gap_d': gaps[0] if gaps else None,
           'shared': sh, 'neutral': ne, 'intra': intra, 'gain': ga, 'nAB': nAB, 'nrungs': len(rung_list)}
    if k >= 2:
        P, P2 = paths[0]['P'], paths[1]['P']
        psi_s = mp.arg(P[1] - P[0])
        psi_g = mp.arg(P2[0] - P[-1])
        kap = psi_s - psi_g
        res['kappa_deg'] = mp.degrees(kap)
        res['pred_d'] = 2 * mp.cos(mp.pi / 3 - kap)
    else:
        P, P2, P3 = paths[0]['P'], paths[1]['P'], paths[2]['P']
        kap = mp.arg(P2[0] - P[0]) - mp.arg(P3[0] - P2[0])
        res['kappa_deg'] = mp.degrees(kap)
        res['pred_d'] = 2 * mp.cos(mp.pi / 3 - kap / 2)
    # q-walk turning (signed, clockwise positive) at each distinct consecutive q of the middle periods
    walk = []
    for (_, q) in rung_list:
        if not walk or abs(walk[-1] - q) > EPS:
            walk.append(q)
    turns = []
    for t in range(1, len(walk) - 1):
        d1, d2 = walk[t] - walk[t - 1], walk[t + 1] - walk[t]
        turns.append(mp.degrees(mp.arg(d1 / d2)))   # >0 : clockwise = convex for our orientation
    res['walk_turns_deg'] = [mp.nstr(x, 6) for x in turns[len(turns) // 3: len(turns) // 3 + per + 1]]
    return res


if __name__ == '__main__':
    for k in range(1, 7):
        for R in [mp.mpf(50), mp.mpf(500), mp.mpf(10) ** 4]:
            r = analyse(k, R)
            per_A = k
            g_half = 1  # one gap per period (each path of k points has 2 endpoints)
            lam = -r['shared'] + r['gain']
            print(f"k={k} R={mp.nstr(R,5)}: min nonedge-1={mp.nstr(r['min_nonedge_minus1'],5)}  "
                  f"gap d={mp.nstr(r['gap_d'],12)} pred 2cos(60-kappa..)={mp.nstr(r['pred_d'],12)}  "
                  f"kappa={mp.nstr(r['kappa_deg'],6)}deg")
            print(f"     per period: |A|={per_A} shared={r['shared']} neutral={r['neutral']} (intra {r['intra']}) "
                  f"gain={r['gain']}  Lambda={lam}  g/2={g_half}  first-layer ledger Def-2|A| >= {lam + g_half}"
                  f"  (per A-point {mp.nstr(mp.mpf(lam + g_half)/per_A,4)})")
            if R == 50:
                print('     q-walk turnings (deg, one period):', r['walk_turns_deg'])
