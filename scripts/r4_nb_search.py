"""Adversarial float screening of the local neighbour bound (Case N: one-sided boundary near y).
y = 0 in int K_loc = cap of discs D(w_j, R), R = 1e4, boundary near y has random corners (turning = spread of the
arc normals present in B(y,2)).  Positions q on C(y,1): 'K' = on dK (exact circle-circle intersections),
'D' = outside with dist(q,K) >= t, 'I' = int K; everything else is forbidden (outside K but closer than t).
Max over angle sets with gaps >= 60 deg of m = #(K or D) and deg + m (weights K,D:2, I:1).  Screening only."""
import numpy as np, math, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
R = 1e4
TOL = 1e-7   # degrees

def trial(t, h, ncent, phimax):
    W = [np.array([0.0, h - R])]
    phis = [0.0]
    for _ in range(ncent):
        x = rng.uniform(-2.5, 2.5); phi = rng.uniform(-phimax, phimax)
        # boundary point of the first disc above x, tilt
        b = np.array([x, h - R + math.sqrt(R * R - x * x)]) - rng.uniform(0, 0.2) * np.array([0, 1])
        W.append(b - R * np.array([math.sin(phi), math.cos(phi)])); phis.append(phi)
    W = np.array(W)
    if np.any(np.linalg.norm(W, axis=1) >= R - 1e-6):   # y must be interior
        return None
    # sample boundary of K near y: points on each circle within B(0, 3) inside all other discs
    bpts, bnorm = [], []
    for j, w in enumerate(W):
        a0 = math.atan2(-w[1], -w[0])
        a = a0 + np.linspace(-4 / R, 4 / R, 16001)
        P = w + R * np.stack([np.cos(a), np.sin(a)], 1)
        ok = np.all(np.linalg.norm(P[:, None, :] - W[None, :, :], axis=2) <= R + 1e-9, axis=1) & (np.linalg.norm(P, axis=1) < 3)
        if ok.any():
            bpts.append(P[ok]); bnorm.append(phis[j])
    if not bpts:
        return None
    B = np.concatenate(bpts)
    h_true = np.linalg.norm(B, axis=1).min()
    if h_true > 1:
        return None
    turning = math.degrees(max(bnorm) - min(bnorm)) if len(bnorm) > 1 else 0.0
    # candidate angles (measured from +y axis = outward normal at the top)
    cand = []
    for w in W:  # C(0,1) cap C(w,R)
        d = np.linalg.norm(w); a = (1 + d * d - R * R) / (2 * d)
        if abs(a) <= 1:
            base = math.atan2(w[1], w[0]); off = math.acos(a)
            for s in (1, -1):
                q = np.array([math.cos(base + s * off), math.sin(base + s * off)])
                if np.all(np.linalg.norm(W - q, axis=1) <= R + 1e-9):
                    cand.append(('K', math.degrees(math.atan2(q[0], q[1]))))
    grid = np.arange(-180, 180, 0.25)
    def cls(psi):
        q = np.array([math.sin(math.radians(psi)), math.cos(math.radians(psi))])
        dm = np.linalg.norm(W - q, axis=1).max()
        if dm < R - 1e-9: return 'I'
        dist = np.linalg.norm(B - q, axis=1).min()
        return 'D' if dist >= t else None
    base_pts = [(c, g) for g in grid for c in [cls(g)] if c]
    # add shifts by multiples of 60 of K candidates and of D/I class-boundaries
    extra = []
    kangs = [a for _, a in cand]
    labs = [c for c, _ in base_pts]
    for i in range(len(base_pts) - 1):
        if labs[i] != labs[i + 1]:
            lo, hi = base_pts[i][1], base_pts[i + 1][1]
            for _ in range(30):
                mid = (lo + hi) / 2
                if cls(mid) == labs[i]: lo = mid
                else: hi = mid
            kangs += [lo, hi]
    for a in kangs:
        for k in range(1, 6):
            g = (a + 60 * k + 180) % 360 - 180
            c = cls(g)
            if c: extra.append((c, g))
    pts = sorted(cand + base_pts + extra, key=lambda p: p[1])
    ang = np.array([p[1] for p in pts]); lab = [p[0] for p in pts]
    wm = np.array([1 if c in 'KD' else 0 for c in lab]); wd = np.array([2 if c in 'KD' else 1 for c in lab])
    return turning, h_true, best(ang, wm), best(ang, wd)

def best(ang, w):
    """max total weight of a subset with circular gaps >= 60 deg (at most 6 points)."""
    n = len(ang); A = np.concatenate([ang, ang + 360]); Wt = np.concatenate([w, w]); res = 0
    for f in range(n):
        if w[f] == 0: continue
        lo = np.searchsorted(A, ang[f] + 60 - TOL); hi = np.searchsorted(A, ang[f] + 300 + TOL, 'right')
        seg = A[lo:hi]; ws = Wt[lo:hi]
        if len(seg) == 0:
            res = max(res, w[f]); continue
        cur = ws.astype(float).copy(); tot = max(w[f], w[f] + cur.max())
        for _ in range(4):
            pm = np.maximum.accumulate(cur)
            idx = np.searchsorted(seg, seg - 60 + TOL, 'right') - 1
            nxt = np.where(idx >= 0, pm[np.maximum(idx, 0)] + ws, -1e9)
            if nxt.max() <= 0: break
            cur = nxt; tot = max(tot, w[f] + cur.max())
        res = max(res, tot)
    return int(res)

rows = []
N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
for it in range(N):
    t = rng.choice([rng.uniform(0.05, 1.2), rng.uniform(0.84, 0.92)])
    h = rng.choice([rng.uniform(0, 1), 10 ** rng.uniform(-6, -3)])
    r = trial(t, h, int(rng.integers(0, 4)), rng.choice([0.002, 0.02, 0.2, 0.8]))
    if r: rows.append((t,) + r)
rows = np.array(rows, dtype=float)
t, turn, hh, m, dm = rows.T
tau = t - (1 - t * t) / (2 * R)
print("trials", len(rows))
print("max m with turning < 30 deg:", int(m[turn < 30].max()), "; overall max m:", int(m.max()), "; max deg+m:", int(dm.max()))
for thr in [1, 5, 30]:
    sel = turn < thr
    for lo, hi in [(0, 0.8660254), (0.8660254, 0.8960254), (0.8960254, 2)]:
        s2 = sel & (tau >= lo) & (tau < hi)
        if s2.any():
            print(f"turning<{thr:>2} deg, tau in [{lo:.4f},{hi:.4f}): n={s2.sum():4d} max m={int(m[s2].max())} max deg+m={int(dm[s2].max())}")
bad = (turn < 1.1) & (tau > 0.8660254 + math.tan(math.radians(1.2))) & (dm > 8)
print("violations of [tau > sqrt3/2 + tan(turning) => deg+m <= 8]:", int(bad.sum()))
print("violations of [turning < 30 => m <= 4]:", int(((turn < 30) & (m > 4)).sum()))
