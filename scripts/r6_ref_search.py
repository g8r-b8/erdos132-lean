"""R6 referee: adversarial FLOAT scan (sanity only) of N3's Lemmas M/H/Pin, WITH Lemma 3.2(b) exceptions enforced.
Model: K = cap of discs D(w_j,R) (R = 1e4), every centre w_j in X.  For y in int K and a value of t:
 - K-row positions on C(y,1): C(y,1) cap dK (root-finding of g(q) = max_j|q-w_j| - R);
 - D positions: C(y,1) cap C(w_j, R+t) with |q - w_k| <= R for k != j.  (Lemma 3.2(b): a point outside
   D(w_j,R) must be at distance exactly Delta = R+t from w_j.  Then dist(q,K) >= t and w_j is a diametral
   partner of q, so Lemma 3.2(a) holds automatically.)
 - int-K positions: arc where g < 0.  Non-S points may sit at int-K or at D positions (R cap D).
v(y,t) = max over S-subsets and extra points, all pairwise >= 60 - TOL degrees apart, of deg + m.
Grid over y (x, depth) and t; TOL relaxes the exact-hexagon coincidence (so found 'heavy' configurations are a
SUPERSET of the feasible ones).  Every heavy (v >= 9) configuration is classified in y's frame and t compared with
Lemma Pin.  Output: counts and any unclassified / out-of-range cases."""
import numpy as np, math, sys, itertools
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
NK = int(sys.argv[2]) if len(sys.argv) > 2 else 6
TOL = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0      # degrees of slack on the 60-degree gaps
R = 1e4
E0 = 0.02
GRID = np.radians(np.arange(-180, 180, 0.1))
UG = np.stack([np.sin(GRID), np.cos(GRID)], 1)


def make_K(ncent, phimax):
    W = [np.array([0.0, -R])]
    for _ in range(ncent):
        x = rng.uniform(-2.5, 2.5); phi = rng.uniform(-phimax, phimax)
        b = np.array([x, -R + math.sqrt(R * R - x * x)]) - rng.uniform(0, 0.002) * np.array([0, 1])
        W.append(b - R * np.array([math.sin(phi), math.cos(phi)]))
    return np.array(W)


def g_arr(Q, W):
    return np.max(np.linalg.norm(Q[:, None, :] - W[None, :, :], axis=2), axis=1) - R


def boundary_turning(W, y):
    """normals of the discs that contribute to dK within B(y,3)."""
    phis = []
    for j, w in enumerate(W):
        a0 = math.atan2(y[0] - w[0], y[1] - w[1])
        a = a0 + np.linspace(-4 / R, 4 / R, 801)
        P = w + R * np.stack([np.sin(a), np.cos(a)], 1)
        ok = (g_arr(P, W) <= 1e-9) & (np.linalg.norm(P - y, axis=1) <= 3)
        if ok.any():
            phis.extend(list(a[ok][[0, -1]]))
    return max(phis) - min(phis) if phis else 0.0


def nearest_boundary(W, y):
    best = None
    for w in W:
        v = y - w; p = w + R * v / np.linalg.norm(v)
        if g_arr(p[None], W)[0] <= 1e-7:
            d = np.linalg.norm(p - y)
            if best is None or d < best[0]: best = (d, p)
    # corner candidates: pairwise circle intersections
    for i in range(len(W)):
        for j in range(i + 1, len(W)):
            a, b = W[i], W[j]; d = np.linalg.norm(b - a)
            if d == 0 or d > 2 * R: continue
            mdp = (a + b) / 2; hh = math.sqrt(max(R * R - d * d / 4, 0)); perp = np.array([-(b - a)[1], (b - a)[0]]) / d
            for s in (1, -1):
                p = mdp + s * hh * perp
                if np.linalg.norm(p - y) < 5 and g_arr(p[None], W)[0] <= 1e-7:
                    dd = np.linalg.norm(p - y)
                    if best is None or dd < best[0]: best = (dd, p)
    return best


def circle_pts(y, w, rad):
    """C(y,1) cap C(w,rad): list of angles psi (from +z) of the points."""
    d = np.linalg.norm(w - y); a = (1 + d * d - rad * rad) / (2 * d)
    if abs(a) > 1: return []
    base = math.atan2((w - y)[0], (w - y)[1]); off = math.acos(a)
    return [base + off, base - off]


def wrap(a): return (a + math.pi) % (2 * math.pi) - math.pi


def extra_count(chosen, allowed_mask, tol):
    """max # extra points on allowed 0.1-degree grid positions, pairwise and to chosen >= 60 - tol (greedy per gap)."""
    gap = math.radians(60 - tol)
    A = GRID[allowed_mask]
    if len(A) == 0: return 0
    A2 = np.concatenate([A, A + 2 * math.pi])
    cs = sorted(chosen); total = 0
    for i, c in enumerate(cs):
        nxt = cs[(i + 1) % len(cs)] + (2 * math.pi if i == len(cs) - 1 else 0)
        if c < -math.pi: c += 2 * math.pi
        last = c
        while True:
            k = np.searchsorted(A2, last + gap - 1e-12)
            if k >= len(A2): break
            a = A2[k]
            while a < c: a += 2 * math.pi
            if a > nxt - gap + 1e-12: break
            total += 1; last = a
    return total


def best_v(Kp, Dp, Imask, Dmask_nonS, tol):
    """Kp, Dp: angles of K-row / D positions. returns (v, chosen list)."""
    S = [(a, 'K') for a in Kp] + [(a, 'D') for a in Dp]
    gap = math.radians(60 - tol)
    best = (0, None)
    for r in range(min(len(S), 4), 2, -1):
        for sub in itertools.combinations(S, r):
            angs = [a for a, _ in sub]
            if any(abs(wrap(x - y)) < gap for x, y in itertools.combinations(angs, 2)): continue
            allowed = Imask | Dmask_nonS
            ex = extra_count(angs, allowed, tol)
            v = 2 * r + ex
            if v > best[0]: best = (v, sub, ex)
        if best[0] >= 2 * r + 6: break
    return best


def classify(sub, n0ang, t, ex):
    rel = sorted((k, round(math.degrees(wrap(a - n0ang)), 2)) for a, k in sub)
    Ks = sorted(a for k, a in rel if k == 'K'); Ds = sorted(a for k, a in rel if k == 'D')
    m = len(rel); deg = m + ex; tl = 4.5
    close = lambda xs, ys: len(xs) == len(ys) and all(abs(x - y) <= tl for x, y in zip(xs, ys))
    if m == 4:
        return ('F6' if deg == 6 else 'F5'), close(Ks, [-90, 90]) and close(Ds, [-30, 30]) and 0.74 <= t <= 0.99, rel
    if close(Ks, [-60, 60]) and close(Ds, [0]): return 'cap', 0.44 <= t <= 0.56, rel
    if close(Ks, [-90, 90]) and len(Ds) == 1 and min(abs(Ds[0] - 30), abs(Ds[0] + 30)) <= tl: return 'HF1', 0.74 <= t <= 0.99, rel
    if close(Ds, [-30, 30]) and len(Ks) == 1 and min(abs(Ks[0] - 90), abs(Ks[0] + 90)) <= tl: return 'HF2', 0.74 <= t <= 0.99, rel
    return 'UNCLASSIFIED', False, rel


stats = {}; bad = []; heavy = 0; tried = 0
TS = np.concatenate([np.linspace(0.02, 1.3, 257), [math.sqrt(3) / 2, 0.5]])
for it in range(NK):
    ncent = 0 if it == 0 else int(rng.integers(1, 4)); phimax = [0.004, 0.02, 0.01, 0.02][it % 4]
    W = make_K(ncent, phimax)
    for yx in np.linspace(-0.6, 0.6, 13):
        top = -R + math.sqrt(R * R - yx * yx)
        for depth in list(np.linspace(0.0005, 1.0, 21)) + [1e-4, 5e-5, 1e-5]:
            y = np.array([yx, top - depth])
            if g_arr(y[None], W)[0] >= 0: continue
            nb = nearest_boundary(W, y)
            if nb is None or nb[0] > 1: continue
            h, p0 = nb; n0ang = math.atan2((p0 - y)[0], (p0 - y)[1])
            turn = boundary_turning(W, y)
            Q = y + UG; gq = g_arr(Q, W)
            Imask = gq < -1e-12
            sgn = np.sign(gq); Kp = []
            for k in np.nonzero(sgn != np.roll(sgn, -1))[0]:
                lo, hi = GRID[k], GRID[(k + 1) % len(GRID)] + (2 * math.pi if k == len(GRID) - 1 else 0)
                glo = g_arr((y + np.array([math.sin(lo), math.cos(lo)]))[None], W)[0]
                for _ in range(50):
                    md = (lo + hi) / 2; gm = g_arr((y + np.array([math.sin(md), math.cos(md)]))[None], W)[0]
                    if (gm > 0) == (glo > 0): lo, glo = md, gm
                    else: hi = md
                Kp.append(wrap((lo + hi) / 2))
            for t in TS:
                tried += 1
                Dp = []
                for j, w in enumerate(W):
                    for a in circle_pts(y, w, R + t):
                        q = y + np.array([math.sin(a), math.cos(a)])
                        e = np.linalg.norm(W - q, axis=1) - R
                        if all(e[k] <= 1e-9 for k in range(len(W)) if k != j): Dp.append(wrap(a))
                Dmask = np.zeros(len(GRID), bool)
                for a in Dp: Dmask[int(round((math.degrees(a) + 180) * 10)) % len(GRID)] = True
                v, sub, *rest = best_v(Kp, Dp, Imask, Dmask, TOL)
                if v >= 9:
                    heavy += 1
                    typ, ok, rel = classify(sub, n0ang, t, rest[0])
                    key = (typ, ok, turn <= E0)
                    stats[key] = stats.get(key, 0) + 1
                    if not ok and turn <= E0 and len(bad) < 40:
                        bad.append((round(t, 4), round(h, 5), round(turn, 4), v, typ, rel))
    print(f"K#{it} ncent={ncent} phimax={phimax}: tried={tried} heavy={heavy} stats={stats}", flush=True)
print("heavy configurations by (type, N3-consistent, turning<=eps0):")
for k, c in sorted(stats.items(), key=str): print("  ", k, c)
print(f"flagged (turning <= eps0, not matching N3 classification/Pin): {len(bad)}")
for b in bad: print("   ", b)
