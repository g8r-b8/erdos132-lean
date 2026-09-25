"""R6 referee: FLOAT hexagon scan (sanity only) for deg-6 heavy points (F6, HF1, HF2, cap) with Lemma 3.2(b) enforced.
K = cap of discs D(w_j,R) (all w_j in X), R = 1e4.  For y on a fine grid (x, depth) and hexagon rotation phi on a
0.05-degree grid, each vertex q is: K-row if |g(q)| <= dK (g = max_j|q-w_j| - R); int-K if g < 0; else a D-point
candidate with required t_q = (common) excess over the centres with |q-w_j| > R (Lemma 3.2(b): all those excesses must
equal t; we require them to agree within dT).  For each candidate t, v = deg + m counts K and t-consistent D vertices
(all D taken in S).  Relaxed tolerances => reported heavy set is a superset of the feasible one.
Every v >= 9 configuration is classified in y's frame (n0 from nearest boundary point) and t compared with Lemma Pin."""
import numpy as np, math, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
NK = int(sys.argv[2]) if len(sys.argv) > 2 else 4
R = 1e4; dK = 1e-2; dT = 2e-2; E0 = 0.02
PHI = np.radians(np.arange(0, 60, 0.05))
ANG = PHI[:, None] + np.radians(60 * np.arange(6))[None, :]           # (nphi, 6)
UX, UZ = np.sin(ANG), np.cos(ANG)


def make_K(ncent, phimax):
    W = [np.array([0.0, -R])]
    for _ in range(ncent):
        x = rng.uniform(-2.0, 2.0); phi = rng.uniform(-phimax, phimax)
        b = np.array([x, -R + math.sqrt(R * R - x * x)]) - rng.uniform(0, 0.002) * np.array([0, 1])
        W.append(b - R * np.array([math.sin(phi), math.cos(phi)]))
    return np.array(W)


def gpt(q, W): return np.max(np.linalg.norm(W - q, axis=1)) - R


def boundary_info(W, y):
    """nearest boundary point (sampled) and turning of dK within B(y,3)."""
    best, phis = None, []
    for w in W:
        a0 = math.atan2(y[0] - w[0], y[1] - w[1])
        a = a0 + np.linspace(-4 / R, 4 / R, 4001)
        P = w + R * np.stack([np.sin(a), np.cos(a)], 1)
        g = np.max(np.linalg.norm(P[:, None, :] - W[None, :, :], axis=2), axis=1) - R
        ok = (g <= 1e-9) & (np.linalg.norm(P - y, axis=1) <= 3)
        if ok.any():
            phis += [a[ok][0], a[ok][-1]]
            d = np.linalg.norm(P[ok] - y, axis=1); i = np.argmin(d)
            if best is None or d[i] < best[0]: best = (d[i], P[ok][i])
    return best, (max(phis) - min(phis) if phis else 0.0)


def classify(kinds, angs, n0ang, t):
    rel = [(k, (math.degrees(a - n0ang) + 180) % 360 - 180) for k, a in zip(kinds, angs) if k in 'KD']
    Ks = sorted(a for k, a in rel if k == 'K'); Ds = sorted(a for k, a in rel if k == 'D'); tl = 3.5
    close = lambda xs, ys: len(xs) == len(ys) and all(abs(x - y) <= tl for x, y in zip(xs, ys))
    if len(rel) == 4:
        return 'F6', close(Ks, [-90, 90]) and close(Ds, [-30, 30]) and 0.74 <= t <= 0.99, rel
    if close(Ks, [-60, 60]) and close(Ds, [0]): return 'cap', 0.44 <= t <= 0.56, rel
    if close(Ks, [-90, 90]) and len(Ds) == 1 and min(abs(Ds[0] - 30), abs(Ds[0] + 30)) <= tl: return 'HF1', 0.74 <= t <= 0.99, rel
    if close(Ds, [-30, 30]) and len(Ks) == 1 and min(abs(Ks[0] - 90), abs(Ks[0] + 90)) <= tl: return 'HF2', 0.74 <= t <= 0.99, rel
    return 'UNCLASSIFIED', False, rel


stats, bad, ts = {}, [], {}
for it in range(NK):
    ncent = 0 if it == 0 else int(rng.integers(1, 4)); phimax = [0.02, 0.004, 0.01, 0.02][it % 4]
    W = make_K(ncent, phimax)
    xs = [0.0] if ncent == 0 else np.linspace(-0.6, 0.6, 49)
    for yx in xs:
        top = -R + math.sqrt(R * R - yx * yx)
        for depth in np.concatenate([np.arange(0.001, 1.0, 0.002), [1 / (2 * R), 1e-5, 1e-4]]):
            y = np.array([yx, top - depth])
            if gpt(y, W) >= 0: continue
            QX = y[0] + UX; QZ = y[1] + UZ
            E = np.sqrt((QX[..., None] - W[:, 0]) ** 2 + (QZ[..., None] - W[:, 1]) ** 2) - R   # (nphi,6,nc)
            g = E.max(-1)
            isK = np.abs(g) <= dK
            isI = g < -dK
            pos = np.where(E > dK, E, np.nan)
            tq = np.nanmax(pos, -1); tmin = np.nanmin(pos, -1)
            isD = (g > dK) & (tq - tmin <= dT)
            nK = isK.sum(1)
            # candidate t = each D vertex's t_q
            best_v = nK * 2 + isI.sum(1)          # no D
            best_t = np.full(len(PHI), np.nan)
            for c in range(6):
                tc = tq[:, c]
                cons = isD & (np.abs(tq - tc[:, None]) <= dT)
                v = 2 * (nK + cons.sum(1)) + isI.sum(1)
                upd = isD[:, c] & (v > best_v)
                best_v = np.where(upd, v, best_v); best_t = np.where(upd, tc, best_t)
            hv = np.nonzero(best_v >= 9)[0]
            if len(hv) == 0: continue
            (h, p0), turn = boundary_info(W, y)
            n0ang = math.atan2(p0[0] - y[0], p0[1] - y[1])
            for i in hv:
                t = best_t[i]
                if not (t > 0): continue
                kinds = ['K' if isK[i, k] else 'I' if isI[i, k] else
                         ('D' if isD[i, k] and abs(tq[i, k] - t) <= dT else 'x') for k in range(6)]
                typ, ok, rel = classify(kinds, ANG[i], n0ang, t)
                key = (typ, bool(ok), turn <= E0, int(best_v[i]))
                stats[key] = stats.get(key, 0) + 1
                ts.setdefault(typ, []).append(t)
                if not ok and turn <= E0 and len(bad) < 30:
                    bad.append((round(float(t), 4), round(h, 4), round(turn, 4), int(best_v[i]), typ,
                                [(k, round(a, 1)) for k, a in rel]))
    print(f"K#{it} ncent={ncent} phimax={phimax}: stats={stats}", flush=True)
print("heavy (v>=9) deg-6 configurations by (type, N3-consistent, turning<=eps0, v):")
for k, c in sorted(stats.items(), key=str): print("  ", k, c)
for typ, l in ts.items(): print(f"   t-range for {typ}: [{min(l):.4f}, {max(l):.4f}]")
print(f"flagged (turning <= eps0, not matching N3): {len(bad)}")
for b in bad: print("   ", b)
