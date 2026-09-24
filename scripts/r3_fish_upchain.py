"""r3_fish_upchain.py -- numerical checks for the "up-lemma" (Lemma U) and the defect-Altman
inequality D >= tau(c) + #{distinct distances <= |c|}   (angle R3/alt, Fishburn reconstruction).

Lemma U.  P convex polygon p_0..p_{n-1} (cyclic), exterior angles eps_v (sum 2pi).  For a chord
[a,b] (forward interval a,a+1,..,b, with b-a <= n-3) let E[a,b] = sum_{v=a}^{b} eps_v.
If E[a,b] <= pi then max(|p_{a-1}p_b|, |p_a p_{b+1}|) > |p_a p_b|.
Proof: quadrilateral p_{a-1} p_a p_b p_{b+1} has interior angles th_a, th_b at p_a, p_b with
th_a + th_b = 2pi - E' >= pi (E' = rotation from edge (a-1,a) to edge (b,b+1) = E[a,b]).  If
|p_{a-1}p_b| <= |p_a p_b| then in triangle (a-1,a,b) the angle at a is <= the angle at a-1, so
th_a < pi/2; likewise th_b < pi/2; contradiction.

tau(c): number of guaranteed up-steps from chord c (both orientations, take max).
Checks: (1) Lemma U on random + perturbed-regular polygons; (2) the inequality on examples; prints
the slack D - (tau + #values<=|c|) minimised over chords (0 = tight).
"""
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
TOL = 1e-9

def ext_angles(P):
    n = len(P); e = np.zeros(n)
    for v in range(n):
        d1 = P[v] - P[v-1]; d2 = P[(v+1) % n] - P[v]
        e[v] = abs(np.arctan2(d1[0]*d2[1]-d1[1]*d2[0], d1@d2))
    return e

def strictly_convex(P):
    n = len(P); s = []
    for i in range(n):
        a, b, c = P[i], P[(i+1) % n], P[(i+2) % n]
        s.append((b-a)[0]*(c-b)[1]-(b-a)[1]*(c-b)[0])
    s = np.array(s); return (s > 1e-12).all() or (s < -1e-12).all()

def distinct_sorted(D):
    v = np.sort(D[np.triu_indices(len(D), 1)]); out = [v[0]]
    for x in v[1:]:
        if x - out[-1] > 1e-7 * max(1, x): out.append(x)
    return np.array(out)

def tau(n, e, a, b):
    """guaranteed up-steps from forward interval [a..b] (vertex count b-a+1 mod n)."""
    L = (b - a) % n + 1; best = None
    # an interval I containing [a..b] with |I| = L+t vertices, I = [a-x .. b+y], x+y=t
    for t in range(0, n):
        if L + t - 1 > n - 3: return t
        for x in range(t + 1):
            y = t - x
            idx = [(a - x + k) % n for k in range(L + t)]
            if e[idx].sum() > np.pi + 1e-12: return t
    return n

def check_upper(P, name, verbose=True):
    n = len(P); e = ext_angles(P)
    D = np.linalg.norm(P[:, None] - P[None], axis=2); vals = distinct_sorted(D)
    m = len(vals); worst = 10**9; best = -1; arg = None; sidebest = -1
    for a in range(n):
        for s in range(1, n):
            b = (a + s) % n
            below = int((vals <= D[a, b] * (1 + 1e-7)).sum())
            t = tau(n, e, a, b); lb = t + below
            worst = min(worst, m - lb)          # validity: must be >= 0
            if lb > best: best, arg = lb, (a, b, t, below)
            if s == 1 or s == n - 1: sidebest = max(sidebest, lb)
    if verbose: print(f"{name:34s} n={n:3d} D={m:3d} fl(n/2)={n//2:3d} | min slack={worst:2d} (valid if >=0) | "
                      f"best bound over non-diameter chords... best={best} sides-only best={sidebest} at {arg}")
    return worst

def check_lemmaU(P):
    n = len(P); e = ext_angles(P); D = np.linalg.norm(P[:, None] - P[None], axis=2); bad = 0; tests = 0
    for a in range(n):
        for s in range(1, n - 2):
            b = (a + s) % n; idx = [(a + k) % n for k in range(s + 1)]
            if e[idx].sum() <= np.pi + 1e-12:
                tests += 1
                if not max(D[a-1, b], D[a, (b+1) % n]) > D[a, b] + TOL: bad += 1
    return tests, bad

def reg(N, keep=None, r=1.0, phase=0.0):
    ang = 2*np.pi*np.arange(N)/N + phase; P = r*np.stack([np.cos(ang), np.sin(ang)], 1)
    return P if keep is None else P[keep]

def rand_convex(n):
    while True:
        v = rng.normal(size=(n, 2)); v -= v.mean(0)
        v = v[np.argsort(np.arctan2(v[:, 1], v[:, 0]))]; P = np.cumsum(v, 0)
        if strictly_convex(P): return P

if __name__ == "__main__":
    # (1) Lemma U
    T = B = 0
    for trial in range(1500):
        n = int(rng.integers(5, 16))
        P = rand_convex(n) if trial % 2 else reg(n) + rng.normal(scale=10**rng.uniform(-4, -1), size=(n, 2))
        if not strictly_convex(P): continue
        t, b = check_lemmaU(P); T += t; B += b
    print("Lemma U: tests", T, "violations", B)
    # (2) inequality on examples
    ex = []
    for n in (9, 11, 13, 16, 21): ex.append((f"R_{n}", reg(n)))
    for n in (8, 10, 12, 16, 20): ex.append((f"R_{n+1}-1", reg(n+1, list(range(n)))))
    for n in (9, 11, 13):
        for h in range(1, (n+2)//2 + 1):
            keep = [i for i in range(n+2) if i not in (0, h)]
            ex.append((f"R_{n+2}-2 holes(0,{h})", reg(n+2, keep)))
    for N in (4, 5, 6, 8):
        rr = 1 + 0.5*(1/np.cos(np.pi/N) - 1)
        A = reg(N); Bp = reg(N, r=rr, phase=np.pi/N); P = np.empty((2*N, 2)); P[0::2] = A; P[1::2] = Bp
        if strictly_convex(P): ex.append((f"A_{2*N} (interleaved R_{N})", P))
    # subdivided Reuleaux pentagon
    V = reg(5); pts = []
    for i in range(5):
        c = V[(i+3) % 5]; p, q = V[i], V[(i+1) % 5]
        a1, a2 = np.arctan2(*(p-c)[::-1]), np.arctan2(*(q-c)[::-1]); R = np.linalg.norm(p-c)
        am = a1 + ((a2 - a1 + np.pi) % (2*np.pi) - np.pi)/2
        pts += [p, c + R*np.array([np.cos(am), np.sin(am)])]
    ex.append(("Reuleaux5 subdivided (n=10)", np.array(pts)))
    # fan polygon: center + arc of span 50deg (as a whole polygon)
    for L in (6, 9):
        th = np.radians(np.linspace(0, 50, L)); ex.append((f"fan L={L} span50", np.vstack([[0, 0], np.stack([np.cos(th), np.sin(th)], 1)])))
    for k in range(4): ex.append((f"random n=10 #{k}", rand_convex(10)))
    for k in range(3):
        P = reg(11) + rng.normal(scale=1e-3, size=(11, 2)); ex.append((f"perturbed R_11 #{k}", P))
    for name, P in ex:
        assert strictly_convex(P), name
        check_upper(P, name)
