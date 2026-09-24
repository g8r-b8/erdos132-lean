"""R3/OS: targeted numerical search for convex n-sets on TWO CONCENTRIC circles (radii 1 and rho) with exactly D
distinct distances.  (Pach-de Zeeuw leaves concentric circles as the only bounded-degree "two-curve" escape, so
this is where a structured COC obstruction would have to live.)

Variables: angles theta_i and rho; circle pattern (which points are inner) fixed per restart.
Same alternating scheme as fewdist_search.py: optimal contiguous partition of sorted distances into D groups, then
least squares.  Floating point; NOT exhaustive.
Usage: python3 r3_os_conc.py n D restarts seed
"""
import numpy as np, sys, itertools
from scipy.optimize import least_squares
n, D, R = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = np.random.default_rng(seed)
I, J = np.triu_indices(n, 1); NP = len(I)


def pts(z, inner):
    th = z[:n]; rho = z[n]
    r = np.where(inner, rho, 1.0)
    return np.c_[r*np.cos(th), r*np.sin(th)]


def dists(P): return np.linalg.norm(P[I]-P[J], axis=1)


def best_partition(d):
    o = np.argsort(d); s = d[o]
    cs = np.concatenate([[0], np.cumsum(s)]); cs2 = np.concatenate([[0], np.cumsum(s*s)])
    A = np.arange(NP+1)[:, None]; B = np.arange(NP+1)[None, :]
    K = np.maximum(B-A, 1)
    C = (cs2[B]-cs2[A]) - (cs[B]-cs[A])**2/K
    C = np.where(B > A, C, np.inf)
    f = np.full(NP+1, np.inf); f[0] = 0; args = []
    for g in range(1, D+1):
        M = f[:, None] + C
        a = np.argmin(M, axis=0); f = M[a, np.arange(NP+1)]; args.append(a)
    lab = np.zeros(NP, int); b = NP
    for g in range(D, 0, -1):
        a = args[g-1][b]; lab[o[a:b]] = g-1; b = a
    return lab


def convres(P, eps=1e-3):
    c = P.mean(0); o = np.argsort(np.arctan2(P[:, 1]-c[1], P[:, 0]-c[0])); Q = P[o]
    A, B, C = Q, np.roll(Q, -1, 0), np.roll(Q, -2, 0)
    cr = (B-A)[:, 0]*(C-B)[:, 1] - (B-A)[:, 1]*(C-B)[:, 0]
    return np.minimum(cr-eps, 0)*10, cr.min()


def cocirc(P, tol=1e-7):
    best = 0
    for a, b, c in itertools.combinations(range(n), 3):
        M = np.array([[P[i, 0], P[i, 1], 1] for i in (a, b, c)]); rhs = -np.array([P[i] @ P[i] for i in (a, b, c)])
        try: s = np.linalg.solve(M, rhs)
        except np.linalg.LinAlgError: continue
        best = max(best, int((np.abs(np.einsum('ij,ij->i', P, P) + P @ s[:2] + s[2]) < tol).sum()))
    return best


seen = {}
for t in range(R):
    b = int(rng.integers(2, n//2+1))
    if rng.random() < 0.5:   # alternating-ish pattern
        inner = np.zeros(n, bool); inner[np.sort(rng.choice(n, b, replace=False))] = True
    else:
        inner = (np.arange(n) % 2 == 1) if b == n//2 else np.isin(np.arange(n), 2*np.arange(b)+1)
    if rng.random() < 0.7:   # near a sub-lattice of angles (regular-ish), moderate noise
        Np = n + int(rng.integers(0, 4)); sub = np.sort(rng.choice(Np, n, replace=False))
        th = np.sort(2*np.pi*sub/Np + rng.normal(0, rng.choice([0.02, 0.06, 0.15]), n))
    else:
        th = np.sort(rng.uniform(0, 2*np.pi, n))
    rho = rng.uniform(0.8, 0.999)
    z = np.r_[th, rho]
    try:
        for it in range(25):
            P = pts(z, inner); d = dists(P); lab = best_partition(d)
            c0 = np.array([d[lab == g].mean() for g in range(D)])
            def res(y):
                Pz = pts(y[:n+1], inner); dd = dists(Pz)
                return np.concatenate([dd - y[n+1:][lab], convres(Pz)[0], [min(y[n]-0.3, 0)*10, max(y[n]-0.99999, 0)*10]])
            sol = least_squares(res, np.r_[z, c0], xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=400)
            zn = sol.x[:n+1]
            if np.allclose(zn, z, atol=1e-13): z = zn; break
            z = zn
    except Exception:
        continue
    P = pts(z, inner); d = dists(P); lab = best_partition(d)
    r = max(np.ptp(d[lab == g]) for g in range(D))
    if r > 1e-9 or convres(P)[1] < 1e-6 or abs(z[n]-1) < 1e-6: continue
    Dn = len(set(np.round(d/d.max(), 7)))
    if Dn != D: continue
    key = tuple(np.round(np.sort(d/d.max()), 5)[::7])
    if key in seen: seen[key][0] += 1; continue
    cc = cocirc(P)
    mult = sorted(np.bincount(lab))
    seen[key] = [1, cc, z[n], int(inner.sum())]
    print("NEW n=%d D=%d rho=%.6f inner=%d maxcocirc=%d mult=%s" % (n, D, z[n], inner.sum(), cc, mult), flush=True)
print("restarts", R, "distinct", len(seen))
from collections import Counter
print("HIST maxcocirc", sorted(Counter(v[1] for v in seen.values()).items()))
