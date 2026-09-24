"""R5/A: systematic scan of D_m-symmetric 'layered polygon' sets: concentric regular m-gons
L_0 (radius 1, offset 0), L_1, L_2, ... each with radius r_i and angular offset o_i * (pi/m), o_i in {0, 1},
(mirror-symmetric orbits, 1 dof each) or a free offset (2 dof, the layer is the D_m orbit of one point,
2m points).  A new layer's radius is chosen at every 'coincidence event': a new pair-bundle distance equals
an existing class, or two new bundles coincide (every equation is linear or quadratic in r, solved by a
fine scan + bisection).  Objective: min_{2<=j<=J} mu_j - n.  Float guidance only.

Usage: python3 r5_a_rings.py m J depth width
"""
from __future__ import annotations
import sys, math, itertools
import numpy as np
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r5_a_search import classes_of, objective, stats

TOL = 1e-9


def layer(m, r, off):
    return r * np.exp(1j * (2 * np.pi * np.arange(m) / m + off * np.pi / m))


def all_d2(X):
    n = len(X); iu = np.triu_indices(n, 1)
    return (np.abs(X[:, None] - X[None]) ** 2)[iu]


def events(X, m, off, rgrid):
    """Radii r at which layer(m, r, off) creates a coincidence (new bundle = old class, or new = new)."""
    base_vals, _ = classes_of(all_d2(X))
    base_vals = base_vals[:40]                      # top classes are what matter
    p0 = lambda r: r * np.exp(1j * off * np.pi / m)
    c_all = np.array([np.abs(X - p0(r)) ** 2 for r in rgrid])
    ch_all = np.array([(2 * r * np.sin(np.pi * np.arange(1, m // 2 + 1) / m)) ** 2 for r in rgrid])
    F = np.concatenate([c_all, ch_all], axis=1)
    out = []
    def roots(g):
        s = np.sign(g); idx = np.nonzero(s[:-1] * s[1:] < 0)[0]
        return [(rgrid[i], rgrid[i + 1]) for i in idx]
    def refine(f, a, b):
        fa = f(a)
        for _ in range(60):
            mid = (a + b) / 2; fm = f(mid)
            if np.sign(fm) == np.sign(fa):
                a, fa = mid, fm
            else:
                b = mid
        return (a + b) / 2
    Xp = X
    def col(r, k):
        if k < len(Xp):
            return abs(Xp[k] - p0(r)) ** 2
        t = k - len(Xp) + 1
        return (2 * r * math.sin(math.pi * t / m)) ** 2
    ncol = F.shape[1]
    # new = old class value
    for k in range(ncol):
        for v in base_vals:
            for a, b in roots(F[:, k] - v):
                out.append(refine(lambda r: col(r, k) - v, a, b))
    # new = new (only a subset of columns: first-point cross distances are symmetric in pairs)
    for k1 in range(ncol):
        for k2 in range(k1 + 1, ncol):
            for a, b in roots(F[:, k1] - F[:, k2]):
                out.append(refine(lambda r: col(r, k1) - col(r, k2), a, b))
    out = sorted(set(round(r, 10) for r in out))
    return out


def scan(m, J, depth, width, rgrid=None, log=True):
    rgrid = rgrid if rgrid is not None else np.linspace(0.02, 1.25, 2500)
    X0 = layer(m, 1.0, 0)
    _, mu = classes_of(all_d2(X0))
    states = [(objective(mu, len(X0), J), X0, [])]
    best = states[0]
    for d in range(depth):
        new = []
        for sc, X, desc in states:
            for off in (0, 1):
                for r in events(X, m, off, rgrid):
                    L = layer(m, r, off)
                    if np.min(np.abs(X[:, None] - L[None])) < 1e-6:
                        continue
                    Y = np.concatenate([X, L])
                    _, mu = classes_of(all_d2(Y))
                    new.append((objective(mu, len(Y), J), Y, desc + [(round(r, 8), off)]))
        new.sort(key=lambda t: t[0], reverse=True)
        # dedupe by objective+desc
        states = new[:width]
        if not states:
            break
        if states[0][0] > best[0]:
            best = states[0]
        if log:
            s = states[0]; _, mu = classes_of(all_d2(s[1]))
            print(f" m={m} depth {d+1}: best obj={s[0]} n={len(s[1])} layers={s[2]} mults={list(mu[:J+2])} "
                  f"{stats(mu, len(s[1]))}  (#events tried={len(new)})", flush=True)
    return best


if __name__ == "__main__":
    m, J, depth, width = map(int, sys.argv[1:5])
    scan(m, J, depth, width)
