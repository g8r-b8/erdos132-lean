"""Adversarial numeric search for non-regular 'tight Lemma-2 ladders'.

TL(q): convex q-gon 1..q (ccw), values f_1<...<f_{q-1}, f_{q-1}=|1q| unique max,
  band (levels q,q+1,q+2): |ij| = f_{j-i}   (Altman Lemma 2 consequence)
  every other pair: |ij| in {f_1..f_{q-2}}
mode 'double' adds levels q-1 and q+3 (sub-case B1b).
mode 'B1a' additionally forces |1,k| = f_{q-2} for a given k<=q-2.
Floats only: sanity / exploration, not proof.
"""
import sys, itertools
import numpy as np
from scipy.optimize import least_squares

rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)


def pairs(q):
    return [(i, j) for i in range(1, q + 1) for j in range(i + 1, q + 1)]


def band(q, mode):
    lv = {q, q + 1, q + 2}
    if mode in ('double',):
        lv |= {q - 1, q + 3}
    return {(i, j) for (i, j) in pairs(q) if (i + j) in lv and (i, j) != (1, q)}


def solve(q, mode, k=None, starts=200):
    P = pairs(q)
    B = band(q, mode)
    found = []
    for s in range(starts):
        # random start: perturbed arc or random convex
        if rng.random() < 0.5:
            th = rng.uniform(0.3, 2 * np.pi / (2 * q - 3))
            ang = np.arange(q) * th + rng.normal(0, 0.15 * th, q)
            rad = 1 + rng.normal(0, 0.15, q)
        else:
            ang = np.sort(rng.uniform(0, np.pi * 1.1, q))
            rad = 1 + rng.normal(0, 0.3, q)
        X = np.c_[rad * np.cos(ang), rad * np.sin(ang)]
        D = {p: np.linalg.norm(X[p[0] - 1] - X[p[1] - 1]) for p in P}
        f = np.array(sorted(D[(i, j)] for (i, j) in P if (i, j) in B or (i, j) == (1, q)))
        # initial f per width
        fw = np.zeros(q)
        for w in range(1, q):
            vals = [D[(i, j)] for (i, j) in B if j - i == w]
            fw[w] = np.mean(vals) if vals else D[(1, q)]
        fw[q - 1] = D[(1, q)]
        assign = {}
        for it in range(30):
            # assign free pairs to nearest f_1..f_{q-2}
            new = {}
            for p in P:
                if p in B or p == (1, q):
                    continue
                if mode == 'B1a' and p == (1, k):
                    new[p] = q - 2
                    continue
                new[p] = int(np.argmin([abs(D[p] - fw[w]) for w in range(1, q - 1)])) + 1
            if new == assign and it > 0:
                break
            assign = new

            def res(z):
                Y = z[:2 * q].reshape(q, 2)
                g = z[2 * q:]
                r = []
                for (i, j) in P:
                    d = np.linalg.norm(Y[i - 1] - Y[j - 1])
                    if (i, j) == (1, q):
                        r.append(d - g[q - 2])
                    elif (i, j) in B:
                        r.append(d - g[j - i - 1])
                    else:
                        r.append(d - g[assign[(i, j)] - 1])
                r.append(g[0] - 1.0)  # scale
                return np.array(r)
            z0 = np.r_[X.ravel(), fw[1:]]
            sol = least_squares(res, z0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
            X = sol.x[:2 * q].reshape(q, 2)
            fw = np.r_[0, sol.x[2 * q:]]
            D = {p: np.linalg.norm(X[p[0] - 1] - X[p[1] - 1]) for p in P}
        if np.max(np.abs(sol.fun)) > 1e-9:
            continue
        g = fw[1:]
        if np.min(np.diff(g)) < 1e-6:
            continue
        # strict convexity, ccw, consecutive order
        ok = True
        cr = []
        for i in range(q):
            a, b, c = X[i], X[(i + 1) % q], X[(i + 2) % q]
            cr.append(np.cross(b - a, c - b))
        cr = np.array(cr)
        if not (np.all(cr > 1e-7) or np.all(cr < -1e-7)):
            continue
        # simple polygon (total turning 2pi)
        tot = 0
        for i in range(q):
            v1 = X[(i + 1) % q] - X[i]; v2 = X[(i + 2) % q] - X[(i + 1) % q]
            tot += np.arctan2(np.cross(v1, v2), v1 @ v2)
        if abs(abs(tot) - 2 * np.pi) > 1e-6:
            continue
        sides = [np.linalg.norm(X[i + 1] - X[i]) for i in range(q - 1)]
        # concyclic test
        A = np.c_[2 * X, np.ones(q)]
        bb = (X ** 2).sum(1)
        cc, *_ = np.linalg.lstsq(A, bb, rcond=None)
        circ = np.max(np.abs(A @ cc - bb))
        regular = (max(sides) - min(sides) < 1e-7) and circ < 1e-7
        found.append((regular, np.round(g, 6), np.round(sides, 5), circ))
    return found


if __name__ == '__main__':
    q = int(sys.argv[1]); mode = sys.argv[2]; k = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else None
    F = solve(q, mode, k, starts=int(sys.argv[5]) if len(sys.argv) > 5 else 200)
    nreg = sum(1 for x in F if x[0])
    print(f"q={q} mode={mode} k={k}: solutions {len(F)}, regular {nreg}, nonregular {len(F)-nreg}")
    seen = set()
    for x in F:
        if not x[0]:
            key = tuple(np.round(x[1], 4))
            if key in seen:
                continue
            seen.add(key)
            print('  NONREG f=', x[1], 'sides=', x[2], 'circ_res=%.2e' % x[3])
