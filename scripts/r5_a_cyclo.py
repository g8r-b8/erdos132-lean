"""R5/A: simulated annealing over subsets of cyclotomic pools, objective min_{2<=j<=J} mu_j - n
(Delta_1 > Delta_2 > ... decreasing; the diameter class is excluded).  Float guidance only; records are
emitted as recipes (op "cyc") for exact re-verification with r5_a_exact.py.

Usage: python3 r5_a_cyclo.py N|tri<R>|sq<R> J n1,n2,.. iters restarts [depth=2] [radius]
Pool: 0, zeta^a, zeta^a+zeta^b, (depth 3) zeta^a+zeta^b+zeta^c, restricted to |p| <= radius.
"""
from __future__ import annotations
import sys, math, random, cmath, json
import numpy as np


def make_pool(N, depth=2, radius=None):
    reps = {}
    def put(expo):
        p = sum(cmath.exp(2j * math.pi * a / N) for a in expo) if expo else 0j
        if radius is not None and abs(p) > radius + 1e-9:
            return
        key = (round(p.real, 8), round(p.imag, 8))
        if key not in reps or len(expo) < len(reps[key][1]):
            reps[key] = (p, list(expo))
    put(())
    for a in range(N):
        put((a,))
    if depth >= 2:
        for a in range(N):
            for b in range(a, N):
                put((a, b))
    if depth >= 3:
        for a in range(N):
            for b in range(a, N):
                for c in range(b, N):
                    put((a, b, c))
    L = list(reps.values())
    return np.array([p for p, _ in L]), [e for _, e in L]


def lattice_pool(kind, R):
    """Triangular (kind 'tri', N=12 recipes) or square ('sq', N=4) lattice points with |p| <= R."""
    out = []; E = []
    for a in range(-R - 1, R + 2):
        for b in range(-R - 1, R + 2):
            if kind == "tri":
                p = a + b * cmath.exp(1j * math.pi / 3); ea = [0] * a if a >= 0 else [6] * (-a)
                eb = [2] * b if b >= 0 else [8] * (-b)
            else:
                p = a + 1j * b; ea = [0] * a if a >= 0 else [2] * (-a); eb = [1] * b if b >= 0 else [3] * (-b)
            if abs(p) <= R + 1e-9:
                out.append(p); E.append(ea + eb)
    return np.array(out), E


def class_matrix(P):
    d2 = np.abs(P[:, None] - P[None, :]) ** 2
    r = np.round(d2, 8)
    vals, inv = np.unique(r, return_inverse=True)   # ascending; class 0 = distance 0
    return inv.reshape(d2.shape).astype(np.int32), vals


def score(counts, n, J):
    nz = np.nonzero(counts[1:])[0][::-1] + 1       # present classes, decreasing distance
    top = counts[nz[1:J]]
    if len(top) < J - 1:
        return -10 ** 9, -10 ** 9
    hard = int(top.min()) - n
    soft = -float((np.maximum(0, n + 1 - top) ** 2).sum())
    return hard, soft


def anneal(C, n, J, iters, T0, seed, init=None):
    rng = random.Random(seed)
    N = C.shape[0]; K = int(C.max()) + 1
    S = list(init) if init else rng.sample(range(N), n)
    inS = np.zeros(N, bool); inS[S] = True
    counts = np.zeros(K, np.int64)
    for i in range(n):
        for j in range(i + 1, n):
            counts[C[S[i], S[j]]] += 1
    cur = score(counts, n, J)
    best = (cur, list(S))
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-3
        k = rng.randrange(n); out = S[k]; inn = rng.randrange(N)
        if inS[inn]:
            continue
        Sarr = np.array(S)
        np.subtract.at(counts, C[out, Sarr], 1); counts[0] += 1
        S[k] = inn; Sarr[k] = inn
        np.add.at(counts, C[inn, Sarr], 1); counts[0] -= 1
        new = score(counts, n, J)
        if new[1] >= cur[1] or rng.random() < math.exp((new[1] - cur[1]) / T):
            cur = new; inS[out] = False; inS[inn] = True
            if cur > best[0]:
                best = (cur, list(S))
        else:
            np.subtract.at(counts, C[inn, Sarr], 1); counts[0] += 1
            S[k] = out; Sarr[k] = out
            np.add.at(counts, C[out, Sarr], 1); counts[0] -= 1
    return best


def run(N, J, ns, iters, restarts, depth=2, radius=None, log=True):
    if isinstance(N, str):
        kind = "tri" if N.startswith("tri") else "sq"
        P, E = lattice_pool(kind, int(N[len(kind):])); N = 12 if kind == "tri" else 4
    else:
        P, E = make_pool(N, depth, radius)
    C, vals = class_matrix(P)
    if log:
        print(f"pool N={N} depth={depth} radius={radius} size={len(P)} classes={len(vals)}", flush=True)
    res = {}
    for n in ns:
        if n > len(P):
            continue
        bb = None
        for r in range(restarts):
            b = anneal(C, n, J, iters, 2.0 * n, r * 7919 + n)
            if bb is None or b[0] > bb[0]:
                bb = b
        (hard, soft), S = bb
        sub = C[np.ix_(S, S)][np.triu_indices(n, 1)]
        cl, cn = np.unique(sub, return_counts=True)
        mults = [int(k) for k in cn[::-1]]
        rare = [j + 1 for j in range(1, len(mults)) if mults[j] <= n]
        rec = {"N": N, "ops": [["cyc", E[i]] for i in S], "name": f"cyc N={N} J={J} n={n}"}
        res[n] = (hard, mults, rec)
        if log:
            print(f"N={N} J={J} n={n} min_(2..J) mu_j - n = {hard}  mults={mults[:J+3]}  "
                  f"first_rare={rare[0] if rare else None} s'={len(rare)} mu(delta)={mults[-1]}", flush=True)
            print("   RECIPE", json.dumps(rec), flush=True)
    return res


if __name__ == "__main__":
    N = sys.argv[1]; N = int(N) if N.isdigit() else N
    J = int(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(",")]
    iters = int(sys.argv[4]); restarts = int(sys.argv[5])
    depth = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    radius = float(sys.argv[7]) if len(sys.argv) > 7 else None
    run(N, J, ns, iters, restarts, depth, radius)
