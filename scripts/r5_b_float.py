"""R5/B float evidence: run the r5_b_exact.check battery (LS, TZ, F', REV, K4, CX, CB, K8) on
(i) ring(m, S) families (regular m-gon + servers on the edge set S) and (ii) random greedy
circle-intersection closures biased to many Delta2-edges (mostly Case II sets).
Squared distances quantised to 1e-8 (va1_common.qform 'flt'), orientation tolerance 1e-7.
Guidance only (floating point).   usage: python3 r5_b_float.py SEEDS STEPS
"""
import sys, math, random
from collections import Counter
import numpy as np
from r5_b_exact import run_float
from r5_b_lab import ring, regular, analyze, circ, compatible, greedy_closure


def make(seed, steps):
    rng = random.Random(seed)
    typ = rng.random()
    if typ < 0.3:
        m = rng.choice([5, 7, 9, 11, 13, 6, 8, 10, 12])
        X = regular(m)
        A = np.array(X)
        ds = sorted({round(float(x), 9) for x in np.sqrt(((A[:, None] - A[None]) ** 2).sum(-1)).ravel()}, reverse=True)
        Dl, D2 = ds[0], ds[1]
        X = rng.sample(X, rng.randint(max(3, m - 4), m))
    elif typ < 0.45:
        m = rng.choice([7, 9, 11, 8, 10, 12])
        S = [j for j in range(m) if rng.random() < 0.5]
        X = ring(m, S)
        r0 = analyze(X)
        Dl, D2 = r0['Dl'], r0['D2']
        X = rng.sample(X, len(X) - rng.randint(0, 3))
    else:
        D2 = 1.0
        Dl = rng.uniform(1.01, 1.99) if rng.random() < 0.7 else rng.uniform(1.0, 1.15)
        X = [(0.0, 0.0), (Dl, 0.0)]
        for _ in range(rng.randint(2, 6)):
            a, b = rng.sample(range(len(X)), 2)
            cs = [z for z in circ(X[a], X[b], D2, rng.choice([D2, Dl])) if compatible(X, z, D2, Dl)]
            if cs:
                X.append(rng.choice(cs))
    return greedy_closure(X, D2, Dl, steps, rng)


if __name__ == '__main__':
    C = Counter()
    for m in range(5, 22):
        for S in (None, [0], [0, 1], [0, 1, 2], list(range(0, m, 2)), list(range(m // 2))):
            run_float(ring(m, S), C)
    print('rings', dict(C), flush=True)
    C = Counter()
    seeds, steps = int(sys.argv[1]), int(sys.argv[2])
    for sd in range(seeds):
        run_float(make(7 * 10 ** 6 + sd, steps), C)
    print('greedy', dict(C))
