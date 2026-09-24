"""R5/A: SA over subsets of a 'constructible pool' = seed set + all two-circle intersection points
(radii = top-K distance classes of the seed, centres = seed points), objective min_{2<=j<=J} mu_j - n.
Initial state = seed + random pool points.  Float guidance only.
Usage: python3 r5_a_poolsa.py <seed> J K n1,n2,.. iters restarts [maxabs]
"""
import sys, json, math
import numpy as np
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r5_a_search import seed_recipe, replay, class_reps, candidates, profile, stats
from r5_a_cyclo import class_matrix, anneal

if __name__ == "__main__":
    seed, J, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    ns = [int(x) for x in sys.argv[4].split(",")]; iters, restarts = int(sys.argv[5]), int(sys.argv[6])
    maxabs = float(sys.argv[7]) if len(sys.argv) > 7 else 1.05
    X = replay(seed_recipe(seed)); vals, mults, reps = class_reps(X)
    C = [c for c, op in candidates(X, list(range(min(K, len(vals)))), vals, reps)]
    P = list(X)
    for c in C:
        if abs(c) <= maxabs and min(abs(p - c) for p in P) > 1e-7:
            P.append(c)
    P = np.array(P); n0 = len(X)
    Cm, cv = class_matrix(P)
    print(f"seed {seed} n0={n0} pool={len(P)} classes={len(cv)}", flush=True)
    for n in ns:
        best = None
        for r in range(restarts):
            rng = np.random.default_rng(r)
            init = list(range(n0)) + list(rng.choice(np.arange(n0, len(P)), n - n0, replace=False))
            b = anneal(Cm, n, J, iters, 1.0 * n, 1000 * r + n, init=init)
            if best is None or b[0] > best[0]:
                best = b
        (hard, soft), S = best
        _, mm = profile(P[S])
        print(f"n={n} J={J} best min mu_j - n = {hard}  mults={list(mm[:J+3])} {stats(mm, n)}", flush=True)
