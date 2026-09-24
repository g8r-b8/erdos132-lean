"""Maximise the genericity margin of a realisation: stochastic hill-climb along the solution variety
(random kernel step + Newton reprojection) of f = min(cc_min, slack, Delta-1) where cc_min is the
min |sin arg crossratio| over all 4-subsets and slack = 1 - max(other distances).
Graph (E2,E1) is kept fixed; any new coincidence (other distance within 1e-6 of 1 or Delta) is rejected."""
import numpy as np
from r2_search_common import *

def objective(X, D, E2, E1):
    e2, e1, mo = classify(X, D, tol=1e-9)
    if set(e2) != set(E2) or set(e1) != set(E1): return -1.0
    c, _ = cc_all(X)
    M = dist_matrix(X); n = len(X); sep = min(M[i, j] for i in range(n) for j in range(i+1, n))
    return min(c, 1 - mo, D - 1, sep)

def climb(X, D, E2, E1, rng, iters=400, sigma=0.02, verbose=False):
    n = len(X); z = np.concatenate([X.ravel(), [D]]); f = objective(X, D, E2, E1)
    for it in range(iters):
        K = kernel(z, n, E2, E1)
        if K.shape[1] == 0: break
        dz = K @ rng.standard_normal(K.shape[1]); dz *= sigma / np.linalg.norm(dz)
        z2, ok = newton(z + dz, n, E2, E1)
        if ok:
            X2 = z2[:2*n].reshape(n, 2); f2 = objective(X2, z2[-1], E2, E1)
            if f2 > f:
                z, f = z2, f2; sigma = min(sigma * 1.5, 0.2); continue
        sigma = max(sigma * 0.8, 1e-4)
        if verbose and it % 100 == 0: print(" it", it, "f", f, "sigma", sigma)
    return z[:2*n].reshape(n, 2), z[-1], f
