"""R3/OS: analyse configurations saved by r3_os_search.py (scratch .npy files).
For each converged convex set: n, D, w = n - max#cocircular, D - n/2, and tests of
  LC  (linear cocircular stability conjecture):  D >= (n + w)/2 - 2
  SIDE: max multiplicity of a side length >= n - 2(D - floor(n/2)) - 2   (candidate "most sides equal")
Usage: python3 r3_os_analyze.py file1.npy [file2.npy ...]
"""
import numpy as np, sys, itertools
from collections import Counter


def cocirc(P, tol=1e-6):
    n = len(P); best = 0
    for a, b, c in itertools.combinations(range(n), 3):
        M = np.array([[P[i, 0], P[i, 1], 1] for i in (a, b, c)]); rhs = -np.array([P[i] @ P[i] for i in (a, b, c)])
        try: s = np.linalg.solve(M, rhs)
        except np.linalg.LinAlgError: continue
        vals = np.abs(np.einsum('ij,ij->i', P, P) + P @ s[:2] + s[2])
        best = max(best, int((vals < tol).sum()))
    return best


for f in sys.argv[1:]:
    arr = np.load(f, allow_pickle=True)
    for x in arr:
        P = np.asarray(x, float).reshape(-1, 2); n = len(P)
        c = P.mean(0); P = P[np.argsort(np.arctan2(P[:, 1]-c[1], P[:, 0]-c[0]))]
        P = P / np.linalg.norm(P[:, None]-P[None], axis=2).max()
        d = [np.linalg.norm(P[i]-P[j]) for i, j in itertools.combinations(range(n), 2)]
        D = len(set(np.round(d, 6)))
        w = n - cocirc(P)
        sides = Counter(np.round(np.linalg.norm(P - np.roll(P, -1, 0), axis=1), 6))
        ms = max(sides.values()); K = D - n//2
        lc = D >= (n + w)/2 - 2
        side_ok = ms >= n - 2*K - 2
        print("%s n=%d D=%d K=%d w=%d  LC:%s  maxEqualSides=%d SIDE:%s" % (f.split('/')[-1], n, D, K, w, lc, ms, side_ok))
