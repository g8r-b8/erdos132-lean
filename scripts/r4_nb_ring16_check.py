"""Consistency check: deg y + m_y over R in ienjoymath's ring construction (scripts/ring16.py). Float screening."""
import os, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from ring16 import construction, summary, spectrum
TOL = 1e-9
for n in [60, 120, 250]:
    best = None
    for m in range(6, n // 2 + 1):
        X, g, D2 = construction(m, n)
        s = summary(X)
        if abs(s['delta'] - g) < TOL and abs(s['D2'] - D2) < TOL:
            v = min(s['mu_D2'], s['mu_delta'])
            if best is None or v > best[0]:
                best = (v, m, X, g, D2)
    v, m, X, g, D2 = best
    X = np.array(X); d = np.abs(X[:, None] - X[None, :])
    S = np.any(np.abs(d - D2) < TOL, axis=1)
    A = np.abs(d - g) < TOL
    deg = A.sum(1); mS = (A & S[None, :]).sum(1)
    R = ~S
    hist = collections.Counter(int(deg[i] + mS[i]) for i in range(len(X)) if R[i])
    print(f"n={n} m={m} min={v} ratio={v/n:.4f} |S|={S.sum()} r={R.sum()} "
          f"max m_y over R={int(mS[R].max())} hist(deg+m over R)={dict(sorted(hist.items()))}")
