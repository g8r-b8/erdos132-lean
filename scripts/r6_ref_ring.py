"""R6 referee: ienjoymath ring construction vs N3 (float).  t/delta must be < 0.44 so Lemma Pin forbids heavy
points; check max v = deg + m over R-points <= 8 (in fact <= 6) and report t/delta, tau."""
import sys, numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from ring16 import construction, summary
TOL = 1e-9
for n in [60, 120, 250]:
    best = None
    for m in range(6, n // 2 + 1):
        X, g, D2 = construction(m, n)
        s = summary(X)
        if abs(s['delta'] - g) < TOL and abs(s['D2'] - D2) < TOL:
            v = min(s['mu_D2'], s['mu_delta'])
            if best is None or v > best[0]: best = (v, m, X, g, D2)
    v, m, X, g, D2 = best
    X = np.array(X); d = np.abs(X[:, None] - X[None, :]); Dm = d.max()
    t = (Dm - D2) / g; R2 = D2 / g; tau = t - (1 - t * t) / (2 * R2)
    S = np.any(np.abs(d - D2) < TOL, axis=1); A = np.abs(d - g) < TOL
    vv = A.sum(1) + (A & S[None, :]).sum(1)
    print(f"n={n} m={m}: t/delta={t:.5f} tau={tau:.5f} Delta/Delta2={Dm/D2:.4f} max v over R = {int(vv[~S].max())}")
    assert t < 0.44 and vv[~S].max() <= 8
print("OK: ring construction has t << 0.44 (no fans/caps possible by Lemma Pin) and v <= 8 on R")
