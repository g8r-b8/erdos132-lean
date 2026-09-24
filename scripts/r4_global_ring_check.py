"""R4-global: check deficit bookkeeping on ienjoymath ring cores (even/odd m) + patch.
Def = 3n - mu(delta).  Classify D (diameter endpoints), S (has Delta2 partner), K-row = S\D.
Reports: s, Def, Def-2s, #S-R delta-edges (rungs), S-degree histogram, tau, F-3n."""
import os, sys, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ring16 import ring_core, spectrum, construction
TOL = 1e-9
def analyze(X, label):
    X = np.array(X); n = len(X)
    Dm = np.abs(X[:, None] - X[None, :])
    sp = spectrum(list(X)); dl, D2, D = sp[0][0], sp[-2][0], sp[-1][0]
    A1 = np.abs(Dm - dl) < TOL; A2 = np.abs(Dm - D2) < TOL; AD = np.abs(Dm - D) < TOL
    Dset = AD.any(1); S = A2.any(1)
    deg = A1.sum(1); mu = A1.sum() // 2; mu2 = A2.sum() // 2
    s = S.sum(); Def = 3 * n - mu
    rungs = int((A1 & S[:, None] & ~S[None, :]).sum())
    t = (D - D2) / dl; D2n = D2 / dl; tau = t - (1 - t * t) / (2 * D2n)
    hist = {int(k): int(((deg == k) & S).sum()) for k in range(7) if ((deg == k) & S).any()}
    F = mu + 4 * mu2 / 3
    print(f"{label}: n={n} s={s} |D|={Dset.sum()} Krow={int((S & ~Dset).sum())} mu_d={mu} mu_D2={mu2} "
          f"Def={Def} Def-2s={Def - 2 * s} S-R rungs={rungs} S-deg hist={hist} tau={tau:.3e} F-3n={F - 3 * n:.2f}")
for m in [8, 12, 20, 40]:
    v, us, D, D2 = ring_core(m); analyze(v + us, f"even core m={m}")
for m in [9, 13, 21, 41]:
    v, us, D, D2 = ring_core(m); analyze(v + us, f"odd  core m={m}")
for n in [100, 300]:
    m = 2 * math.ceil(3 * n / 14)
    X, g, D2 = construction(m, n); analyze(X, f"full construction n={n} m={m}")
