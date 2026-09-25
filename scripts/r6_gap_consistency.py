"""Coordinator consistency check (floats) on ienjoymath configurations:
exact split Def(G) = Def(G[D]) + Def(G[X\\D]) - e(D, X\\D); K-part claim Def(G[X\\D]) >= 2|S\\D| - o(n)."""
import sys, math, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from ring16 import ring_core, spectrum, construction
TOL = 1e-9
def Def(adj, idx):
    sub = adj[np.ix_(idx, idx)]; return 3*len(idx) - sub.sum()//2
def analyze(X, label):
    X = np.array(X); n = len(X); Dm = np.abs(X[:, None]-X[None, :])
    sp = spectrum(list(X)); dl, D2, D = sp[0][0], sp[-2][0], sp[-1][0]
    A1 = np.abs(Dm-dl) < TOL; Dset = (np.abs(Dm-D) < TOL).any(1); S = (np.abs(Dm-D2) < TOL).any(1)
    Di = np.nonzero(Dset)[0]; Ki = np.nonzero(~Dset)[0]
    DefG = 3*n - A1.sum()//2; cross = int(A1[np.ix_(Di, Ki)].sum())
    dD, dK = Def(A1, Di), Def(A1, Ki); krow = int((S & ~Dset).sum()); sD = int((S & Dset).sum())
    assert DefG == dD + dK - cross
    print(f"{label}: n={n} |D|={len(Di)} |S∩D|={sD} Krow={krow} Def(G[D])-2|D|={dD-2*len(Di)} "
          f"Def(Kpart)-2Krow={dK-2*krow} cross e(D,X\\D)={cross} Def-2s={DefG-2*int(S.sum())}")
for m in [8, 12, 20, 40]:
    v, us, D, D2 = ring_core(m); analyze(v+us, f"even core m={m}")
for m in [9, 13, 21]:
    v, us, D, D2 = ring_core(m); analyze(v+us, f"odd core m={m}")
for n in [100, 300]:
    m = 2*math.ceil(3*n/14); X, g, D2 = construction(m, n); analyze(X, f"full n={n}")
