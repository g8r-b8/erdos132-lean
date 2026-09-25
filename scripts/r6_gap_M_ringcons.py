"""Consistency: ienjoymath ring configurations vs the pure penny claims.
A := strict convex-hull vertices of X (then all neighbours of a lie in an open half-plane).
Check: deg(a)<=3; Def(G) - 2|A|; rung-end degree lemma (B-neighbour of an A-point with two A-neighbours in G[A]
that is its middle neighbour has deg<=5)."""
import sys, math, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from ring16 import ring_core, construction
TOL = 1e-9
def hull(P):
    idx = sorted(range(len(P)), key=lambda i: (P[i].real, P[i].imag))
    cr = lambda o, a, b: (a-o).real*(b-o).imag - (a-o).imag*(b-o).real
    lo, up = [], []
    for i in idx:
        while len(lo) >= 2 and cr(P[lo[-2]], P[lo[-1]], P[i]) <= 1e-12: lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up) >= 2 and cr(P[up[-2]], P[up[-1]], P[i]) <= 1e-12: up.pop()
        up.append(i)
    return lo[:-1] + up[:-1]
def check(X, label):
    X = [complex(z) for z in X]; n = len(X)
    Z = np.array(X); Dm = np.abs(Z[:, None]-Z[None, :]); dl = np.min(Dm[Dm > 1e-9])
    adj = np.abs(Dm - dl) < TOL*max(1, dl)
    deg = adj.sum(1); Def = 3*n - adj.sum()//2
    H = hull(X); Aset = set(H)
    viol = [i for i in H if deg[i] > 3]
    bad = 0
    for a in H:
        nb = [j for j in np.nonzero(adj[a])[0]]
        Anb = [j for j in nb if j in Aset]
        if deg[a] == 3 and len(Anb) == 2:
            # middle neighbour
            ang = sorted(nb, key=lambda j: math.atan2(((X[j]-X[a])/(-X[a]+sum(X)/n)).imag, ((X[j]-X[a])/(-X[a]+sum(X)/n)).real))
            m = ang[1]
            if m not in Aset and deg[m] > 5: bad += 1
    print(f'{label}: n={n} |A_hull|={len(H)} maxdegA={max(deg[i] for i in H)} Def={Def} Def-2|A|={Def-2*len(H)} degA>3:{len(viol)} middle-deg6:{bad}')
for m in [8, 12, 20, 40]:
    v, us, D, D2 = ring_core(m); check(v+us, f'even core m={m}')
for m in [9, 13, 21]:
    v, us, D, D2 = ring_core(m); check(v+us, f'odd core m={m}')
for N in [100, 300]:
    m = 2*math.ceil(3*N/14); X, g, D2 = construction(m, N); check(X, f'full n={N}')
