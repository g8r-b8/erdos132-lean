"""R5/C theory: G_j core statistics (float, guidance only).
core_stats(P, j): the Delta_j-graph, its 2-core, core degrees by layer, edge depth types."""
import sys, numpy as np
from collections import Counter, defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r5_c_common import dist_classes, depths, ring, reg


def core(n, E):
    adj = defaultdict(set)
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    alive = set(adj)
    ch = True
    while ch:
        ch = False
        for v in list(alive):
            if len(adj[v] & alive) < 2:
                alive.discard(v); ch = True
    return alive, adj


def core_stats(P, j=3, verbose=True, name=''):
    cl = dist_classes(P)
    d = depths(P)
    E = cl[j - 1][1]
    alive, adj = core(len(P), E)
    cdeg = {v: len(adj[v] & alive) for v in alive}
    bylayer = defaultdict(Counter)
    for v, k in cdeg.items():
        bylayer[d[v]][k] += 1
    types = Counter(tuple(sorted((d[a], d[b]))) for a, b in E)
    ctypes = Counter(tuple(sorted((d[a], d[b]))) for a, b in E if a in alive and b in alive)
    lay = Counter(d.values())
    out = dict(n=len(P), mu=len(E), layers=dict(sorted(lay.items())), types=dict(types),
               coretypes=dict(ctypes), coredeg={k: dict(v) for k, v in sorted(bylayer.items())},
               coreedges=sum(1 for a, b in E if a in alive and b in alive))
    if verbose:
        print(name, out)
    return out, d, cdeg


def F(m, K):
    """float version of the exact family F(m,K)"""
    R = ring(m)
    cl = dist_classes(R)
    D3 = cl[2][0]
    c = np.cos(np.pi / m)
    rho = -c + np.sqrt(c * c - 1 + D3 ** 2)
    P = [ -rho * np.array([np.cos(2*np.pi*(j+.5)/m), np.sin(2*np.pi*(j+.5)/m)]) for j in K]
    return np.vstack([R] + ([np.array(P)] if P else []))


if __name__ == '__main__':
    for m in (5, 7, 9, 11):
        for k in (0, 1, 2, m):
            core_stats(F(m, range(k)), 3, name=f'F({m},{k})')
