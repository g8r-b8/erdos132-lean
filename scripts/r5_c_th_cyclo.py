"""R5/C theory: cyclotomic-pool search (float with 1e-9 quantisation = GUIDANCE; hits are
re-verified exactly in r5_c_th_verify.py).  q = 0, Delta3 = 1, pool = {sum of <= W N-th roots
of unity} within the closed unit disc (mode L3) or also on circle radius Delta2 (mode L2).
Reports max core degree of 0 by depth over maximal cliques, per (Delta2, Delta).
usage: python3 r5_c_th_cyclo.py N W L3|L2 [cap]
"""
import sys, itertools, cmath, math
from collections import defaultdict
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from va1_clique import maximal_cliques
from r5_c_th_search import core
from va1_common import layers

Q = 1e8


def key(z):
    return (round(z.real * 1e7), round(z.imag * 1e7))


def sq(a, b):
    return round(abs(a - b) ** 2 * Q)


def pool_pts(N, W):
    roots = [cmath.exp(2j * math.pi * k / N) for k in range(N)]
    pts = {}
    for w in range(1, W + 1):
        for c in itertools.combinations_with_replacement(range(N), w):
            z = sum(roots[k] for k in c)
            if abs(z) > 1e-9:
                pts.setdefault(key(z), z)
    return list(pts.values())


def run(N, W, mode, cap=50000):
    P = pool_pts(N, W)
    one = round(Q)
    disc = [z for z in P if round(abs(z) ** 2 * Q) <= one]
    vals = sorted({sq(a, b) for a in disc for b in disc if sq(a, b) > one + 5} | {round(abs(z)**2*Q) for z in P if abs(z)**2 > 1 + 1e-7 and abs(z) <= 2})
    results = defaultdict(int)
    gdeg = defaultdict(int)
    hits = []
    for N2 in vals:
        pool = disc + ([z for z in P if round(abs(z) ** 2 * Q) == N2] if mode == 'L2' else [])
        for N1 in vals:
            if N1 <= N2 or N1 > 4 * N2:
                continue
            m = len(pool)
            nbr = [0] * m
            for i in range(m):
                for j in range(i + 1, m):
                    s = sq(pool[i], pool[j])
                    if s <= one or s == N2 or s == N1:
                        nbr[i] |= 1 << j; nbr[j] |= 1 << i
            cl = maximal_cliques(nbr, m, cap)
            if len(cl) >= cap:
                print('CAP', N2, N1)
            for c in cl:
                X = [0j] + [pool[i] for i in range(m) if c >> i & 1]
                n = len(X)
                E, big = [], set()
                for i in range(n):
                    for j in range(i + 1, n):
                        s = sq(X[i], X[j])
                        if s == one:
                            E.append((i, j))
                        elif s > one:
                            big.add(s)
                if big != {N1, N2}:
                    continue
                alive, adj = core(n, E)
                L = layers([(z.real, z.imag) for z in X])
                d0 = [k + 1 for k, Lk in enumerate(L) if 0 in Lk][0]
                gdeg[d0] = max(gdeg[d0], len(adj[0]))
                if 0 not in alive:
                    continue
                cd0 = len(adj[0] & alive)
                results[d0] = max(results[d0], cd0)
                if cd0 >= 3 and (d0 == 3 or cd0 >= 7):
                    hits.append((d0, cd0, N2 / Q, N1 / Q, X))
    print(f'N={N} W={W} {mode}: pool(disc)={len(disc)} max coredeg(0) by depth {dict(results)} '
          f'#interesting hits={len(hits)}; max G3-deg(0) by depth {dict(gdeg)}')
    for h in hits[:5]:
        print('  HIT', h[:4], [(round(z.real, 6), round(z.imag, 6)) for z in h[4]])
    return hits


if __name__ == '__main__':
    N, W, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    run(N, W, mode, int(sys.argv[4]) if len(sys.argv) > 4 else 50000)
