"""R5/C theory: exact lattice search for non-extreme G3'-vertices of high core degree.

q = origin, Delta3^2 = r2 (a norm of the lattice), (Delta2^2, Delta^2) = (N2, N1).
All distances of X are <= Delta3 or in {Delta2, Delta}.
mode L3: X subset closed disc D(0, Delta3)   (forced when q in L3)
mode L2: X subset D(0, Delta3) cup C(0, Delta2) (forced when q not extreme: X in D(0,Delta2),
         no distance in (Delta3, Delta2))
Candidates = cliques of the compatibility graph.  'coredeg_{G3'}(0) >= c' and 'N1, N2 realised'
are monotone under adding compatible points, depth(0) is non-decreasing and <= 3 whenever 0 has
a Delta3-edge, so maximal cliques decide existence.  Exact integer arithmetic throughout.
usage: python3 r5_c_th_search.py tri|sq r2 L2|L3 [cap]
"""
import sys
from collections import defaultdict, Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from va1_common import qform, layers
from va1_clique import maximal_cliques


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


def analyse(X, kind, r2):
    n = len(X)
    E = []
    big = set()
    for i in range(n):
        for j in range(i + 1, n):
            s = qform(kind, X[i][0] - X[j][0], X[i][1] - X[j][1])
            if s == r2:
                E.append((i, j))
            elif s > r2:
                big.add(s)
    L = layers(X)
    dep = {}
    for k, Lk in enumerate(L):
        for i in Lk:
            dep[i] = k + 1
    alive, adj = core(n, E)
    cd = {v: len(adj[v] & alive) for v in alive}
    return big, E, dep, cd, adj


def run(kind, r2, mode, cap=100000, verbose=False):
    R = int((4 * r2) ** 0.5) + 3
    allpts = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1) if (a, b) != (0, 0)]
    disc = [p for p in allpts if qform(kind, *p) <= r2]
    circ = [p for p in disc if qform(kind, *p) == r2]
    if len(circ) < 3:
        return
    norms = sorted({qform(kind, *p) for p in allpts if r2 < qform(kind, *p) <= 4 * r2})
    best = Counter()
    hits = []
    for N2 in norms:
        pool = disc + ([p for p in allpts if qform(kind, *p) == N2] if mode == 'L2' else [])
        for N1 in norms:
            if N1 <= N2 or (mode == 'L3' and N1 > 4 * r2):
                continue
            m = len(pool)
            nbr = [0] * m
            for i in range(m):
                for j in range(i + 1, m):
                    s = qform(kind, pool[i][0] - pool[j][0], pool[i][1] - pool[j][1])
                    if s <= r2 or s == N2 or s == N1:
                        nbr[i] |= 1 << j; nbr[j] |= 1 << i
            cl = maximal_cliques(nbr, m, cap)
            if len(cl) >= cap:
                print('  CAP', N2, N1)
            for c in cl:
                X = [(0, 0)] + [pool[i] for i in range(m) if c >> i & 1]
                big, E, dep, cd, adj = analyse(X, kind, r2)
                if big != {N1, N2}:
                    continue
                for v, k in cd.items():
                    if dep[v] >= 2:
                        key = (dep[v], k)
                        best[key] += 1
                if cd.get(0, 0) >= 3:
                    hits.append((dep[0], cd[0], N2, N1, len(X), X))
    mx = defaultdict(int)
    for (d, k), c in best.items():
        mx[d] = max(mx[d], k)
    print(f'{kind} r2={r2} {mode}: max core-deg of non-extreme vertices by depth {dict(mx)}; '
          f'#hits(coredeg(0)>=3)={len(hits)}')
    hs = sorted(hits, key=lambda h: (-h[1], h[4]))
    seen = set()
    for h in hs:
        if (h[0], h[1]) in seen:
            continue
        seen.add((h[0], h[1]))
        print('   depth', h[0], 'coredeg', h[1], 'N2,N1', h[2], h[3], 'n', h[4], h[5])
    return hits


if __name__ == '__main__':
    kind, r2, mode = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
    run(kind, r2, mode, cap)
