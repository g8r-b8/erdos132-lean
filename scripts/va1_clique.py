"""Exhaustive (within a lattice pool) search for a counterexample to
[Ve96, Prop 3] as used by CDL / Theorem A: a point q not on the hull whose
Delta2-degree in the 2-core G' is >= 3.

If q is not in L1 then X is inside the closed disk D(q, Delta2) (else q has a
Delta-partner and is in L1), and every pair of X has squared distance
<= r2 := Delta2^2 or == Delta^2.  So candidate X are cliques of the
'compatibility graph' on lattice points of D(q, r) (q = origin).  The target
property (q not a hull vertex, deg_{G'}(q) >= 3) is monotone under adding
compatible points, so it suffices to check maximal cliques.  Each maximal
clique is also run through the full checker (Theorem A, A1, Props 3,5-8).

usage: python3 va1_clique.py tri|sq R2MAX [cap]
"""
import sys, time
from va1_common import qform, analyze, hull_vertices


def maximal_cliques(nbr, nverts, cap):
    """Bron-Kerbosch with pivoting over int bitsets. yields bitsets."""
    out = []
    stack = [(0, (1 << nverts) - 1, 0)]
    while stack and len(out) < cap:
        R, P, Xs = stack.pop()
        if P == 0 and Xs == 0:
            out.append(R)
            continue
        PX = P | Xs
        # pivot: vertex maximizing |P & N(u)|
        best, bu = -1, None
        t = PX
        while t:
            u = (t & -t).bit_length() - 1
            t &= t - 1
            c = bin(P & nbr[u]).count('1')
            if c > best:
                best, bu = c, u
        cand = P & ~nbr[bu]
        while cand:
            v = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            stack.append((R | (1 << v), P & nbr[v], Xs & nbr[v]))
            P &= ~(1 << v)
            Xs |= 1 << v
    return out


def run(kind, r2, d2, cap=200000):
    R = int(r2 ** 0.5) + 2
    pool = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)
            if 0 < qform(kind, a, b) <= r2]
    part = [p for p in pool if qform(kind, *p) == r2]
    if len(part) < 3:
        return None
    m = len(pool)
    nbr = [0] * m
    for i in range(m):
        for j in range(m):
            if i != j:
                s = qform(kind, pool[i][0] - pool[j][0], pool[i][1] - pool[j][1])
                if s <= r2 or s == d2:
                    nbr[i] |= 1 << j
    cl = maximal_cliques(nbr, m, cap)
    hits, viol, checked = [], {}, 0
    for c in cl:
        X = [(0, 0)] + [pool[i] for i in range(m) if c >> i & 1]
        res = analyze(X, kind)
        if res is None:
            continue
        checked += 1
        for v in res['viol']:
            key = v.split(':')[0]
            viol.setdefault(key, []).append((X, v))
        hv = hull_vertices(X)
        if 0 not in hv and res['Delta2'] == r2:
            # q interior: record q's G-degree
            hits.append(res['L2deg'].get((0, 0), 0))
    return dict(pool=m, cliques=len(cl), capped=len(cl) >= cap, checked=checked,
                viol=viol, qdeg=max(hits) if hits else None, nint=len(hits))


if __name__ == '__main__':
    kind = sys.argv[1]
    r2max = int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    norms = sorted({qform(kind, a, b) for a in range(-40, 41) for b in range(-40, 41)} - {0})
    for r2 in [x for x in norms if x <= r2max]:
        for d2 in [x for x in norms if r2 < x <= 4 * r2]:
            t = time.time()
            out = run(kind, r2, d2, cap)
            if out is None:
                continue
            flag = '' if not out['viol'] else ' VIOL ' + str({k: len(v) for k, v in out['viol'].items()})
            print(f"{kind} r2={r2} D2={d2} pool={out['pool']} cliques={out['cliques']}{'(CAP)' if out['capped'] else ''} "
                  f"q-interior sets={out['nint']} max deg_G(q)={out['qdeg']} {time.time()-t:.1f}s{flag}", flush=True)
            for k, lst in out['viol'].items():
                for X, v in lst[:2]:
                    print('   ', v, X)
