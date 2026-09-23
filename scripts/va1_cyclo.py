"""Clique search (as in va1_clique.py) over cyclotomic pools Z[zeta_N]
(sums of <= W roots of unity), float64 with 1e-8 quantisation.  Targets a
counterexample to [Ve96, Prop 3] / Theorem A / A1 with q = 0 interior.

usage: python3 va1_cyclo.py N W [cap] [r2max]
"""
import sys, math, itertools, time
from va1_common import qform, analyze, hull_vertices
from va1_clique import maximal_cliques


def pool_pts(N, W):
    roots = [(math.cos(2 * math.pi * k / N), math.sin(2 * math.pi * k / N)) for k in range(N)]
    if N % 2:
        roots += [(-x, -y) for x, y in roots]
    key = lambda z: (round(z[0] * 1e7), round(z[1] * 1e7))  # dedupe near-equal floats
    pts = {key((0.0, 0.0)): (0.0, 0.0)}
    frontier = [(0.0, 0.0)]
    for _ in range(W):
        new = []
        for p in frontier:
            for r in roots:
                z = (p[0] + r[0], p[1] + r[1])
                k = key(z)
                if k not in pts:
                    pts[k] = z
                    new.append(z)
        frontier = new
    return sorted(pts.values())


def run(N, W, cap, r2max):
    P = pool_pts(N, W)
    nq = lambda p: qform('flt', p[0], p[1])
    norms = {}
    for p in P:
        norms.setdefault(nq(p), []).append(p)
    r2s = sorted(k for k, v in norms.items() if len(v) >= 3 and 0 < k <= r2max * 1e8)
    tot = 0
    worst = {}
    for r2 in r2s:
        disk = [p for p in P if 0 < nq(p) <= r2]
        m = len(disk)
        # candidate Delta^2: squared distances realised in disk, in (r2, 4 r2]
        dd = {}
        for i in range(m):
            for j in range(i + 1, m):
                s = qform('flt', disk[i][0] - disk[j][0], disk[i][1] - disk[j][1])
                if r2 < s <= 4 * r2 + 10:
                    dd.setdefault(s, []).append((i, j))
        for d2 in sorted(dd):
            nbr = [0] * m
            for i in range(m):
                for j in range(i + 1, m):
                    s = qform('flt', disk[i][0] - disk[j][0], disk[i][1] - disk[j][1])
                    if s <= r2 or s == d2:
                        nbr[i] |= 1 << j
                        nbr[j] |= 1 << i
            cl = maximal_cliques(nbr, m, cap)
            for c in cl:
                X = [(0.0, 0.0)] + [disk[i] for i in range(m) if c >> i & 1]
                res = analyze(X, 'flt')
                if res is None:
                    continue
                tot += 1
                if res['viol']:
                    print('VIOL', N, W, r2 / 1e8, d2 / 1e8, res['viol'][:3], X, flush=True)
                hv = hull_vertices(X)
                if 0 not in hv and res['Delta2'] == r2:
                    dq = res['L2deg'].get((0.0, 0.0), 0)
                    worst[dq] = worst.get(dq, 0) + 1
            if len(cl) >= cap:
                print('CAP', N, W, r2 / 1e8, d2 / 1e8, flush=True)
    print(f"N={N} W={W} pool={len(P)} r2 values={len(r2s)} sets checked={tot} "
          f"q-interior deg_G(q) histogram={dict(sorted(worst.items()))}", flush=True)


if __name__ == '__main__':
    N = int(sys.argv[1]); W = int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 50000
    r2max = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
    run(N, W, cap, r2max)
