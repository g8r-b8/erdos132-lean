"""Adversarial tests for VERIFY_A1c.md (deg_{G'}(p) <= 4 for p in L1', and the stronger
G-level Lemma F: if p is extreme and its Delta2-neighbours are w_1..w_k in angular order,
then w_3..w_{k-2} have deg_G = 1).

extra(X, kind) runs va1_common.analyze (Theorem A, A1, Unconditional form, Props 3,5-8, CDL,
3n/2) and additionally checks
   'deg4'  : total core degree <= 4 on L1' (the claim of VERIFY_A1c),
   'LemmaF': the G-level statement above for every hull vertex p.

Modes
  pool KIND R2MAX [cap]   KIND in tri|sq (exact) or cycN_W (float, sums of <= W N-th roots).
      p = 0 is forced extreme by restricting the pool to the open half-plane
      {y > 0} u {y = 0, x > 0}, intersected with D(0, Delta).  Every pair must have
      squared distance <= r2 or == d2.  All maximal cliques (Bron-Kerbosch) are checked.
      The Lemma F failure at p = 0 is monotone under adding compatible points, so
      maximal cliques are exhaustive for it within the pool.
  greedy SEEDS STEPS      float greedy constructions: p = 0 with 5-7 unit neighbours in a
      half-plane arc, then repeatedly add circle-intersection points (radius 1 / Delta)
      that are compatible, preferring points adjacent to middle neighbours of p.
"""
import sys, math, random, itertools
from va1_common import qform, analyze, hull_vertices, layers, two_core
from va1_clique import maximal_cliques
from va1_cyclo import pool_pts


def euc(kind, v):
    if kind == 'tri':
        return (v[0] + v[1] / 2, v[1] * math.sqrt(3) / 2)
    return (float(v[0]), float(v[1]))


def extra(X, kind):
    res = analyze(X, kind)
    if res is None:
        return None
    n = len(X)
    D = [[qform(kind, X[i][0] - X[j][0], X[i][1] - X[j][1]) for j in range(n)] for i in range(n)]
    D2 = res['Delta2']
    adj = {i: [j for j in range(n) if j != i and D[i][j] == D2] for i in range(n)}
    L = layers(X)
    L1, L2 = L[0], (L[1] if len(L) > 1 else set())
    core = two_core(L1 | L2, adj)
    for v in core & L1:
        dc = sum(1 for u in adj[v] if u in core)
        if dc > 4:
            res['viol'].append(f'deg4: hull vertex {X[v]} core degree {dc}')
    for p in L1:
        nb = adj[p]
        if len(nb) < 5:
            continue
        P = euc(kind, X[p])
        ang = {j: math.atan2(euc(kind, X[j])[1] - P[1], euc(kind, X[j])[0] - P[0]) for j in nb}
        # rotate so that the angular order is linear (p extreme => all in an open half-plane)
        s = sorted(nb, key=lambda j: ang[j])
        gaps = [(ang[s[(i + 1) % len(s)]] - ang[s[i]]) % (2 * math.pi) for i in range(len(s))]
        i0 = max(range(len(s)), key=lambda i: gaps[i])
        order = s[i0 + 1:] + s[:i0 + 1]
        for w in order[2:-2]:
            if len(adj[w]) != 1:
                res['viol'].append(f'LemmaF: deep-middle nbr {X[w]} of {X[p]} has deg_G {len(adj[w])}')
    return res


def pool_mode(kind, r2max, cap):
    if kind.startswith('cyc'):
        N, W = map(int, kind[3:].split('_'))
        P = pool_pts(N, W)
        k = 'flt'
        norms = sorted({qform(k, *p) for p in P} - {0})
        r2s = [x for x in norms if x <= r2max * 1e8]
    else:
        k = kind
        R = 40
        P = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)]
        norms = sorted({qform(k, *p) for p in P} - {0})
        r2s = [x for x in norms if x <= r2max]
    halfp = lambda v: euc(k, v)[1] > 1e-9 or (abs(euc(k, v)[1]) <= 1e-9 and euc(k, v)[0] > 0)
    tot = nviol = nh5 = 0
    for r2 in r2s:
        nbrs = [p for p in P if qform(k, *p) == r2 and halfp(p)]
        if len(nbrs) < 5:
            continue
        for d2 in [x for x in norms if r2 < x <= 4 * r2]:
            pool = [p for p in P if 0 < qform(k, *p) <= d2 and halfp(p)
                    and (qform(k, *p) <= r2 or qform(k, *p) == d2)]
            m = len(pool)
            nb = [0] * m
            for i in range(m):
                for j in range(i + 1, m):
                    s = qform(k, pool[i][0] - pool[j][0], pool[i][1] - pool[j][1])
                    if s <= r2 or s == d2:
                        nb[i] |= 1 << j
                        nb[j] |= 1 << i
            cl = maximal_cliques(nb, m, cap)
            for c in cl:
                X = [(0, 0) if k != 'flt' else (0.0, 0.0)] + [pool[i] for i in range(m) if c >> i & 1]
                res = extra(X, k)
                if res is None:
                    continue
                tot += 1
                nh5 += res['maxh'] >= 5
                if res['viol']:
                    nviol += 1
                    print('VIOL', kind, r2, d2, res['viol'][:3], X, flush=True)
            print(f'{kind} r2={r2} d2={d2} pool={m} cliques={len(cl)}{" CAP" if len(cl) >= cap else ""}', flush=True)
    print(f'TOTAL {kind}: sets checked={tot} with a hull vertex of h>=5 (Lemma F non-vacuous)={nh5} '
          f'violating sets={nviol}')


TOL = 1e-9


def circ(p, q, r1, r2):
    d = math.dist(p, q)
    if d < 1e-12 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h = math.sqrt(max(r1 * r1 - a * a, 0))
    ex, ey = (q[0] - p[0]) / d, (q[1] - p[1]) / d
    mx, my = p[0] + a * ex, p[1] + a * ey
    return [(mx - h * ey, my + h * ex), (mx + h * ey, my - h * ex)]


def compatible(X, z, Dl):
    for q in X:
        d = math.dist(z, q)
        if d < 1e-3:     # keep points well separated: avoids float-collinearity artefacts in the hull code
            return False
        if abs(d - 1) < TOL or abs(d - Dl) < TOL:
            continue
        if d > 1 - 1e-6:
            return False
    return True


def snap(X, Dl):
    """Quantise: build exact-ish 'flt' coordinates (qform rounds sq. distances to 1e-8)."""
    return [(round(x, 12), round(y, 12)) for x, y in X]


def greedy(seeds, steps):
    tot = nviol = nh5 = 0
    best = 0
    for sd in range(seeds):
        rng = random.Random(sd)
        k = rng.choice([5, 6, 7])
        mode = rng.random()
        if mode < 0.5:   # all within 60 degrees
            angs = sorted(rng.uniform(0, math.pi / 3) for _ in range(k))
            if min(b - a for a, b in zip(angs, angs[1:])) < 0.02:
                continue
            Dl = rng.uniform(1.05, 2.0)
        else:            # two clusters at angular distance theta_Delta
            th = rng.uniform(math.pi / 3 + 0.05, 2 * math.pi / 3)
            Dl = 2 * math.sin(th / 2)
            a = [0.0, th] + [rng.uniform(th - math.pi / 3, math.pi / 3) for _ in range(k - 2)]
            angs = sorted(a)
            if min(b - a for a, b in zip(angs, angs[1:])) < 0.02:
                continue
        X = [(0.0, 0.0)] + [(math.cos(t), math.sin(t)) for t in angs]
        if not all(compatible(X[:i], X[i], Dl) for i in range(1, len(X))):
            continue
        W = X[1:]
        for _ in range(steps):
            cands = []
            src = W[2:-2] if rng.random() < 0.7 else X
            for u in src:
                for v in rng.sample(X, min(len(X), 6)):
                    if u == v:
                        continue
                    for r2 in (1.0, Dl):
                        cands += circ(u, v, 1.0, r2)
            rng.shuffle(cands)
            for z in cands[:60]:
                if compatible(X, z, Dl):
                    X.append(z)
                    break
        Xs = snap(X, Dl)
        res = extra(Xs, 'flt')
        if res is None:
            continue
        tot += 1
        nh5 += res['maxh'] >= 5
        best = max(best, res['mu2'] - res['n'])
        if res['viol']:
            nviol += 1
            print('VIOL seed', sd, res['viol'][:3], flush=True)
    print(f'greedy: sets={tot} with h>=5 hull vertex={nh5} violating={nviol} best mu2-n={best}')


if __name__ == '__main__':
    if sys.argv[1] == 'pool':
        pool_mode(sys.argv[2], float(sys.argv[3]) if sys.argv[2].startswith('cyc') else int(sys.argv[3]),
                  int(sys.argv[4]) if len(sys.argv) > 4 else 20000)
    else:
        greedy(int(sys.argv[2]), int(sys.argv[3]))
