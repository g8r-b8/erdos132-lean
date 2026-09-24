"""R5/B lab: local structure at core-degree-3/4 hull vertices of the Delta2-graph (Case II).

Float (tolerance 1e-9) exploration + candidate-lemma checker.  Guidance only; exact
re-checks live in r5_b_exact.py.

analyze(X) returns a dict with the layer / core data and a list of violated candidate
statements.  Status after R5/B (p in L1' of core degree k, W = core nbrs in angular order,
w a middle core nbr, r = another core nbr of w):
  K1, K1b  outer nbrs of a degree-4 p are Delta-endpoints; |r2 w1| = |r3 w4| = Delta   PROVED
  K2, K3   core degree 4 (resp. 3) => p has a Delta-partner              FALSE (n=5,6 lens sets)
  K4       r2 != r3 at a degree-4 vertex                                PROVED
  K5       |p r| != Delta at a degree-4 vertex                          open (no violation seen)
  K6       w is also a middle nbr of r                                  FALSE
  K7       r has core degree >= 3                                       FALSE
  K8       mu2 <= |L1|+|L2|+|V_Delta|                  conjecture (follows from the Charge Lemma)
  K9       mu2 <= |L1|+|L2|+mu(Delta)                                   FALSE (even rings)
  K10      every r is charged at most twice                             = Charge Lemma (conj.)
"""
from __future__ import annotations
import math, random, itertools, sys
import numpy as np

TOL = 1e-9


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull(ids, X):
    """strict hull vertices of X[ids]"""
    ids = sorted(ids, key=lambda i: (round(X[i][0], 9), round(X[i][1], 9)))
    if len(ids) <= 2:
        return set(ids)
    lo, up = [], []
    for i in ids:
        while len(lo) >= 2 and cross(X[lo[-2]], X[lo[-1]], X[i]) <= 1e-9:
            lo.pop()
        lo.append(i)
    for i in reversed(ids):
        while len(up) >= 2 and cross(X[up[-2]], X[up[-1]], X[i]) <= 1e-9:
            up.pop()
        up.append(i)
    return set(lo[:-1] + up[:-1])


def side(p, w, x):
    """sign of x relative to directed line p->w (+1 left, -1 right, 0 on)"""
    c = cross(p, w, x)
    return 0 if abs(c) < 1e-9 else (1 if c > 0 else -1)


def angular_order(p, nb, X):
    ang = {j: math.atan2(X[j][1] - X[p][1], X[j][0] - X[p][0]) for j in nb}
    s = sorted(nb, key=lambda j: ang[j])
    if len(s) <= 1:
        return s
    gaps = [(ang[s[(i + 1) % len(s)]] - ang[s[i]]) % (2 * math.pi) for i in range(len(s))]
    i0 = max(range(len(s)), key=lambda i: gaps[i])
    return s[i0 + 1:] + s[:i0 + 1]


def analyze(X):
    X = [tuple(map(float, x)) for x in X]
    n = len(X)
    A = np.array(X)
    D = np.sqrt(((A[:, None] - A[None]) ** 2).sum(-1))
    vals = []
    for d in sorted(D[np.triu_indices(n, 1)], reverse=True):
        if not vals or vals[-1] - d > TOL:
            vals.append(d)
    if len(vals) < 2:
        return None
    Dl, D2 = vals[0], vals[1]
    adj = {i: [j for j in range(n) if j != i and abs(D[i, j] - D2) < TOL] for i in range(n)}
    adjD = {i: [j for j in range(n) if j != i and abs(D[i, j] - Dl) < TOL] for i in range(n)}
    rem = list(range(n))
    Ls = []
    while rem:
        h = hull(rem, X)
        Ls.append(h)
        rem = [i for i in rem if i not in h]
    L1 = Ls[0]
    L2 = Ls[1] if len(Ls) > 1 else set()
    m3 = n - len(L1) - len(L2)
    V = L1 | L2
    core = set(V)
    ch = True
    while ch:
        ch = False
        for v in list(core):
            if sum(1 for u in adj[v] if u in core) < 2:
                core.discard(v)
                ch = True
    dc = {v: sum(1 for u in adj[v] if u in core) for v in core}
    mu2 = sum(len(a) for a in adj.values()) // 2
    muD = sum(len(a) for a in adjD.values()) // 2
    VD = {i for i in range(n) if adjD[i]}
    t = {k: sum(1 for v in core & L1 if dc[v] == k) for k in (2, 3, 4)}
    res = dict(n=n, mu2=mu2, muD=muD, VD=len(VD), L1=len(L1), L2=len(L2), m3=m3, t=t,
               core=len(core), Dl=Dl, D2=D2, viol=[], data={})
    viol = res['viol']
    # ---- candidate checks at core-degree 3/4 hull vertices
    charges_r = {}      # Delta-endpoint r  -> number of charges (excess units)
    charges_e = {}      # Delta-edge (unordered) -> number of charges
    Hedges = []
    info = []
    for p in sorted(core & L1):
        k = dc[p]
        if k < 3:
            continue
        cn = [u for u in adj[p] if u in core]
        W = angular_order(p, cn, X)  # core nbrs in angular order
        allnb = angular_order(p, adj[p], X)
        mids = W[1:-1]
        rec = dict(p=p, k=k, W=W, hasD=bool(adjD[p]), rs=[])
        for w in mids:
            others = [r for r in adj[w] if r != p and r in core]
            if not others:
                viol.append('core?')
                continue
            for r in others:
                # which outer nbr of p is on the opposite side of line p w from r?
                sr = side(X[p], X[w], X[r])
                opp = [a for a in W if a != w and side(X[p], X[w], X[a]) != 0 and side(X[p], X[w], X[a]) != sr]
                dels = [a for a in opp if abs(D[r, a] - Dl) < TOL]
                if not dels:
                    viol.append('LemmaM-fail')
                rec['rs'].append((w, r, dels, sr))
            if k == 4 and len(adj[w]) != 2:
                viol.append('middle-lemma (deg_G(w)=2)')
        info.append(rec)
        # K2/K3: p has Delta partner
        if k == 4 and not adjD[p]:
            viol.append('K2: deg4 p without Delta-partner')
        if k == 3 and not adjD[p]:
            viol.append('K3: deg3 p without Delta-partner')
        if k == 4:
            (w2, r2, d2_, _), (w3, r3, d3_, _) = rec['rs'][0], rec['rs'][-1]
            w1, w4 = W[0], W[-1]
            if w1 not in L1 or w4 not in L1 or not adjD[w1] or not adjD[w4]:
                viol.append('K1: outer nbrs of deg4 not Delta-endpoints')
            if r2 == r3:
                viol.append('K4: r2 == r3')
            for r in (r2, r3):
                if abs(D[p, r] - Dl) < TOL:
                    viol.append('K5: |p r| = Delta')
            if abs(D[r2, w1] - Dl) > TOL or abs(D[r3, w4] - Dl) > TOL:
                viol.append('K1b: |r2 w1| or |r3 w4| != Delta')
            for (w, r) in ((w2, r2), (w3, r3)):
                Hedges.append((p, r, w))
                sides = {side(X[r], X[w], X[u]) for u in adj[r] if u != w}
                if not (1 in sides and -1 in sides):
                    viol.append('K6: server w not middle for r')
                if dc.get(r, 0) < 3:
                    viol.append('K7: r has core degree 2')
            # Delta-partner position pattern relative to W
            pats = []
            for x in adjD[p]:
                o = angular_order(p, W + [x], X)
                pats.append(o.index(x))
            rec['Dpat'] = sorted(pats)
        for (w, r, dels, sr) in rec['rs']:
            charges_r[r] = charges_r.get(r, 0) + 1
            for a in dels[:1]:
                e = tuple(sorted((r, a)))
                charges_e[e] = charges_e.get(e, 0) + 1
    res['data'] = dict(info=info, charges_r=charges_r, charges_e=charges_e, Hedges=Hedges)
    excess = sum(dc[v] - 2 for v in core & L1)
    res['excess'] = excess
    # K8: mu2 <= |L1|+|L2|+|VD|  ;  K9: mu2 <= |L1|+|L2|+muD
    if mu2 > len(L1) + len(L2) + len(VD) + 1e-9:
        viol.append('K8: mu2 > |L1|+|L2|+|V_Delta|')
    if mu2 > len(L1) + len(L2) + muD + 1e-9:
        viol.append('K9: mu2 > |L1|+|L2|+mu(Delta)')
    if charges_r and max(charges_r.values()) > 2:
        viol.append('K10: some r charged > 2')
    return res


# ---------------------------------------------------------------- generators
def regular(m, rot=0.0):
    return [(math.cos(2 * math.pi * j / m + rot), math.sin(2 * math.pi * j / m + rot)) for j in range(m)]


def ring(m, S=None):
    """regular m-gon + servers on edges j in S (server of edge (j,j+1) at distance Delta2
    from both endpoints, inside)."""
    V = regular(m)
    if m % 2 == 0:
        D2 = 2 * math.cos(math.pi / m)
    else:
        D2 = 2 * math.cos(3 * math.pi / (2 * m))
    S = range(m) if S is None else S
    out = list(V)
    for j in S:
        th = 2 * math.pi * (j + .5) / m
        u = (math.cos(th), math.sin(th))
        c = V[j][0] * u[0] + V[j][1] * u[1]
        tt = -c + math.sqrt(c * c - 1 + D2 ** 2)
        out.append((-tt * u[0], -tt * u[1]))
    return out


def circ(p, q, r1, r2):
    d = math.dist(p, q)
    if d < 1e-12 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1 * r1 - r2 * r2 + d * d) / (2 * d)
    h = math.sqrt(max(r1 * r1 - a * a, 0))
    ex, ey = (q[0] - p[0]) / d, (q[1] - p[1]) / d
    mx, my = p[0] + a * ex, p[1] + a * ey
    return [(mx - h * ey, my + h * ex), (mx + h * ey, my - h * ex)]


def compatible(X, z, D2, Dl, sep=1e-3):
    for q in X:
        d = math.dist(z, q)
        if d < sep:
            return False
        if abs(d - D2) < TOL or abs(d - Dl) < TOL:
            continue
        if d > D2 - 1e-7:
            return False
    return True


def greedy_closure(X, D2, Dl, steps, rng, bias=None):
    """add circle-intersection points (radii D2/Dl) greedily maximising new D2-edges."""
    X = list(X)
    for _ in range(steps):
        best, bd = None, 0
        pairs = list(itertools.combinations(range(len(X)), 2))
        rng.shuffle(pairs)
        for a, b in pairs[:600]:
            for r1, r2 in ((D2, D2), (D2, Dl), (Dl, D2)):
                for z in circ(X[a], X[b], r1, r2):
                    if not compatible(X, z, D2, Dl):
                        continue
                    deg = sum(1 for q in X if abs(math.dist(z, q) - D2) < TOL)
                    sc = deg + rng.random() * 0.5
                    if sc > bd:
                        best, bd = z, sc
        if best is None or bd < 2:
            break
        X.append(best)
    return X


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'rings'
    if mode == 'rings':
        for m in (7, 8, 9, 10, 11, 12, 13, 15, 16):
            for S in (None, [0], [0, 1], [0, 1, 2], list(range(0, m, 2)), list(range(m // 2))):
                X = ring(m, S)
                r = analyze(X)
                print(f"m={m} S={'all' if S is None else S[:6]} n={r['n']} mu2={r['mu2']} muD={r['muD']} "
                      f"VD={r['VD']} L1={r['L1']} L2={r['L2']} t={r['t']} viol={sorted(set(r['viol']))} "
                      f"Dpat={[i.get('Dpat') for i in r['data']['info'] if i['k']==4][:1]} "
                      f"maxcharge_r={max(r['data']['charges_r'].values()) if r['data']['charges_r'] else 0}")
    elif mode == 'greedy':
        seeds, steps = int(sys.argv[2]), int(sys.argv[3])
        from collections import Counter
        C = Counter()
        best = -99
        for sd in range(seeds):
            rng = random.Random(sd)
            typ = rng.random()
            if typ < 0.4:   # regular odd/even polygon start
                m = rng.choice([5, 7, 9, 11, 6, 8, 10])
                X = regular(m)
                A = np.array(X)
                ds = sorted({round(float(x), 9) for x in np.sqrt(((A[:, None] - A[None]) ** 2).sum(-1)).ravel()}, reverse=True)
                Dl, D2 = ds[0], ds[1]
                X = rng.sample(X, rng.randint(max(3, m - 3), m))
            else:           # random seed: two Delta-points + random D2 constructions
                D2 = 1.0
                Dl = rng.uniform(1.02, 1.95)
                X = [(0.0, 0.0), (Dl, 0.0)]
                for _ in range(4):
                    a, b = rng.sample(range(len(X)), 2)
                    cs = circ(X[a], X[b], D2, rng.choice([D2, Dl]))
                    cs = [z for z in cs if compatible(X, z, D2, Dl)]
                    if cs:
                        X.append(rng.choice(cs))
            X = greedy_closure(X, D2, Dl, steps, rng)
            r = analyze(X)
            if r is None or abs(r['D2'] - D2) > 1e-6:
                continue
            for v in set(r['viol']):
                C[v.split(':')[0]] += 1
            C['sets'] += 1
            C['case2'] += r['mu2'] > r['n']
            C['has_deg4'] += r['t'][4] > 0
            C['has_deg3'] += r['t'][3] > 0
            best = max(best, r['mu2'] - r['n'])
            if r['viol'] and '-v' in sys.argv:
                print(sd, r['n'], r['mu2'], r['t'], sorted(set(r['viol'])))
        print(dict(C), 'best mu2-n', best)
