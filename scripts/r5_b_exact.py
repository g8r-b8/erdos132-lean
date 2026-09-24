"""R5/B exact adversarial checks (integer lattices Z[omega], Z[i]; exact arithmetic).

For every maximal clique of a lattice compatibility pool (as in va1c_random.py pool mode: p = 0
forced extreme, all pairs at squared distance <= r2 or == d2) we recompute Delta, Delta2, layers,
the Delta2-graph G and its 2-core exactly and test:

  LS   local structure at p in L1 with core degree >= 3 (proved in R5_B notes, Thm 1):
       every middle core neighbour w of p is G-position 2 or h-1 (h = deg_G p);
       deg_G(w) = 2 unless h = 3; if h = 3, w has at most one other neighbour on each side
       of line pw; every other neighbour x of w is at distance Delta from the outer
       G-neighbour of p on the far side of line pw from x.
  TZ   trapezoid lemma (proved, Thm 2): for a hook (p,w,x;b) and a unit neighbour u of x strictly
       on the far side of line xw from p:  |up| = Delta, x,p,b,u concyclic, xp || ub,
       w on the same side of line xp as u and b.
  CX   charge lemma (conjecture): each x lies in at most one hook of each orientation.
  CB   dual charge (conjecture): each b lies in at most one hook of each orientation.
  K8   mu2 <= |L1| + |L2| + |V_Delta|  (consequence of CX).

A hook is (p, w, x; b): p extreme, w a middle Delta2-neighbour of p (p has Delta2-neighbours
strictly on both sides of line pw), x != p a Delta2-neighbour of w, b the outer (first/last)
Delta2-neighbour of p strictly on the far side of line pw from x with |xb| = Delta.
Orientation of a hook = side of p w.r.t. the directed line x->w.

usage: python3 r5_b_exact.py tri|sq R2MAX [cap]
"""
from __future__ import annotations
import sys, functools
from collections import Counter
from va1_common import qform, hull_vertices, layers, two_core
from va1_clique import maximal_cliques


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


EPS = [0]


def sgn(v):
    if isinstance(v, float) and abs(v) < EPS[0]:
        return 0
    return (v > 0) - (v < 0)


def order_in_halfplane(p, nb, X):
    """exact angular order of nb around extreme p (all in an open half-plane at p)"""
    def cmp(a, b):
        c = sgn(cross(X[p], X[a], X[b]))
        return -c
    return sorted(nb, key=functools.cmp_to_key(cmp))


def check(X, kind, C):
    n = len(X)
    D = [[qform(kind, X[i][0] - X[j][0], X[i][1] - X[j][1]) for j in range(n)] for i in range(n)]
    vals = sorted({D[i][j] for i in range(n) for j in range(i + 1, n)}, reverse=True)
    if len(vals) < 2:
        return
    Dl, D2 = vals[0], vals[1]
    adj = {i: [j for j in range(n) if j != i and D[i][j] == D2] for i in range(n)}
    adjD = {i: [j for j in range(n) if j != i and D[i][j] == Dl] for i in range(n)}
    Ls = layers(X)
    L1 = Ls[0]
    L2 = Ls[1] if len(Ls) > 1 else set()
    core = two_core(L1 | L2, adj)
    mu2 = sum(len(a) for a in adj.values()) // 2
    VD = sum(1 for i in range(n) if adjD[i])
    C['sets'] += 1
    C['case2'] += mu2 > n
    viol = []
    if mu2 > len(L1) + len(L2) + VD:
        viol.append('K8')
    hooks = []
    for p in L1:
        W = order_in_halfplane(p, adj[p], X)
        h = len(W)
        cn = [u for u in W if u in core]
        if p in core and len(cn) >= 3:
            C['LS-tested'] += 1
            for w in cn[1:-1]:
                pos = W.index(w)
                oth = [x for x in adj[w] if x != p]
                if oth and pos not in (1, h - 2):
                    viol.append('LS-position')
                if h >= 4 and len(adj[w]) > 2:
                    viol.append('LS-deg2')
                if h == 3:
                    sides = Counter(sgn(cross(X[p], X[w], X[x])) for x in oth)
                    if sides[1] > 1 or sides[-1] > 1:
                        viol.append('LS-h3')
        for i in range(1, h - 1):
            w = W[i]
            for x in adj[w]:
                if x == p:
                    continue
                sx = sgn(cross(X[p], X[w], X[x]))
                outs = [a for a in (W[0], W[-1]) if sgn(cross(X[p], X[w], X[a])) == -sx]
                bs = [a for a in outs if D[x][a] == Dl]
                if sx != 0 and not bs:
                    viol.append('LS-Delta')
                    continue
                if sx == 0:
                    C['online'] += 1
                for b in bs:
                    hooks.append((p, w, x, b))
    C['hooks'] += len(hooks)
    cx, cb = Counter(), Counter()
    for (p, w, x, b) in hooks:
        o = sgn(cross(X[x], X[w], X[p]))
        cx[(x, o)] += 1
        cb[(b, sgn(cross(X[p], X[w], X[x])))] += 1
        # trapezoid lemma
        for u in adj[x]:
            if u != w and sgn(cross(X[x], X[w], X[u])) == -o and o != 0:
                C['TZ-tested'] += 1
                if D[u][p] != Dl:
                    viol.append('TZ-Delta')
                    continue
                # xp || ub  <=> cross(p - x, b - u) == 0 ; w and u,b same side of line xp
                par = (X[p][0] - X[x][0]) * (X[b][1] - X[u][1]) - (X[p][1] - X[x][1]) * (X[b][0] - X[u][0])
                if sgn(par) != 0:
                    viol.append('TZ-parallel')
                if sgn(cross(X[x], X[p], X[w])) != sgn(cross(X[x], X[p], X[b])) or \
                        sgn(cross(X[x], X[p], X[u])) != sgn(cross(X[x], X[p], X[b])):
                    viol.append('TZ-side')
    hookset = {(p, w, x) for (p, w, x, b) in hooks}
    for (p, w, x, b) in hooks:
        # Lemma F' at x: at most one unit nbr of x strictly on the far side of line xw from p
        o = sgn(cross(X[x], X[w], X[p]))
        far = [u for u in adj[x] if u != w and sgn(cross(X[x], X[w], X[u])) == -o]
        if len(far) > 1:
            viol.append("F'")
        near = [u for u in adj[x] if u != w and sgn(cross(X[x], X[w], X[u])) == o]
        # reversed hook: if w is a middle nbr of x (x extreme), then (x, w, p) is a hook
        if x in L1 and far and near and (x, w, p) not in hookset:
            viol.append('REV')
        C['hooks-symmetric' if (far and near) else 'hooks-asymmetric'] += 1
    for p in core & L1:
        cn = [u for u in order_in_halfplane(p, adj[p], X) if u in core]
        if len(cn) == 4:
            r2 = {x for x in adj[cn[1]] if x != p}
            r3 = {x for x in adj[cn[2]] if x != p}
            if r2 & r3:
                viol.append('K4')
    if cx and max(cx.values()) > 1:
        viol.append('CX')
    if cb and max(cb.values()) > 1:
        viol.append('CB')
    for v in set(viol):
        C['VIOL ' + v] += 1
    if viol and C['printed'] < 5:
        C['printed'] += 1
        print('VIOL', sorted(set(viol)), X, flush=True)


def run(kind, r2max, cap):
    R = 40
    P = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)]
    norms = sorted({qform(kind, *p) for p in P} - {0})
    euy = (lambda v: v[1]) if kind == 'sq' else (lambda v: v[1])  # sign of y is basis-invariant here
    halfp = lambda v: v[1] > 0 or (v[1] == 0 and v[0] > 0)
    C = Counter()
    for r2 in [x for x in norms if x <= r2max]:
        nbrs = [p for p in P if qform(kind, *p) == r2 and halfp(p)]
        if len(nbrs) < 3:
            continue
        for d2 in [x for x in norms if r2 < x <= 4 * r2]:
            pool = [p for p in P if 0 < qform(kind, *p) <= d2 and halfp(p)
                    and (qform(kind, *p) <= r2 or qform(kind, *p) == d2)]
            m = len(pool)
            nb = [0] * m
            for i in range(m):
                for j in range(i + 1, m):
                    s = qform(kind, pool[i][0] - pool[j][0], pool[i][1] - pool[j][1])
                    if s <= r2 or s == d2:
                        nb[i] |= 1 << j
                        nb[j] |= 1 << i
            cl = maximal_cliques(nb, m, cap)
            if len(cl) >= cap:
                C['CAP'] += 1
            for c in cl:
                X = [(0, 0)] + [pool[i] for i in range(m) if c >> i & 1]
                check(X, kind, C)
    print(kind, r2max, dict(C))


def run_float(X, C, eps=1e-7):
    """float point sets: squared distances quantised by qform('flt'); cross signs with tolerance"""
    EPS[0] = eps
    check([tuple(map(float, q)) for q in X], 'flt', C)


if __name__ == '__main__':
    run(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 20000)
