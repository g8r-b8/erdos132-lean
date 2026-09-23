"""Exact checker for Theorem A / Corollary A1 (angle_C.md) and the CDL-cited
Vesztergombi propositions (obs. (1)-(8) in CDL's proof of Thm 1.3).

Points are integer lattice coordinates (a, b).  kind='tri' means a + b*omega
(omega = e^{2 pi i/3}... we use the form a^2+ab+b^2, i.e. basis 1, e^{i pi/3});
kind='sq' means a + b*i.  Orientation tests are done in (a, b) coordinates,
which is valid because the lattice basis map is linear with positive
determinant.  Everything is exact integer arithmetic.
"""
from __future__ import annotations


def qform(kind, da, db):
    if kind == 'flt':  # float coordinates; squared distance quantised to 1e-8
        return round((da * da + db * db) * 1e8)
    if kind == 'tri':
        return da * da + da * db + db * db
    return da * da + db * db


def cross(o, a, b):
    c = (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    if isinstance(c, float) and abs(c) < 1e-9:
        return 0
    return c


def hull_vertices(pts):
    """Indices (into pts) of strict hull vertices (collinear boundary points excluded)."""
    def _k(p):  # round floats so near-equal x-coordinates sort consistently
        return tuple(round(c, 9) if isinstance(c, float) else c for c in p)
    idx = sorted(range(len(pts)), key=lambda i: _k(pts[i]))
    # dedupe not needed (distinct points assumed)
    if len(idx) <= 2:
        return set(idx)
    lower, upper = [], []
    for i in idx:
        while len(lower) >= 2 and cross(pts[lower[-2]], pts[lower[-1]], pts[i]) <= 0:
            lower.pop()
        lower.append(i)
    for i in reversed(idx):
        while len(upper) >= 2 and cross(pts[upper[-2]], pts[upper[-1]], pts[i]) <= 0:
            upper.pop()
        upper.append(i)
    return set(lower[:-1] + upper[:-1])


def layers(pts):
    rem = list(range(len(pts)))
    out = []
    while rem:
        sub = [pts[i] for i in rem]
        hv = hull_vertices(sub)
        L = {rem[i] for i in hv}
        out.append(L)
        rem = [i for i in rem if i not in L]
    return out


def two_core(V, adj):
    core = set(V)
    changed = True
    while changed:
        changed = False
        for v in list(core):
            if sum(1 for u in adj[v] if u in core) < 2:
                core.discard(v)
                changed = True
    return core


def analyze(pts, kind):
    """Return a dict of quantities and a list of violated claims."""
    n = len(pts)
    D = [[qform(kind, pts[i][0] - pts[j][0], pts[i][1] - pts[j][1]) for j in range(n)] for i in range(n)]
    vals = sorted({D[i][j] for i in range(n) for j in range(i + 1, n)}, reverse=True)
    res = {'n': n, 'viol': []}
    if len(vals) < 2:
        return None
    Dl, D2 = vals[0], vals[1]
    adj = {i: [j for j in range(n) if j != i and D[i][j] == D2] for i in range(n)}
    adjD = {i: [j for j in range(n) if j != i and D[i][j] == Dl] for i in range(n)}
    mu2 = sum(len(v) for v in adj.values()) // 2
    Ls = layers(pts)
    L1 = Ls[0]
    L2 = Ls[1] if len(Ls) > 1 else set()
    m3 = n - len(L1) - len(L2)
    V = L1 | L2
    # obs (1),(2): all Delta2 pairs inside L1 u L2 and each has an L1 endpoint
    for i in range(n):
        for j in adj[i]:
            if i < j:
                if not (i in L1 or j in L1):
                    res['viol'].append('obs1: D2 edge with no L1 endpoint')
                if not (i in V and j in V):
                    res['viol'].append('obs2: D2 edge leaves L1uL2')
    for i in range(n):
        for j in adjD[i]:
            if not (i in L1 and j in L1):
                res['viol'].append('obs1: Delta edge not in L1')
    core = two_core(V, adj)
    dc = {v: sum(1 for u in adj[v] if u in core) for v in core}
    L1c = core & L1
    L2c = core & L2
    for v in L2c:
        if dc[v] != 2:
            res['viol'].append(f'Prop3: L2 core vertex {pts[v]} has core degree {dc[v]}')
    for v in L1c:
        d1 = sum(1 for u in adj[v] if u in L1c)
        d2 = sum(1 for u in adj[v] if u in L2c)
        if d2 > 2:
            res['viol'].append('Prop5')
        if d1 == 3 and d2 > 1:
            res['viol'].append('Prop6')
        if d1 == 4 and d2 > 0:
            res['viol'].append('Prop7')
        if d1 > 4:
            res['viol'].append('Prop8')
    # L2' independent (obs 3)
    for v in L2c:
        if any(u in L2c for u in adj[v]):
            res['viol'].append('obs3')
    thmA2 = 2 * (len(L1) + len(L2)) + sum(dc[v] - 2 for v in L1c)  # 2x bound
    if 2 * mu2 > thmA2:
        res['viol'].append(f'ThmA: mu2={mu2} > {thmA2/2}')
    h = {v: len(adj[v]) for v in range(n)}
    H3 = all(h[v] <= 3 for v in L1)
    if H3 and 2 * mu2 > 3 * len(L1) + 2 * len(L2):
        res['viol'].append(f'A1: mu2={mu2} > 1.5|L1|+|L2|')
    unc = sum(max(min(h[v], 4) - 2, 0) for v in L1)
    if unc <= 2 * m3 and mu2 > n:
        res['viol'].append('Unconditional form')
    cdl = min(3 * (len(L1) + len(L2)) / 2, 4 * len(L1) / 3 + 2 * len(L2), 2 * len(L1) + len(L2))
    if mu2 > cdl + 1e-9:
        res['viol'].append('CDL Thm1.3 bound')
    if 2 * mu2 > 3 * n:
        res['viol'].append('Vesztergombi 3n/2')
    res.update(mu2=mu2, L1=len(L1), L2=len(L2), m3=m3, core=len(core),
               thmA=thmA2 / 2, H3=H3, maxh=max(h[v] for v in L1), cdl=cdl,
               Delta2=D2, Delta=Dl, L2deg={pts[v]: len(adj[v]) for v in L2 if adj[v]})
    return res
