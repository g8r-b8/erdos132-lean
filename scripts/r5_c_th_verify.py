"""R5/C theory: EXACT verification (sympy) of a point set: exact distinct squared distances
(sorted exactly via minimal-polynomial-certified comparisons), top multiplicities, strict convex
layers with exact orientation signs, Delta_j-graph, its 2-core and core degrees by layer.
usage: .venv/bin/python r5_c_th_verify.py <name>   (named examples below)"""
import sys
import sympy as sp
from collections import Counter, defaultdict

s3 = sp.sqrt(3)


def e(deg):
    return (sp.cos(sp.pi * sp.Rational(deg, 180)), sp.sin(sp.pi * sp.Rational(deg, 180)))


def add(a, b):
    return (sp.nsimplify(a[0] + b[0]), sp.nsimplify(a[1] + b[1]))


def sgn(x):
    x = sp.nsimplify(sp.radsimp(sp.expand(x)))
    if x == 0:
        return 0
    v = sp.N(x, 50)
    if abs(v) < 1e-40:  # certify zero
        assert sp.minimal_polynomial(x, sp.Symbol('y')) == sp.Symbol('y'), x
        return 0
    return 1 if v > 0 else -1


def cross(o, a, b):
    return sgn((a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]))


def strict_hull(idx, P):
    """strict extreme points: p is extreme iff not in conv of others.  O(n^3) exact test:
    p non-extreme iff p in some closed triangle of the others or on a segment of two others."""
    out = set()
    for i in idx:
        others = [j for j in idx if j != i]
        inside = False
        for a in range(len(others)):
            for b in range(a + 1, len(others)):
                A, B = P[others[a]], P[others[b]]
                if cross(A, B, P[i]) == 0 and sgn((P[i][0]-A[0])*(P[i][0]-B[0]) + (P[i][1]-A[1])*(P[i][1]-B[1])) <= 0:
                    inside = True; break
                for c in range(b + 1, len(others)):
                    C = P[others[c]]
                    s1, s2, s3_ = cross(A, B, P[i]), cross(B, C, P[i]), cross(C, A, P[i])
                    if (s1 >= 0 and s2 >= 0 and s3_ >= 0) or (s1 <= 0 and s2 <= 0 and s3_ <= 0):
                        if cross(A, B, C) != 0:
                            inside = True; break
                if inside:
                    break
            if inside:
                break
        if not inside:
            out.add(i)
    return out


def layers(P):
    rem = list(range(len(P)))
    dep = {}
    k = 1
    while rem:
        L = strict_hull(rem, P) if len(rem) > 2 else set(rem)
        for i in L:
            dep[i] = k
        rem = [i for i in rem if i not in L]
        k += 1
    return dep


def analyse(P, J=3, name=''):
    n = len(P)
    D = {}
    for i in range(n):
        for j in range(i + 1, n):
            D[(i, j)] = sp.nsimplify(sp.radsimp(sp.expand((P[i][0]-P[j][0])**2 + (P[i][1]-P[j][1])**2)))
    # exact classes
    items = sorted(D.items(), key=lambda kv: -sp.N(kv[1], 50))
    cls = []
    for k, v in items:
        if cls and sgn(cls[-1][0] - v) == 0:
            cls[-1][1].append(k)
        else:
            cls.append([v, [k]])
    for a, b in zip(cls, cls[1:]):
        assert sgn(a[0] - b[0]) == 1
    dep = layers(P)
    print(f'== {name}: n={n}, layers {dict(sorted(Counter(dep.values()).items()))}')
    print('   top squared distances:', [(sp.nsimplify(c[0]), len(c[1])) for c in cls[:J + 1]])
    for jj in range(J):
        E = cls[jj][1]
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
        cd = defaultdict(Counter)
        for v in alive:
            cd[dep[v]][len(adj[v] & alive)] += 1
        types = Counter(tuple(sorted((dep[a], dep[b]))) for a, b in E)
        print(f'   D{jj+1}: mu={len(E)} types={dict(types)} coredeg by layer={ {k: dict(v) for k, v in sorted(cd.items())} }')
    return dep, cls


def ex_tri10():
    v = [e(0), e(120), e(240)]
    P = [(sp.Integer(0), sp.Integer(0))] + v
    for i in range(3):
        for s in (150, -150):
            P.append(add(v[i], e(120 * i + s)))
    return P


def ex_hex7():
    return [(sp.Integer(0), sp.Integer(0))] + [e(60 * i) for i in range(6)]


def ex_deg4L3():
    s_ = 2 * sp.sin(sp.pi / 18)
    P = [(sp.Integer(0), sp.Integer(0))]
    for a in (20, 80, 160, 300):
        c, d = e(a)
        P += [(c, d), (s_ * c, s_ * d)]
    return P


EX = {'tri10': ex_tri10, 'hex7': ex_hex7, 'deg4L3': ex_deg4L3}

if __name__ == '__main__':
    for nm in (sys.argv[1:] or EX):
        P = EX[nm]()
        analyse(P, 3, nm)
        print('   points:', P)
