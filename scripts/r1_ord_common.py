"""R1 (ordinal angle): compact SAT model of Q-colourings of the pairs of a convex n-gon.

Colours 1..D (ordered).  Order literals Y(p,t) <=> c(p) >= t (t = 2..D).  Lemma Q (ordinal quadrilateral
inequality): for i<j<k<l, diagonals {ik, jl}, opposite sides {ij,kl} or {jk,li}: NOT(sorted diag <= sorted
sides coordinatewise)  <=>  no matching diag->side with c(diag) <= c(side) on both.  Encoded with aux literal
L(a,b) implied by c(a) <= c(b).  Helpers to add extra constraints (colour classes, counts)."""
import itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType


def e(i, j):
    return (i, j) if i < j else (j, i)


class Model:
    def __init__(self, n, D, all_used=True, quads=None):
        self.n, self.D = n, D
        self.pool = IDPool()
        self.cl = []
        self.pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        self._L = {}
        for p in self.pairs:
            for t in range(3, D + 1):
                self.cl.append([-self.Y(p, t), self.Y(p, t - 1)])
        for q in (itertools.combinations(range(n), 4) if quads is None else quads):
            self.add_Q(*q)
        if all_used:
            for c in range(1, D + 1):
                self.cl.append([self.X(p, c) for p in self.pairs])

    # literal: c(p) >= t   (t<=1 -> True, t>D -> False) ; returned as list-of-literal semantics via helpers
    def Y(self, p, t):
        return self.pool.id(('y', p, t))

    def geq(self, p, t):
        """literal for c(p) >= t, or True/False"""
        if t <= 1:
            return True
        if t > self.D:
            return False
        return self.Y(p, t)

    def X(self, p, c):
        """literal <=> c(p) == c (defined lazily)"""
        key = ('x', p, c)
        new = key not in self.pool.obj2id
        v = self.pool.id(key)
        if new:
            a, b = self.geq(p, c), self.geq(p, c + 1)
            # v <-> a & ~b
            if a is True and b is False:
                self.cl.append([v])
            elif a is True:
                self.cl += [[-v, -b], [b, v]]
            elif b is False:
                self.cl += [[-v, a], [-a, v]]
            else:
                self.cl += [[-v, a], [-v, -b], [-a, b, v]]
        return v

    def clause(self, lits):
        """add clause; lits may contain True/False"""
        if any(l is True for l in lits):
            return
        self.cl.append([l for l in lits if l is not False])

    def Lle(self, a, b):
        """literal implied by c(a) <= c(b)"""
        key = (a, b)
        if key in self._L:
            return self._L[key]
        v = self.pool.id(('L', a, b))
        self._L[key] = v
        for t in range(1, self.D + 1):
            # c(a) <= t and c(b) >= t -> v
            A = self.geq(a, t + 1)       # c(a) >= t+1  (False if t = D)
            B = self.geq(b, t)
            lits = [A]
            lits.append(True if B is False else (False if B is True else -B))
            lits.append(v)
            self.clause(lits)
        return v

    def add_Q(self, i, j, k, l):
        d1, d2 = e(i, k), e(j, l)
        for s1, s2 in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            for (a, b), (a2, b2) in (((d1, s1), (d2, s2)), ((d1, s2), (d2, s1))):
                self.cl.append([-self.Lle(a, b), -self.Lle(a2, b2)])

    def size_geq(self, c, k, sel=None):
        lits = [self.X(p, c) for p in self.pairs]
        enc = CardEnc.atleast(lits=lits, bound=k, vpool=self.pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            self.cl.append(cl + ([-sel] if sel else []))

    def size_leq(self, c, k, sel=None):
        lits = [self.X(p, c) for p in self.pairs]
        enc = CardEnc.atmost(lits=lits, bound=k, vpool=self.pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            self.cl.append(cl + ([-sel] if sel else []))

    def decode(self, model):
        m = set(l for l in model if l > 0)
        col = {}
        for p in self.pairs:
            c = 1
            for t in range(2, self.D + 1):
                if self.Y(p, t) in m:
                    c = t
            col[p] = c
        return col


def check_Q(n, col):
    """independent brute-force check of Lemma Q; returns list of violations"""
    bad = []
    for i, j, k, l in itertools.combinations(range(n), 4):
        x = sorted((col[e(i, k)], col[e(j, l)]))
        for s in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            y = sorted((col[s[0]], col[s[1]]))
            if x[0] <= y[0] and x[1] <= y[1]:
                bad.append((i, j, k, l, s))
    return bad


def show(n, col):
    D = max(col.values())
    rows = []
    for i in range(n):
        rows.append(' '.join('.' if i == j else f"{col[e(i, j)]:x}" for j in range(n)))
    return '\n'.join(rows)


def profile(col, D):
    cnt = [0] * (D + 1)
    for v in col.values():
        cnt[v] += 1
    return cnt[1:]
