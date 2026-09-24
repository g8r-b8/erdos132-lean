"""Ordinal strictly anti-Monge (supermodular) p x q matrices: for rows a<b, cols c<d,
NOT( sorted(A[a][c],A[b][d]) <= sorted(A[a][d],A[b][c]) coordinatewise ).
Question: min number of distinct values.  Args: p q V  -> SAT if a matrix with <= V values exists."""
import sys, itertools
from pysat.formula import IDPool
from pysat.solvers import Solver

def build(p, q, V, extra=None):
    pool = IDPool(); cl = []
    Y = lambda a, c, t: pool.id(('y', a, c, t))
    def geq(a, c, t):
        return True if t <= 1 else (False if t > V else Y(a, c, t))
    for a in range(p):
        for c in range(q):
            for t in range(3, V + 1):
                cl.append([-Y(a, c, t), Y(a, c, t - 1)])
    Lc = {}
    def Lle(x, y):
        if (x, y) in Lc: return Lc[(x, y)]
        v = pool.id(('L', x, y)); Lc[(x, y)] = v
        for t in range(1, V + 1):
            A = geq(*x, t + 1); B = geq(*y, t)
            lits = [A, (True if B is False else (False if B is True else -B)), v]
            if any(l is True for l in lits): continue
            cl.append([l for l in lits if l is not False])
        return v
    for a, b in itertools.combinations(range(p), 2):
        for c, d in itertools.combinations(range(q), 2):
            d1, d2, s1, s2 = (a, c), (b, d), (a, d), (b, c)
            for (x, y), (x2, y2) in (((d1, s1), (d2, s2)), ((d1, s2), (d2, s1))):
                cl.append([-Lle(x, y), -Lle(x2, y2)])
    return pool, cl, geq

if __name__ == '__main__':
    p, q, V = map(int, sys.argv[1:4])
    pool, cl, geq = build(p, q, V)
    with Solver(name='cadical153', bootstrap_with=cl) as S:
        r = S.solve()
        print(p, q, V, 'SAT' if r else 'UNSAT')
        if r:
            m = set(l for l in S.get_model() if l > 0)
            for a in range(p):
                print(' '.join(str(max([1] + [t for t in range(2, V + 1) if pool.id(('y', a, c, t)) in m])) for c in range(q)))
