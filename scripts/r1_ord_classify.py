"""Enumerate all Q-colourings of the convex n-gon with exactly D colours, up to rotation/reflection
(blocking clauses on the whole orbit).  Args: n D [maxsols]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show, profile, e
from pysat.solvers import Solver
n, D = map(int, sys.argv[1:3]); mx = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
M = Model(n, D)
sols = []
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    while len(sols) < mx and S.solve():
        col = M.decode(S.get_model()); assert not check_Q(n, col)
        sols.append(col)
        ring = all(len({col[e(i, (i + l) % n)] for i in range(n)}) == 1 for l in range(1, n // 2 + 1))
        print('#', len(sols), 'profile', profile(col, D), 'ring' if ring else 'NOT ring')
        print(show(n, col))
        for r in range(n):
            for refl in (1, -1):
                f = lambda x: (refl * x + r) % n
                S.add_clause([-M.X(p, col[e(f(p[0]), f(p[1]))]) for p in M.pairs])
print('total classes', len(sols))
