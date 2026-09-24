"""Which sets of colours can simultaneously be frequent (size >= n+1)?  n, D, F: tests every F-subset of colours.
Also reports, for each feasible set, one profile."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, profile
from pysat.solvers import Solver
n, D, F = map(int, sys.argv[1:4])
M = Model(n, D)
sel = {}
for c in range(1, D + 1):
    f = M.pool.id(('f', c)); sel[c] = f; M.size_geq(c, n + 1, sel=f)
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    for T in itertools.combinations(range(1, D + 1), F):
        r = S.solve(assumptions=[sel[c] for c in T])
        if r:
            col = M.decode(S.get_model()); assert not check_Q(n, col)
            print(T, 'FEASIBLE', profile(col, D), flush=True)
        else:
            print(T, 'infeasible', flush=True)
