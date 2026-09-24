"""Conjecture PK(t): in a Q-colouring of the pairs of a convex n-gon with D colours (all used), the top t colour
classes have at most t*n pairs in total (t < n/2).  Search for violations.  Args: n D t [bound]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show, profile
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
n, D, t = map(int, sys.argv[1:4]); bound = int(sys.argv[4]) if len(sys.argv) > 4 else t * n
M = Model(n, D)
lits = []
for p in M.pairs:
    g = M.geq(p, D - t + 1)
    if g is True:
        x = M.pool.id(('T', p)); M.cl.append([x]); lits.append(x)
    elif g is not False:
        lits.append(g)
if bound + 1 > len(lits):
    print(n, D, t, bound, 'ok (trivial)'); sys.exit()
M.cl += CardEnc.atleast(lits, bound + 1, vpool=M.pool, encoding=EncType.seqcounter).clauses
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    r = S.solve(); print(n, D, t, bound, 'VIOLATION' if r else 'ok', flush=True)
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(profile(col, D)); print(show(n, col))
