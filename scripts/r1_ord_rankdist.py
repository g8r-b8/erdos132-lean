"""Test conjecture RD: in every Q-colouring (colours = ranks 1..D, all used), c(i,j) >= cyclic distance d(i,j).
Search for c(0,k) <= k-1.  Args: n D k"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show
from pysat.solvers import Solver
n, D, k = map(int, sys.argv[1:4])
M = Model(n, D)
M.clause([False if M.geq((0, k), k) is True else (-M.geq((0, k), k) if M.geq((0, k), k) is not False else True)])
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    r = S.solve(); print(n, D, k, 'VIOLATION' if r else 'ok', flush=True)
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(show(n, col))
