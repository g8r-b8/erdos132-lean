"""Conjecture TP: |G_D| + |G_c| <= 2n for every colour c < D (G_D = top class).  Search for violations.
Args: n D c"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, profile
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
n, D, c = map(int, sys.argv[1:4])
M = Model(n, D)
lits = [M.X(p, D) for p in M.pairs] + [M.X(p, c) for p in M.pairs]
M.cl += CardEnc.atleast(lits, 2 * n + 1, vpool=M.pool, encoding=EncType.seqcounter).clauses
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    r = S.solve(); print(n, D, c, 'VIOLATION' if r else 'ok', flush=True)
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(profile(col, D))
