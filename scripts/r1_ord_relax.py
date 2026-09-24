"""Relaxations of Q-ORD: n, D, and a list of thresholds: require (after sorting classes decreasingly) the
k-th largest class to have size >= thr[k].  Encoded via selectors: for each threshold value h, at least
#(thr >= h) classes of size >= h.  Args: n D thr1 thr2 ...  Prints a model if SAT."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show, profile
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
n, D = map(int, sys.argv[1:3]); thr = sorted(map(int, sys.argv[3:]), reverse=True)
M = Model(n, D)
for h in sorted(set(thr)):
    k = sum(1 for x in thr if x >= h)
    fs = []
    for c in range(1, D + 1):
        f = M.pool.id(('f', h, c)); fs.append(f); M.size_geq(c, h, sel=f)
    M.cl += CardEnc.atleast(fs, k, vpool=M.pool, encoding=EncType.seqcounter).clauses
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    r = S.solve(); print(n, D, thr, 'SAT' if r else 'UNSAT', flush=True)
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(profile(col, D)); print(show(n, col))
