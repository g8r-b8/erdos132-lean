"""Lemma FAN(t) (Perles-type step for the Kupitz bound PK(t)): on 2t+2 points 0..2t+1, the 2t+1 'double fan'
pairs (0,1..t+1) and (t+1, t+2..2t+1) cannot all have colours among the top t colours (i.e. >= D-t+1 where
D = max colour).  Search for a violation with D colours available (max colour D forced to occur)."""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show
from pysat.solvers import Solver
t = int(sys.argv[1]); n = 2 * t + 2
Ds = [int(x) for x in sys.argv[2:]] or [n * (n - 1) // 2]
fan = [(0, i) for i in range(1, t + 2)] + [(t + 1, j) for j in range(t + 2, n)]
for D in Ds:
    M = Model(n, D, all_used=False)
    M.cl.append([M.X(p, D) for p in M.pairs])     # colour D occurs
    for p in fan:
        M.clause([M.geq(p, D - t + 1)])
    with Solver(name='cadical153', bootstrap_with=M.cl) as S:
        r = S.solve(); print(t, D, 'VIOLATION' if r else 'FAN holds', flush=True)
        if r:
            col = M.decode(S.get_model()); assert not check_Q(n, col); print(show(n, col))
