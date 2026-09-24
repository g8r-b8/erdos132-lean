"""Test Lemma STAR: on n = 2s points, the alternate sides (0,1),(2,3),...,(2s-2,2s-1) cannot all have colour
>= D-s+2 in a Q-colouring with (at most) D colours.  Violation search with given D."""
import sys, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show
from pysat.solvers import Solver
s = int(sys.argv[1]); n = 2 * s
Ds = [int(x) for x in sys.argv[2:]] or [n * (n - 1) // 2]
for D in Ds:
    M = Model(n, D, all_used=False)
    for i in range(s):
        M.clause([M.geq((2 * i, 2 * i + 1), D - s + 2)])
    t = time.time()
    with Solver(name='cadical153', bootstrap_with=M.cl) as S:
        r = S.solve()
        print(s, D, 'VIOLATION' if r else 'ok', f"{time.time()-t:.1f}s", len(M.cl), flush=True)
        if r:
            col = M.decode(S.get_model()); assert not check_Q(n, col); print(show(n, col))
