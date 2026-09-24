"""Test Pi: in a Q-colouring of n points with D = floor(n/2) colours, the colour-1 class is exactly the set of
the n sides.  Two searches: (a) some diagonal (0,k), k>=2, has colour 1; (b) side (0,1) has colour > 1.
Args: n [D]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show
from pysat.solvers import Solver
n = int(sys.argv[1]); D = int(sys.argv[2]) if len(sys.argv) > 2 else n // 2
for label, extra in [('diag (0,%d) colour 1' % k, [[-M_] for M_ in []]) for k in []] or []:
    pass
tests = [('side (0,1) > 1', lambda M: [[M.geq((0, 1), 2)]])]
for k in range(2, n // 2 + 1):
    tests.append((f'diag (0,{k}) = 1', (lambda k: lambda M: [[-M.geq((0, k), 2)]])(k)))
for label, f in tests:
    M = Model(n, D)
    M.cl += f(M)
    with Solver(name='cadical153', bootstrap_with=M.cl) as S:
        r = S.solve(); print(n, D, label, 'EXISTS' if r else 'impossible', flush=True)
        if r:
            col = M.decode(S.get_model()); assert not check_Q(n, col); print(show(n, col))
