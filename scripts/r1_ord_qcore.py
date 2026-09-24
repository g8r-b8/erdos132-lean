"""Deletion-minimal set of quadrilaterals whose Q-constraints refute a statement about Q-colourings of the
n-gon with exactly D colours plus extra unit constraints.  Args: n D mode
modes: side  -> c(0,1) >= 2 ;  diag<k> -> c(0,k) = 1 ; all -> nothing extra (D < n/2 bound)"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, e
from pysat.solvers import Solver
n, D, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
M = Model(n, D, quads=[])
sel = {}
for q in itertools.combinations(range(n), 4):
    s = M.pool.id(('sel', q)); sel[s] = q
    before = len(M.cl); M.add_Q(*q)
    for i in range(before, len(M.cl)):
        M.cl[i] = M.cl[i] + [-s]
if mode == 'side':
    M.cl.append([M.geq((0, 1), 2)])
elif mode.startswith('diag'):
    k = int(mode[4:]); M.cl.append([-M.geq((0, k), 2)])
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    assert not S.solve(assumptions=list(sel)), 'statement is satisfiable'
    core = list(S.get_core()); i = 0
    while i < len(core):
        trial = core[:i] + core[i + 1:]
        if not S.solve(assumptions=trial):
            c2 = [x for x in S.get_core() if x in trial]; core = c2 if c2 else trial
        else:
            i += 1
print(n, D, mode, 'core', len(core), 'of', len(sel))
print(sorted(sel[s] for s in core))
