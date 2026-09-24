"""Q-ORD instance (n, D, F) with the compact aux-literal encoding of r1_ord_common (cross-check of b3_sat):
Q-colouring of the n-gon, exactly D colours all used, >= F classes of size >= n+1.  Optional symmetry breaking:
'sb' forces the top colour D to occur on a pair (0,k) (rotation), k <= n/2 (reflection).  Args: n D F [sb] [solver]"""
import sys, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, profile
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
n, D, F = map(int, sys.argv[1:4]); sb = 'sb' in sys.argv[4:]
sname = next((a for a in sys.argv[4:] if a != 'sb'), 'cadical153')
t0 = time.time()
M = Model(n, D)
fs = []
for c in range(1, D + 1):
    f = M.pool.id(('f', c)); fs.append(f); M.size_geq(c, n + 1, sel=f)
M.cl += CardEnc.atleast(fs, F, vpool=M.pool, encoding=EncType.seqcounter).clauses
if sb:
    M.cl.append([M.X((0, k), D) for k in range(1, n // 2 + 1)])
print(f"n={n} D={D} F={F} sb={sb}: {M.pool.top} vars {len(M.cl)} clauses ({time.time()-t0:.1f}s build)", flush=True)
with Solver(name=sname, bootstrap_with=M.cl) as S:
    r = S.solve()
    print('SAT' if r else 'UNSAT', f"{time.time()-t0:.1f}s", sname, flush=True)
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(profile(col, D))
