"""Sanity: r1_ord_common reproduces B3 results: (n,D,F) with F classes >= n+1."""
import sys, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, profile
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

def run(n, D, F, timeout=None):
    M = Model(n, D)
    fs = []
    for c in range(1, D + 1):
        f = M.pool.id(('f', c)); fs.append(f)
        M.size_geq(c, n + 1, sel=f)
    if F:
        M.cl += CardEnc.atleast(lits=fs, bound=F, vpool=M.pool, encoding=EncType.seqcounter).clauses
    with Solver(name='cadical153', bootstrap_with=M.cl) as S:
        r = S.solve()
        if r:
            col = M.decode(S.get_model())
            assert not check_Q(n, col)
            return profile(col, D)
        return None

if __name__ == '__main__':
    for n, D, F in [(7, 3, 0), (7, 4, 1), (7, 4, 2), (7, 2, 0), (9, 5, 2), (9, 5, 3), (9, 3, 0), (11, 6, 3), (11, 6, 4), (6,3,1), (6,2,0)]:
        t = time.time(); print(n, D, F, run(n, D, F), f"{time.time()-t:.1f}s", flush=True)
