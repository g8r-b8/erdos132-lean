"""Ordinal Cap Lemma exploration: ring R_q (q odd, points 0..q-1, colour of (i,j) = 2*cyclic distance) plus
one extra point u = q placed between q-1 and 0.  u-edges may take any colour 1..q (odd values = strictly between
ring colours, q = 2*(max dist)+1 is above everything).  Enumerate all valid colour vectors of u
(c(u,0..q-1)).  Args: q"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, e
from pysat.solvers import Solver
q = int(sys.argv[1]); n = q + 1; h = q // 2; D = 2 * h + 1 + (int(sys.argv[2]) if len(sys.argv) > 2 else 0)
M = Model(n, D, all_used=False)
dist = lambda i, j: min(abs(i - j), q - abs(i - j))
for i, j in itertools.combinations(range(q), 2):
    M.cl.append([M.X((i, j), 2 * dist(i, j))])
for x in range(q):
    for c in range(1, D + 1): M.X((x, q), c)
sols = []
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    while S.solve():
        col = M.decode(S.get_model()); assert not check_Q(n, col)
        vec = tuple(col[(x, q)] for x in range(q)); sols.append(vec)
        S.add_clause([-M.X((x, q), vec[x]) for x in range(q)])
print(len(sols), 'vectors (ring colour 2d = distance d; odd = in between)')
for v in sorted(sols):
    print(' '.join(f"{x/2:g}" for x in v))
