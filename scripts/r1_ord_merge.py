"""Test MERGE lemma: n = 2s points, star edges (2i,2i+1) all >= L with some = L.  Claim: there is a star family
of size s-1 (2s-2 of the points, paired consecutively in their cyclic order) with all colours >= L+1.
Search for a counterexample.  Args: s D L"""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show, e
from pysat.solvers import Solver

def star_families(pts, t):
    for sub in itertools.combinations(pts, 2 * t):
        for off in (0, 1):
            yield [e(sub[(2 * i + off) % (2 * t)], sub[(2 * i + 1 + off) % (2 * t)]) for i in range(t)]

s, D, L = map(int, sys.argv[1:4]); n = 2 * s
M = Model(n, D, all_used=False)
star = [(2 * i, 2 * i + 1) for i in range(s)]
for p in star:
    M.clause([M.geq(p, L)])
M.clause([-M.geq(p, L + 1) for p in star])
for fam in star_families(list(range(n)), s - 1):
    M.clause([-M.geq(p, L + 1) for p in fam])
with Solver(name='cadical153', bootstrap_with=M.cl) as S:
    r = S.solve()
    print(s, D, L, 'COUNTEREXAMPLE' if r else 'merge holds')
    if r:
        col = M.decode(S.get_model()); assert not check_Q(n, col); print(show(n, col))
