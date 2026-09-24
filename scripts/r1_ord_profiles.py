"""Enumerate all realisable colour-class profiles (s_1..s_D), s_c = #pairs of colour c, of Q-colourings of a
convex n-gon with exactly D colours.  Uses one incremental solver with assumptions on exact-count selectors.
Args: n D   -> prints profiles (colour 1 = smallest)."""
import sys, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType, ITotalizer

n, D = map(int, sys.argv[1:3]); N = n * (n - 1) // 2
M = Model(n, D)
tots = []
for c in range(1, D + 1):
    tot = ITotalizer(lits=[M.X(p, c) for p in M.pairs], ubound=N, top_id=M.pool.top)
    M.pool.occupy(M.pool.top + 1, tot.top_id); M.pool.top = tot.top_id
    M.cl += tot.cnf.clauses; tots.append(tot)
# tot.rhs[k] true iff count >= k+1
def exact(c, s):
    r = tots[c].rhs; a = []
    if s >= 1: a.append(r[s - 1])
    if s < N: a.append(-r[s])
    return a
S = Solver(name='cadical153', bootstrap_with=M.cl)
found = []
def rec(c, remaining, pref):
    # prune: check feasibility of prefix via lower/upper bounds
    if c == D - 1:
        s = remaining
        if s >= 1:
            ass = sum((exact(k, v) for k, v in enumerate(pref + [s])), [])
            if S.solve(assumptions=ass):
                found.append(pref + [s]); print(pref + [s], flush=True)
        return
    for s in range(1, remaining - (D - 1 - c) + 1):
        ass = sum((exact(k, v) for k, v in enumerate(pref + [s])), [])
        if S.solve(assumptions=ass):
            rec(c + 1, remaining - s, pref + [s])
rec(0, N, [])
print('total profiles', len(found))
