"""Kupitz-type conjecture for ordinal anti-Monge p x q matrices (and the bipartite part of Q-colourings):
#cells whose value is among the top t values <= bound(t).  Search for violations.
Args: p q V t bound   (all V values used; top t values = V-t+1..V)"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_matrix import build
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
p, q, V, t, bound = map(int, sys.argv[1:6])
pool, cl, geq = build(p, q, V)
def isv(a, c, v):
    x = pool.id(('eq', a, c, v)); A, B = geq(a, c, v), geq(a, c, v + 1)
    if A is True and B is False: cl.append([x])
    elif A is True: cl.extend([[-x, -B], [B, x]])
    elif B is False: cl.extend([[-x, A], [-A, x]])
    else: cl.extend([[-x, A], [-x, -B], [-A, B, x]])
    return x
cells = [(a, c) for a in range(p) for c in range(q)]
for v in range(1, V + 1):
    cl.append([isv(a, c, v) for a, c in cells])
top = []
for a, c in cells:
    g = geq(a, c, V - t + 1)
    if g is True:
        x = pool.id(('T', a, c)); cl.append([x]); top.append(x)
    elif g is not False:
        top.append(g)
cl.extend(CardEnc.atleast(top, bound + 1, vpool=pool, encoding=EncType.seqcounter).clauses)
with Solver(name='cadical153', bootstrap_with=cl) as S:
    r = S.solve(); print(p, q, V, t, bound, 'VIOLATION' if r else 'ok', flush=True)
    if r:
        m = set(l for l in S.get_model() if l > 0)
        for a in range(p):
            print(' '.join(str(max([1] + [u for u in range(2, V + 1) if pool.id(('y', a, c, u)) in m])) for c in range(q)))
