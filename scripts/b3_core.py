"""Angle B3: which quadrilaterals does the ordinal refutation need?  Deletion-minimal set of 4-subsets whose
Lemma-Q constraints (order encoding) already make (n, D, F) UNSAT, profile constraints always kept.
Usage: b3_core.py n D F"""
import sys, itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

def run(n, D, F):
    pool = IDPool(); pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    e = lambda i, j: (i, j) if i < j else (j, i)
    X = lambda p, c: pool.id(('x', p, c)); Y = lambda p, t: pool.id(('y', p, t))
    base = []
    for p in pairs:
        base += CardEnc.equals([X(p, c) for c in range(1, D + 1)], 1, vpool=pool, encoding=EncType.pairwise).clauses
        for t in range(2, D + 1):
            base.append([-Y(p, t)] + [X(p, c) for c in range(t, D + 1)])
            base += [[-X(p, c), Y(p, t)] for c in range(t, D + 1)]
    fs = []
    for c in range(1, D + 1):
        lits = [X(p, c) for p in pairs]; base.append(lits)
        f = pool.id(('f', c)); fs.append(f)
        base += [cl + [-f] for cl in CardEnc.atleast(lits, n + 1, vpool=pool, encoding=EncType.seqcounter).clauses]
    if F:
        base += CardEnc.atleast(fs, F, vpool=pool, encoding=EncType.seqcounter).clauses
    le = lambda p, t: [] if t >= D else [Y(p, t + 1)]
    ge = lambda p, t: [] if t <= 1 else [-Y(p, t)]
    quads = list(itertools.combinations(range(n), 4)); sel = {}
    for q in quads:
        i, j, k, l = q; s = pool.id(('s', q)); sel[s] = q
        d1, d2 = e(i, k), e(j, l)
        for s1, s2 in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            for (a, b), (a2, b2) in (((d1, s1), (d2, s2)), ((d1, s2), (d2, s1))):
                for t in range(1, D + 1):
                    for u in range(1, D + 1):
                        base.append([-s] + le(a, t) + ge(b, t) + le(a2, u) + ge(b2, u))
    with Solver(name='cadical153', bootstrap_with=base) as S:
        assert not S.solve(assumptions=list(sel))
        core = list(S.get_core())
        i = 0
        while i < len(core):      # deletion-based minimisation
            trial = core[:i] + core[i + 1:]
            if not S.solve(assumptions=trial):
                core = [x for x in S.get_core() if x in trial] or trial
                core = trial if len(core) > len(trial) else core
            else:
                i += 1
    return sorted(sel[s] for s in core), len(quads)

if __name__ == '__main__':
    n, D, F = map(int, sys.argv[1:4])
    core, tot = run(n, D, F)
    print(f"n={n} D={D} F={F}: minimal core uses {len(core)} of {tot} quadrilaterals")
    print(core)
