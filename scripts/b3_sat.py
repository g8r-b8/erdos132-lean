"""Angle B3: independent SAT encoding of the same combinatorial problem as b3_enum.py (cross-check for n=7,
and the main tool for n=11).

Variables x[e,c]: pair e has colour c (1 = smallest distance, D = largest).  Clauses:
  exactly one colour per pair;
  (T) triangle rigidity on each side of each line ij;
  (Q) ordinal quadrilateral inequality (sorted diagonal colours not dominated by sorted opposite-side colours);
  every colour used; at least F colours have >= n+1 pairs (cardinality networks from pysat).
(X) is a special case of (Q) and is not encoded separately.
Symmetry is not broken (UNSAT answers are what matter).

Usage: b3_sat.py n D F [solver] [T|Q|TQ] [order]   -> prints SAT/UNSAT (and a model if SAT)
"""
import sys, itertools, time
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

def build(n, D, F, use_T=True, use_Q=True, order_Q=False):
    pool = IDPool()
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    def e(i, j): return (i, j) if i < j else (j, i)
    X = lambda p, c: pool.id(('x', p, c))
    cnf = CNF()
    for p in pairs:
        lits = [X(p, c) for c in range(1, D + 1)]
        cnf.extend(CardEnc.equals(lits=lits, bound=1, vpool=pool, encoding=EncType.pairwise).clauses)
    # (T)
    for i, j in (pairs if use_T else []):
        arc1 = list(range(i + 1, j)); arc2 = [w for w in range(n) if w not in arc1 and w not in (i, j)]
        for arc in (arc1, arc2):
            for w, w2 in itertools.combinations(arc, 2):
                for a in range(1, D + 1):
                    for b in range(1, D + 1):
                        cnf.append([-X(e(i, w), a), -X(e(j, w), b), -X(e(i, w2), a), -X(e(j, w2), b)])
    # (Q)
    if order_Q:
        # order literals Y(p,t) <-> colour(p) >= t, t = 2..D
        Y = lambda p, t: pool.id(('y', p, t))
        for p in pairs:
            for t in range(2, D + 1):
                cnf.append([-Y(p, t)] + [X(p, c) for c in range(t, D + 1)])
                for c in range(t, D + 1):
                    cnf.append([-X(p, c), Y(p, t)])
        def le(p, t):   # literal list asserting NOT(colour(p) <= t)
            return [] if t >= D else [Y(p, t + 1)]
        def ge(p, t):   # literal list asserting NOT(colour(p) >= t)
            return [] if t <= 1 else [-Y(p, t)]
    for i, j, k, l in (itertools.combinations(range(n), 4) if use_Q else []):
        d1, d2 = e(i, k), e(j, l)
        for s1, s2 in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            if order_Q:
                # forbid colour(a) <= colour(b) and colour(a') <= colour(b') for both matchings {a,a'}={d1,d2}
                for (a, b), (a2, b2) in (((d1, s1), (d2, s2)), ((d1, s2), (d2, s1))):
                    for t in range(1, D + 1):
                        for u in range(1, D + 1):
                            cnf.append(le(a, t) + ge(b, t) + le(a2, u) + ge(b2, u))
                continue
            for p, q, r, s in itertools.product(range(1, D + 1), repeat=4):
                x = sorted((p, q)); y = sorted((r, s))
                if x[0] <= y[0] and x[1] <= y[1]:
                    cnf.append([-X(d1, p), -X(d2, q), -X(s1, r), -X(s2, s)])
    # counts
    fsel = []
    for c in range(1, D + 1):
        lits = [X(p, c) for p in pairs]
        cnf.append(lits)  # colour used
        f = pool.id(('f', c)); fsel.append(f)
        # f -> sum >= n+1
        enc = CardEnc.atleast(lits=lits, bound=n + 1, vpool=pool, encoding=EncType.seqcounter)
        for cl in enc.clauses:
            cnf.append(cl + [-f])
    if F > 0:
        cnf.extend(CardEnc.atleast(lits=fsel, bound=F, vpool=pool, encoding=EncType.seqcounter).clauses)
    return cnf, pool, pairs, X

if __name__ == '__main__':
    n, D, F = map(int, sys.argv[1:4]); sname = sys.argv[4] if len(sys.argv) > 4 else 'cadical153'
    only = sys.argv[5] if len(sys.argv) > 5 else 'TQ'   # ablation: 'T' or 'Q' drops the other family
    order_Q = len(sys.argv) > 6 and sys.argv[6] == 'order'   # compact order encoding of (Q)
    t = time.time()
    cnf, pool, pairs, X = build(n, D, F, use_T='T' in only, use_Q='Q' in only, order_Q=order_Q)
    print(f"n={n} D={D} F={F} [{only}{' order' if order_Q else ''}]: {pool.top} vars, {len(cnf.clauses)} clauses", flush=True)
    with Solver(name=sname, bootstrap_with=cnf.clauses) as s:
        r = s.solve()
        print("SAT" if r else "UNSAT", f"({time.time() - t:.1f}s, solver {sname})")
        if r:
            m = set(l for l in s.get_model() if l > 0)
            col = [next(c for c in range(1, D + 1) if X(p, c) in m) for p in pairs]
            print(''.join(map(str, col)))
            # cross-check the model against the independent constraint code of b3_enum.py
            from b3_enum import setup, ok, profile_generic
            _, _, _, cons = setup(n, use_T='T' in only)
            cnt = [0] * (D + 1)
            for c in col: cnt[c] += 1
            okf, _ = profile_generic(n, D, F)
            good = all(ok(k, col, D) for step in cons for k in step if k[0] != 'T' or 'T' in only) and okf(cnt)
            print("model re-checked by b3_enum constraints:", "OK" if good else "MISMATCH", "profile", cnt[1:])
