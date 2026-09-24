"""Test Lemma DJ: for s pairwise disjoint (vertex-disjoint, non-crossing) chords, the minimum colour is
<= D - s + 1  (equivalently: at most s-2 colour values lie strictly above the min colour of the family... no:
at most s-1 values are >= min).  WLOG n = 2s and the family is a non-crossing perfect matching (restriction
to its endpoints + compression preserves Q and the rank condition).  We search for a violation: a Q-colouring
with D colours (not all used) where all chords of S have colour >= D-s+2.  D = C(n,2) is enough."""
import sys, itertools, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, e, show
from pysat.solvers import Solver

def ncmatchings(pts):
    if not pts:
        yield []
        return
    a = pts[0]
    for idx in range(1, len(pts), 2):
        b = pts[idx]
        for m1 in ncmatchings(pts[1:idx]):
            for m2 in ncmatchings(pts[idx + 1:]):
                yield [(a, b)] + m1 + m2

def canon(M, n):
    best = None
    for r in range(n):
        for refl in (1, -1):
            f = lambda x: (refl * x + r) % n
            key = tuple(sorted(e(f(a), f(b)) for a, b in M))
            if best is None or key < best:
                best = key
    return best

if __name__ == '__main__':
    s = int(sys.argv[1]); n = 2 * s
    D = int(sys.argv[2]) if len(sys.argv) > 2 else n * (n - 1) // 2
    seen = set()
    for Mt in ncmatchings(list(range(n))):
        c = canon(Mt, n)
        if c in seen:
            continue
        seen.add(c)
        M = Model(n, D, all_used=False)
        for p in c:
            M.clause([M.geq(p, D - s + 2)])
        t = time.time()
        with Solver(name='cadical153', bootstrap_with=M.cl) as S:
            r = S.solve()
            print(c, 'VIOLATION' if r else 'ok', f"{time.time()-t:.1f}s", flush=True)
            if r:
                col = M.decode(S.get_model()); assert not check_Q(n, col)
                vals = sorted(set(col.values())); rk = {v: i + 1 for i, v in enumerate(vals)}
                col = {p: rk[v] for p, v in col.items()}
                print(show(n, col))
