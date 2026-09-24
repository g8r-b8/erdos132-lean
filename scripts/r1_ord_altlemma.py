"""Is Altman's Lemma 1 (consecutive form) an ordinal consequence of Q + 'the chord (0,n-1) has top colour D'?
Points 0..n-1 (the closed side of a diameter, as a convex polygon; extra points E on the other side optional).
Lemma1(i,l): c(i,l) > min(c(i+1,l), c(i,l-1)) for 0<=i<l<=n-1, l-i>=2, (i,l) != (0,n-1).
Also tests the weak form c(i,l) >= min(...).  Args: n D [extra]"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r1_ord_common import Model, check_Q, show, e
from pysat.solvers import Solver
n, D = int(sys.argv[1]), int(sys.argv[2]); extra = int(sys.argv[3]) if len(sys.argv) > 3 else 0
N = n + extra
for strict in (True, False):
    for (i, l) in [(i, l) for i in range(n) for l in range(i + 2, n) if (i, l) != (0, n - 1)]:
        M = Model(N, D, all_used=False)
        M.clause([M.geq((0, n - 1), D)])
        # violation: c(i,l) <= min(...) (strict lemma)  or  c(i,l) < min(...) (weak)
        for other in ((i + 1, l), (i, l - 1)):
            # strict violation: c(i,l) <= c(other) ; weak violation: c(i,l) < c(other)
            for t in range(1, D + 1):
                if strict:   # not(c(i,l) >= t+1) -> c(other) >= t ... encode c(il) <= c(o): for all t: c(il)>=t -> c(o)>=t
                    M.clause([-M.geq((i, l), t) if M.geq((i, l), t) not in (True, False) else (not M.geq((i, l), t)), M.geq(other, t)])
                else:        # c(il) < c(o): for all t: c(il) >= t -> c(o) >= t+1
                    M.clause([-M.geq((i, l), t) if M.geq((i, l), t) not in (True, False) else (not M.geq((i, l), t)), M.geq(other, t + 1)])
        with Solver(name='cadical153', bootstrap_with=M.cl) as S:
            r = S.solve(); mdl = S.get_model()
        if r:
            print('strict' if strict else 'weak', 'VIOLATION at', (i, l))
            col = M.decode(mdl); assert not check_Q(N, col); print(show(N, col)); break
    else:
        print('strict' if strict else 'weak', 'lemma holds for all (i,l)')
