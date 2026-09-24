"""SAT version of the Moric-Pritchard level argument (arXiv 1103.0412, Sec. 4) for
T = {2} (second-largest distance), with optional extra constraints valid for sets
with NO FOUR CONCYCLIC points.

Grid: top points t_i, i in [-R, R]; bottom points b_j, j in [1-R, 1+R]. Clockwise order
t_{-R} .. t_R .. b_{1+R} .. b_{1-R}.  Diagonal t_i b_j lies in level j - i.
Variables A[i,j] (|t_i b_j| = Delta = d1), B[i,j] (= Delta2 = d2); both false = shorter.

Query: is there a configuration with t_0 b_1 the leftmost level-1 diagonal of length
>= d2, and for every m' = 1..L, #d2 in levels 1..m' > alpha*m' ?
UNSAT  ==> analogue of MP Lemma 4.2 ==> mu(d2) <= alpha*n + C (via MP Lemma 1.5).

usage: python r2_convex_levels.py L alpha_num alpha_den [flags]
flags: base  = only MP-type facts (Fact 3.1 consequences + Fact 3.3)
       cc    = add no-4-concyclic consequences (deg<=3, Lemma T, same-side uniqueness)
"""
import sys
from fractions import Fraction
from itertools import combinations
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def build(L, alpha, cc, extra_R=1, want_model=False, forbid=None, f32=True, norm=True, counts=True, useT=True, useSame=True, useDeg=True):
    k = 2
    R = 2 * k + L + extra_R
    T = list(range(-R, R + 1))
    Bt = list(range(1 - R, 1 + R + 1))
    pool = IDPool()
    A = {(i, j): pool.id(('A', i, j)) for i in T for j in Bt}
    B = {(i, j): pool.id(('B', i, j)) for i in T for j in Bt}
    cl = []
    top_ = [pool.top]
    for key in A:
        cl.append([-A[key], -B[key]])
    def ge2(i, j):  # length >= d2
        return [A[i, j], B[i, j]]
    for i, i2 in combinations(T, 2):
        for j, j2 in combinations(Bt, 2):
            # non-crossing pair (i,j),(i2,j2); crossing pair (i,j2),(i2,j)
            a, b = (i, j), (i2, j2)
            c, d = (i, j2), (i2, j)
            cl.append([-A[a], -A[b]])
            cl.append([-B[a], -B[b], A[c], A[d]])
            for x, y in ((a, b), (b, a)):
                cl.append([-A[x], -B[y], A[c]])
                cl.append([-A[x], -B[y], A[d]])
            # Fact 3.3 with i=j=2: two non-crossing >=d2 diagonals -> min gap <= 1
            # (gap = number of vertices strictly between)
            if min(i2 - i - 1, j2 - j - 1) > 1:
                for u in (A[a], B[a]):
                    for v in (A[b], B[b]):
                        cl.append([-u, -v])
            # Fact 3.3 (2,1): d2 and d1 non-crossing -> gap <= 0 on one side
            if min(i2 - i - 1, j2 - j - 1) > 0:
                cl.append([-A[a], -B[b]]); cl.append([-B[a], -A[b]])
            if f32:
                # Fact 3.2 on a=t_i, b=t_i2, c=b_j2, d=b_j (clockwise)
                cases = []
                def gt(u, v):
                    # returns clauses-list meaning 'd(u) > d(v)' soundly: not A[v], B[v] -> A[u]
                    return [[-A[v]], [-B[v], A[u]]]
                c1 = [gt((i, x), (i, j)) for x in range(j + 1, j2 + 1)]
                c2 = [gt((i2, x), (i2, j2)) for x in range(j, j2)]
                c3 = [gt((x, j2), (i2, j2)) for x in range(i, i2)]
                c4 = [gt((x, j), (i, j)) for x in range(i + 1, i2 + 1)]
                cvars = []
                for cs in (c1, c2, c3, c4):
                    top_[0] += 1; v = top_[0]; cvars.append(v)
                    for g in cs:
                        for cc_ in g:
                            cl.append([-v] + cc_)
                cl.append(cvars)
            if cc:
                # Lemma T: non-crossing pair both d2, crossing pair both d1 -> concyclic
                if useT: cl.append([-B[a], -B[b], -A[c], -A[d]])
                # same-side uniqueness (two rows, two cols)
                for X in ((A, B) if useSame else ()):
                    for Y in (A, B):
                        # rows i,i2 ; cols j,j2 : d(i,j)=d(i,j2)=x, d(i2,j)=d(i2,j2)=y
                        cl.append([-X[i, j], -X[i, j2], -Y[i2, j], -Y[i2, j2]])
                        # cols j,j2 ; rows i,i2: d(i,j)=d(i2,j)=x, d(i,j2)=d(i2,j2)=y
                        cl.append([-X[i, j], -X[i2, j], -Y[i, j2], -Y[i2, j2]])
    top = top_[0]
    if cc and useDeg:
        for X in (A, B):
            for i in T:
                enc = CardEnc.atmost([X[i, j] for j in Bt], bound=3, top_id=top, encoding=EncType.seqcounter)
                cl += enc.clauses; top = max(top, enc.nv)
            for j in Bt:
                enc = CardEnc.atmost([X[i, j] for i in T], bound=3, top_id=top, encoding=EncType.seqcounter)
                cl += enc.clauses; top = max(top, enc.nv)
    # normalisation
    if not norm:
        return cl, A, B, T, Bt
    cl.append([A[0, 1], B[0, 1]])
    for i in T:
        if i < 0 and (i + 1) in Bt:
            cl.append([-A[i, i + 1]]); cl.append([-B[i, i + 1]])
    # counts
    for m in range(1, L + 1):
        lits = [B[i, j] for i in T for j in Bt if 1 <= j - i <= m]
        need = int(alpha * m) + 1  # floor(alpha m) + 1
        enc = CardEnc.atleast(lits, bound=need, top_id=top, encoding=EncType.seqcounter)
        cl += enc.clauses; top = max(top, enc.nv)
    if forbid:
        cl += forbid
    return cl, A, B, T, Bt

def solve(L, alpha, cc):
    cl, A, B, T, Bt = build(L, alpha, cc)
    s = Cadical153(bootstrap_with=cl)
    r = s.solve()
    model = None
    if r:
        m = set(x for x in s.get_model() if x > 0)
        model = {(i, j): ('1' if A[i, j] in m else '2' if B[i, j] in m else '.') for i in T for j in Bt}
    s.delete()
    return r, model, T, Bt

def show(model, T, Bt):
    print('     ' + ''.join('%3d' % i for i in T))
    for j in Bt:
        print('%4d ' % j + ''.join('%3s' % model[i, j] for i in T))

if __name__ == '__main__':
    L = int(sys.argv[1]); alpha = Fraction(int(sys.argv[2]), int(sys.argv[3]))
    cc = 'cc' in sys.argv[4:]
    r, model, T, Bt = solve(L, alpha, cc)
    print('L=%d alpha=%s cc=%s ->' % (L, alpha, cc), 'SAT' if r else 'UNSAT')
    if r and 'show' in sys.argv:
        show(model, T, Bt)
