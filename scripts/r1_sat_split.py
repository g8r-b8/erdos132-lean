"""Angle R1: split the (n, D, F=D-2) ordinal-counterexample instance of B3 by the pair of non-frequent colours.

A (n, D, D-2) ordinal counterexample is a colouring c: E(K_n) -> {1..D} (vertices 0..n-1 in convex cyclic order),
all D colours used, satisfying the ordinal quadrilateral inequality (Lemma Q, order encoding exactly as in
b3_sat.build(order_Q=True)), with at least D-2 colour classes of size >= n+1.

Case split (assumption-free): choose D-2 frequent colours; the remaining two colours {r1, r2} are the case.
  Case (r1, r2):  every colour c not in {r1,r2} has >= n+1 pairs;  r1, r2 each used (>= 1 pair);
                  redundant (implied by the above + total C(n,2)): |r1| + |r2| <= C(n,2) - (D-2)(n+1).
Every counterexample satisfies at least one case, so all C(D,2) cases UNSAT  =>  (n, D, D-2) UNSAT.

Optional cube: additionally fix the colours of a given list of pairs (used for further splitting).
Optional symmetry breaking (flag 'sb=Dmax'): see sb_clauses docstring.

Usage:
  r1_sat_split.py cnf  n D r1 r2 OUT.cnf [sb=<mode>] [cube=i-j:c,i-j:c,...]
"""
import sys, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


def build(n, D, rare, cube=(), sb=None, thr=None):
    thr = n + 1 if thr is None else thr   # frequency threshold; != n+1 only in r1_sb_test
    pool = IDPool()
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    N = len(pairs)
    def e(i, j): return (i, j) if i < j else (j, i)
    X = lambda p, c: pool.id(('x', p, c))
    Y = lambda p, t: pool.id(('y', p, t))
    for p in pairs:                      # allocate x first so x-ids are 1..N*D (readable)
        for c in range(1, D + 1): X(p, c)
    cnf = CNF()
    for p in pairs:
        cnf.extend(CardEnc.equals(lits=[X(p, c) for c in range(1, D + 1)], bound=1, vpool=pool,
                                  encoding=EncType.pairwise).clauses)
    # order literals Y(p,t) <-> colour(p) >= t, t = 2..D
    for p in pairs:
        for t in range(2, D + 1):
            cnf.append([-Y(p, t)] + [X(p, c) for c in range(t, D + 1)])
            for c in range(t, D + 1):
                cnf.append([-X(p, c), Y(p, t)])
    def le(p, t): return [] if t >= D else [Y(p, t + 1)]    # clause part: NOT(colour(p) <= t)
    def ge(p, t): return [] if t <= 1 else [-Y(p, t)]       # clause part: NOT(colour(p) >= t)
    # Lemma Q: for i<j<k<l, diagonals d1=ik, d2=jl; for each pair of opposite sides {s1,s2} and each matching,
    # forbid colour(a) <= colour(b) and colour(a2) <= colour(b2).
    for i, j, k, l in itertools.combinations(range(n), 4):
        d1, d2 = e(i, k), e(j, l)
        for s1, s2 in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            for (a, b), (a2, b2) in (((d1, s1), (d2, s2)), ((d1, s2), (d2, s1))):
                for t in range(1, D + 1):
                    for u in range(1, D + 1):
                        cnf.append(le(a, t) + ge(b, t) + le(a2, u) + ge(b2, u))
    # profile of the case
    r1, r2 = rare
    for c in range(1, D + 1):
        lits = [X(p, c) for p in pairs]
        if c in rare:
            cnf.append(lits)
        else:
            cnf.extend(CardEnc.atleast(lits=lits, bound=thr, vpool=pool, encoding=EncType.seqcounter).clauses)
    slack = N - (D - 2) * thr
    rl = [X(p, r1) for p in pairs] + [X(p, r2) for p in pairs]
    cnf.extend(CardEnc.atmost(lits=rl, bound=slack, vpool=pool, encoding=EncType.seqcounter).clauses)
    for (p, c) in cube:
        cnf.append([X(p, c)])
    if sb:
        sb_clauses(sb, n, D, rare, pairs, X, cnf)
    return cnf, pool, pairs, X


def sb_clauses(mode, n, D, rare, pairs, X, cnf):
    """Symmetry breaking under the dihedral group (the Q clause set and the case profile are dihedral-invariant;
    the cube, if any, is added separately and is a complete split of the SB'd formula).
    mode 'Dmax': let L* = max cyclic length clen(e) = min(j-i, n-(j-i)) over the D-edges (D-class nonempty).
      Rotation: WLOG {0, L*} is a D-edge.  Selector s_L -> x[{0,L},D] and s_L -> no D-edge of clen > L; OR_L s_L.
      Reflection sigma_L: i -> L-i (mod n) fixes {0,L} and preserves clen, so under s_L we may also require
      c({0,L+1}) <= c({L,n-1})  (if violated, replace c by c o sigma_L, which reverses the strict inequality).
    """
    assert mode == 'Dmax'
    def e(i, j): i %= n; j %= n; return (i, j) if i < j else (j, i)
    def clen(p): d = p[1] - p[0]; return min(d, n - d)
    top = max(cnf.nv, max(abs(l) for cl in cnf.clauses for l in cl))
    sel = []
    for L in range(1, n // 2 + 1):
        top += 1; sL = top; sel.append(sL)
        cnf.append([-sL, X(e(0, L), D)])
        for p in pairs:
            if clen(p) > L: cnf.append([-sL, -X(p, D)])
        a, b = e(0, L + 1), e(L, n - 1)
        # forbid colour(a) = ca > colour(b) = cb
        for ca in range(1, D + 1):
            for cb in range(1, ca):
                cnf.append([-sL, -X(a, ca), -X(b, cb)])
    cnf.append(sel)


def parse_cube(s, n):
    out = []
    for tok in s.split(','):
        pq, c = tok.split(':'); i, j = map(int, pq.split('-'))
        out.append(((min(i, j), max(i, j)), int(c)))
    return out


if __name__ == '__main__':
    assert sys.argv[1] == 'cnf'
    n, D, r1, r2 = map(int, sys.argv[2:6]); out = sys.argv[6]
    cube = (); sb = None
    for a in sys.argv[7:]:
        if a.startswith('cube='): cube = parse_cube(a[5:], n)
        if a.startswith('sb='): sb = a[3:]
    cnf, pool, pairs, X = build(n, D, (r1, r2), cube, sb)
    cnf.to_file(out)
    print(f"n={n} D={D} rare={r1},{r2} cube={len(cube)}: {cnf.nv} vars {len(cnf.clauses)} clauses -> {out}")
