"""Angle R1: empirical soundness test of the 'Dmax' symmetry breaking in r1_sat_split.

For small SAT instances, enumerate ALL solutions (projected on the colouring) without SB, group them into
dihedral orbits, and check that (a) the solution set is dihedral-invariant (sanity check of the encoding),
(b) SB solutions are a subset of plain solutions, (c) every orbit contains a colouring satisfying the SB formula.
Usage: r1_sb_test.py n D r1 r2 [thr]   (thr = frequency threshold, default n+1; lower it to get many solutions)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Solver
from r1_sat_split import build


def colourings(n, D, rare, sb, thr=None):
    cnf, pool, pairs, X = build(n, D, rare, (), sb, thr)
    xs = [X(p, c) for p in pairs for c in range(1, D + 1)]
    out = set()
    with Solver(name='cadical153', bootstrap_with=cnf.clauses) as s:
        while s.solve():
            m = set(l for l in s.get_model() if l > 0)
            col = tuple(next(c for c in range(1, D + 1) if X(p, c) in m) for p in pairs)
            out.add(col)
            s.add_clause([-X(p, c) for p, c in zip(pairs, col)])
    return out, pairs


def main():
    n, D, r1, r2 = map(int, sys.argv[1:5]); thr = int(sys.argv[5]) if len(sys.argv) > 5 else None
    plain, pairs = colourings(n, D, (r1, r2), None, thr)
    withsb, _ = colourings(n, D, (r1, r2), 'Dmax', thr)
    idx = {p: k for k, p in enumerate(pairs)}
    def act(col, g):
        new = [0] * len(pairs)
        for p, c in zip(pairs, col):
            a, b = g(p[0]), g(p[1]); new[idx[(min(a, b), max(a, b))]] = c
        return tuple(new)
    group = [(lambda r: (lambda i: (i + r) % n))(r) for r in range(n)] + \
            [(lambda r: (lambda i: (r - i) % n))(r) for r in range(n)]
    assert withsb <= plain
    orbits = set(); miss = 0
    for col in plain:
        orb = frozenset(act(col, g) for g in group)
        if orb in orbits: continue
        orbits.add(orb)
        assert orb <= plain, 'solution set not dihedral-invariant'
        if not (orb & withsb): miss += 1
    print(f"n={n} D={D} rare={r1},{r2}: {len(plain)} solutions, {len(orbits)} orbits, {len(withsb)} with SB, "
          f"orbits missed by SB: {miss}")
    assert miss == 0


if __name__ == '__main__':
    main()
