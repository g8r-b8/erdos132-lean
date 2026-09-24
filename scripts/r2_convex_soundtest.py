"""Soundness test of the clause families in r2_convex_levels.py: take a certified convex
no-4-concyclic configuration (certified_n*.txt), map a window of it onto the grid
(t_i = a_{x0-i}, b_j = a_{y0+j}), fix all A/B variables to the true labels and check that
every clause (without normalisation / counting) is satisfiable (i.e. no clause violated)."""
import sys, itertools
import mpmath as mp
from pysat.solvers import Cadical153
import r2_convex_levels as LV
mp.mp.dps = 55
fn = sys.argv[1]; L = int(sys.argv[2])
lines = [l.split() for l in open(fn) if not l.startswith('#')]
P = [(mp.mpf(a), mp.mpf(b)) for a, b in lines[:-1]]; D = mp.mpf(lines[-1][1])
n = len(P)
def lab(x, y):
    d = mp.sqrt((P[x][0]-P[y][0])**2 + (P[x][1]-P[y][1])**2)
    if abs(d - 1) < mp.mpf(10)**-35: return 'B'
    if abs(d - D) < mp.mpf(10)**-35: return 'A'
    return '.'
cl, A, B, T, Bt = LV.build(L, 1, True, norm=False, counts=False)
R = max(T)
tot = 0; bad = 0
for x0 in range(0, n, 4):
    for off in range(n):
        y0 = (x0 + off) % n
        # need the two index windows disjoint: t window x0-R..x0+R, b window y0+1-R..y0+1+R
        tw = {(x0 - i) % n for i in T}; bw = {(y0 + j) % n for j in Bt}
        if tw & bw or len(tw) < len(T) or len(bw) < len(Bt):
            continue
        # also require every >=Delta2 pair inside grid is top-bottom only (no special diagonal): skip check
        assum = []
        has = 0
        for i in T:
            for j in Bt:
                l = lab((x0 - i) % n, (y0 + j) % n)
                assum.append(A[i, j] if l == 'A' else -A[i, j])
                assum.append(B[i, j] if l == 'B' else -B[i, j])
                has += l != '.'
        if has == 0: continue
        s = Cadical153(bootstrap_with=cl)
        ok = s.solve(assumptions=assum); s.delete()
        tot += 1; bad += (not ok)
print(fn, 'windows tested', tot, 'violations', bad)
