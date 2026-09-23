"""VERIFY_B2: exact (sympy) multiplicity profiles of the three convex hexagons with exactly 3 distances
(Fishburn 1995: "Three hexagons have exactly three intervertex distances").

H1 = R_6               (regular hexagon)
H2 = R_7^-             (regular heptagon minus a vertex)
H3 = equilateral hexagon, interior angles alternating 150, 90 (found by scripts/fewdist_search.py 6 3;
     distances 1, sqrt2, (sqrt6+sqrt2)/2).  Its vertices: walk unit steps with exterior turns 90, 30, 90, 30, 90, 30.
For each: strict convexity (exact cross products), distinct distances, multiplicities, k = #{d : mult <= 6}.
"""
import sympy as sp
from itertools import combinations
from collections import Counter


def analyse(name, P):
    n = len(P)
    cr = []
    for i in range(n):
        a, b, c = P[i], P[(i + 1) % n], P[(i + 2) % n]
        cr.append(sp.nsimplify(sp.simplify((b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]))))
    assert all(sp.simplify(x) > 0 for x in cr), (name, cr)
    d2 = [sp.radsimp(sp.expand((P[i][0] - P[j][0]) ** 2 + (P[i][1] - P[j][1]) ** 2)) for i, j in combinations(range(n), 2)]
    classes = []
    for v in d2:
        for cl in classes:
            if abs(sp.N(cl[0] - v, 80)) < sp.Float('1e-60'):  # 80-digit test; sympy cannot always simplify trig forms
                cl[1] += 1
                break
        else:
            classes.append([v, 1])
    classes.sort(key=lambda t: float(sp.N(t[0])))
    mult = [c[1] for c in classes]
    k = sum(1 for m in mult if m <= n)
    print("%-6s strictly convex; D=%d; squared distances=%s; multiplicities=%s; k=%d"
          % (name, len(classes), [sp.nsimplify(sp.N(c[0], 30), [sp.sqrt(3)]) if c[0].has(sp.cos, sp.sin) else c[0] for c in classes], mult, k))
    return len(classes), k


def walk(turns_deg):
    P = [(sp.Integer(0), sp.Integer(0))]
    ang = sp.Integer(0)
    for t in turns_deg[:-1]:
        x, y = P[-1]
        P.append((sp.nsimplify(x + sp.cos(ang)), sp.nsimplify(y + sp.sin(ang))))
        ang += sp.rad(t)
    # closure check
    x, y = P[-1]
    assert sp.simplify(x + sp.cos(ang)) == 0 and sp.simplify(y + sp.sin(ang)) == 0
    return P


def regular(N, keep):
    return [(sp.cos(2 * sp.pi * j / N), sp.sin(2 * sp.pi * j / N)) for j in range(keep)]


if __name__ == "__main__":
    res = [analyse("R_6", regular(6, 6)), analyse("R_7^-", regular(7, 6)),
           analyse("H3", walk([90, 30, 90, 30, 90, 30]))]
    assert all(D == 3 and k == 3 for D, k in res)
    print("all three Fishburn hexagons: D = 3, k = 3")
