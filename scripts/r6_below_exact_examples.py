#!/usr/bin/env python3
"""r6_below_exact_examples.py -- exact (Q(sqrt3), Fractions) flat-model examples for report section O.

Numbers are pairs (a, b) = a + b*sqrt(3), a, b in Q.  Unit distance and >= 1 are decided exactly.
Examples:
  (E1) A-row stack, t arbitrary (take t = 0 < ... D-row absent): K-row z=0 at x in Z+1/2, R rows j=1..k
       at depth j*sqrt3/2.  Row 1 = type A (v=8).
  (E2) cap lattice, t = 1/2 exactly: K at (sqrt3/2 + sqrt3*i, 0), D at (sqrt3*i, 1/2), R columns.
       Row y (depth 1/2) = caps (v=9), a (depth 1), b (1.5), ...
For each truncation depth: v-values of R points of one period (interior of a long strip, periodic
boundary), average, and final charges under the Region-I discharging rules (report P4).
"""
from fractions import Fraction as F


class Q3:
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(s, o): return Q3(s.a + o.a, s.b + o.b)
    def __sub__(s, o): return Q3(s.a - o.a, s.b - o.b)
    def __mul__(s, o): return Q3(s.a * o.a + 3 * s.b * o.b, s.a * o.b + s.b * o.a)

    def sign(s):
        a, b = s.a, s.b
        if b == 0: return (a > 0) - (a < 0)
        if a == 0: return (b > 0) - (b < 0)
        if a > 0 and b > 0: return 1
        if a < 0 and b < 0: return -1
        # opposite signs: compare a^2 vs 3 b^2
        d = a * a - 3 * b * b
        if a > 0: return (d > 0) - (d < 0)
        return -((d > 0) - (d < 0))

    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def __repr__(s): return f"({s.a}+{s.b}r3)"


ONE = Q3(1)


def d2(p, q):
    dx, dz = p[0] - q[0], p[1] - q[1]
    return dx * dx + dz * dz


def analyse(pts, period, label):
    """pts: list of (x, z, typ) for 3 periods; analyse middle period R points."""
    # check min distance >= 1 exactly
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            assert (d2(pts[i], pts[j]) - ONE).sign() >= 0, (pts[i], pts[j])
    res = []
    for p in pts:
        if p[2] != 'R' or not p[3]:
            continue
        nb = [q for q in pts if q is not p and (d2(p, q) - ONE).sign() == 0]
        deg = len(nb)
        m = sum(1 for q in nb if q[2] != 'R')
        res.append((p, deg, m, deg + m))
    avg = F(sum(r[3] for r in res), len(res))
    print(f"{label}: v per period = {[r[3] for r in res]}, average = {avg} = {float(avg):.4f}")
    return res


def A_stack(k):
    pts = []
    half = Q3(F(1, 2)); s32 = Q3(0, F(1, 2))
    for c in range(-6, 7):
        mid = (0 <= c < 1)
        pts.append((Q3(F(1, 2) + c), Q3(0), 'K', mid))
        for j in range(1, k + 1):
            x = Q3(c + (F(1, 2) if j % 2 == 0 else 0))
            pts.append((x, Q3(0, F(-j, 2)), 'R', mid))
    return pts


def cap_lattice(k):
    """columns: even columns x = sqrt3*i: D at z=1/2, R at -1/2, -3/2, ...; odd x = sqrt3*i + sqrt3/2: K at 0, R at -1, -2..
    k = number of R layers counted in depth order (-1/2, -1, -3/2, ...)."""
    pts = []
    for i in range(-4, 5):
        mid = (i == 0)
        xe = Q3(0, i); xo = Q3(0, F(2 * i + 1, 2))
        pts.append((xe, Q3(F(1, 2)), 'D', mid))
        pts.append((xo, Q3(0), 'K', mid))
        for L in range(1, k + 1):          # layer L at depth L/2
            if L % 2 == 1:
                pts.append((xe, Q3(F(-L, 2)), 'R', mid))
            else:
                pts.append((xo, Q3(F(-L, 2)), 'R', mid))
    return pts


if __name__ == '__main__':
    print("(E1) A-row stacks (any t; K-row unit spaced):")
    for k in (1, 2, 3, 4, 6):
        analyse(A_stack(k), 1, f"  k={k} rows")
    print("   rule: A (row 1, v=8) sends 1/2 to each +-150 nbr (row 2).  Final: row1 7, row2 6+1=7 (k>=3) -> the")
    print("   radius-1 rule is tight at 7 although the true average is 6 + O(1/k)... <= 6.")
    print("(E2) cap lattice, t = 1/2 exactly (D-row at height 1/2, K-row spacing sqrt3):")
    for k in (1, 2, 3, 4, 5, 6):
        analyse(cap_lattice(k), 1, f"  {k} R-layers")
    print("   rule Th: cap sends 1 to its 180-nbr (b), 1/2 to each +-120 nbr (a); a (v=7 when k>=4) forwards")
    print("   its 1 to its 180-nbr.  Final (k>=4): cap 7, a 7, b 6+1 = 7, c 6+1 = 7 or less.")
