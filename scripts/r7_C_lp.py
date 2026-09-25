"""R7/C: LP values (exact Fractions).  Adversary maximises min{1.5 s - kappa q, s + theta q + c r} over
s + r = 1, 0 <= q <= (2/3) s, s, r >= 0 (B2 section 0).  Maximum of a min of two linear forms over a polygon is attained
at a vertex of the polygon or on the intersection of the equality line with an edge; enumerate exactly."""
from fractions import Fraction as F
from itertools import combinations
def lpval(theta, kappa, c):
    # variables (s, q); r = 1 - s.  constraints: 0 <= s <= 1, 0 <= q, q <= 2s/3
    cons = [((1, 0), 0, '>='), ((1, 0), 1, '<='), ((0, 1), 0, '>='), ((F(2, 3), -1), 0, '>=')]
    f1 = lambda s, q: F(3, 2) * s - kappa * q
    f2 = lambda s, q: s + theta * q + c * (1 - s)
    lines = [(a, b) for (a, b, _) in cons] + [((F(3, 2) - 1 + c, -kappa - theta), c)]  # f1 - f2 = 0: (1/2 + c) s - (k+th) q = c
    def feas(s, q):
        return s >= 0 and s <= 1 and q >= 0 and q <= F(2, 3) * s
    best = None
    for (a1, b1), (a2, b2) in combinations(lines, 2):
        det = F(a1[0]) * a2[1] - F(a1[1]) * a2[0]
        if det == 0: continue
        s = (F(b1) * a2[1] - F(a1[1]) * b2) / det
        q = (F(a1[0]) * b2 - F(b1) * a2[0]) / det
        if feas(s, q):
            v = min(f1(s, q), f2(s, q))
            best = v if best is None or v > best else best
    return best
def formula(theta, kappa, c):
    return max(F(3) * c / (2 * c + 1), 1 + theta / (2 * (theta + kappa)))
half = F(1, 2)
rows = []
for theta, lab in [(F(1), 'theta=1 (R4, old window)'), (F(4, 5), 'theta=4/5 (AI only)'), (F(2, 3), 'theta=2/3 (this branch)'), (half, 'theta=1/2 (Region II / |Rd|>4)')]:
    for c in [F(4), F(4) - F(1, 100), F(7, 2), F(3)]:
        v = lpval(theta, half, c); assert v == formula(theta, half, c), (theta, c, v)
        rows.append((lab, c, v))
        print('%-32s c=%-8s value=%-10s = %.6f' % (lab, c, v, float(v)))
assert lpval(F(2, 3), half, F(7, 2)) == F(21, 16)
assert lpval(F(2, 3), half, F(3)) == F(9, 7)
assert lpval(F(2, 3), half, F(4)) == F(4, 3)
assert lpval(F(4, 5), half, F(7, 2)) == F(21, 16)
assert lpval(F(1), half, F(3)) == F(4, 3)
# generic c = 4 - eta: value 3c/(2c+1) = (12 - 3 eta)/(9 - 2 eta) < 4/3 for 0 < eta <= 1
for k in range(1, 101):
    eta = F(k, 100); c = 4 - eta
    assert lpval(F(2, 3), half, c) == F(3) * c / (2 * c + 1) < F(4, 3)
print('theta = 2/3: value = max{3c/(2c+1), 9/7}; c = 4-eta -> (12-3eta)/(9-2eta) < 4/3 (checked eta = k/100); c = 7/2 -> 21/16')
print('r7_C_lp: all checks pass')
