"""Exact LP for Regions II/III (Fractions).

Adversary maximises  min{ 1.5 s - kappa q ,  s + theta q + c r }
subject to s + r = 1, 0 <= q <= rho s   (rho = cap on q/s; rho = 2/3 is always valid:
q <= |K-row|, and |D-row| >= #rungs/2 >= q/2 since a D-point carries <= 2 rungs).

Claim checked: optimum = max{ 3c/(2c+1), 1 + lam0/2 }  with lam0 = theta/(theta+kappa),
as long as the cap rho does not bind (it does not for the cases below), where the
first term is the q = 0 value and the second the r = 0 value.
"""
from fractions import Fraction as F
from itertools import combinations


def lp_value(kappa, theta, c, rho=F(2, 3)):
    # variables (s, q), r = 1 - s. Region: 0<=s<=1, 0<=q<=rho*s.
    # objective min(A, B), A = 1.5 s - kappa q, B = s + theta q + c(1-s).
    # piecewise linear concave -> optimum at a vertex of the arrangement of
    # boundary lines and the line A = B.
    lines = [  # a*s + b*q = d
        (F(1), F(0), F(0)), (F(1), F(0), F(1)), (F(0), F(1), F(0)),
        (-rho, F(1), F(0)),
        # A - B = 0 : (1.5 - 1 + c) s + (-kappa - theta) q - c = 0
        (F(1, 2) + c, -kappa - theta, c),
    ]
    best = None
    for (a1, b1, d1), (a2, b2, d2) in combinations(lines, 2):
        det = a1 * b2 - a2 * b1
        if det == 0:
            continue
        s = (d1 * b2 - d2 * b1) / det
        q = (a1 * d2 - a2 * d1) / det
        if not (0 <= s <= 1 and 0 <= q <= rho * s):
            continue
        A = F(3, 2) * s - kappa * q
        B = s + theta * q + c * (1 - s)
        v = min(A, B)
        if best is None or v > best[0]:
            best = (v, s, q)
    return best


def formula(kappa, theta, c):
    lam0 = theta / (theta + kappa)
    return max(F(3) * c / (2 * c + 1), 1 + lam0 / 2)


if __name__ == "__main__":
    half = F(1, 2)
    cases = []
    for c in [F(4), F(7, 2), F(3), F(5)]:
        for theta in [F(1), F(3, 4), F(1, 2), F(1, 4), F(0)]:
            for kappa in [half, F(3, 4), F(1)]:
                cases.append((kappa, theta, c))
    print("kappa theta c | LP value (s*,q*) | formula")
    for kappa, theta, c in cases:
        v, s, q = lp_value(kappa, theta, c)
        f = formula(kappa, theta, c)
        assert v == f, (kappa, theta, c, v, f)
        print(f"{kappa} {theta} {c} | {v} ({s},{q}) | {f}")
    # key facts
    assert lp_value(half, F(1), F(4))[0] == F(4, 3)
    # any c: with theta=1,kappa=1/2 the r=0 corner already gives 4/3
    assert lp_value(half, F(1), F(3))[0] == F(4, 3)
    # theta = 1/2 makes the q-term irrelevant whenever c >= 5/2
    for c in [F(5, 2), F(3), F(7, 2), F(4)]:
        assert lp_value(half, half, c)[0] == F(3) * c / (2 * c + 1)
    # below 4/3 iff theta < 2 kappa and c < 4
    assert lp_value(half, F(99, 100), F(399, 100))[0] < F(4, 3)
    assert lp_value(F(1, 2), F(1), F(399, 100))[0] == F(4, 3)
    assert lp_value(F(1, 2), F(1, 2), F(4))[0] == F(4, 3)
    print("all LP assertions pass")
