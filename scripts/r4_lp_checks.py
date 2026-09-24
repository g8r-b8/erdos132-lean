"""R4: exact (Fraction) certificates for the LP steps used in angle_R4.md.

Inputs (per regime), with s = |S|, p = |P1| (points of Delta2-degree 1), r = |R|, n = s + r:
  A := mu(Delta2) <= 1.5 s - 0.5 p          (Lemma 4.2 argument, [Ve87] on S minus P1)
  B := mu(delta)  <= s + p + c r            (e(S) <= s + p; R-points contribute (deg+m)/2 <= c)
For weights lam on A and 1-lam on B we need: p-coefficient <= 0 and
max(s-coeff, r-coeff) = value.  c = 6 is the trivial bound (E) of WRITEUP_A2.
Also re-checks the old table (Lemma 4.1: 9/(7.5-k)) and the Region III LP of the draft.
"""
from fractions import Fraction as F

def cert(c):
    """Value of max_{s,p,r} min(A,B) with a dual certificate (weights lam, 1-lam)."""
    c = F(c)
    lam = max((c - 1) / (c + F(1, 2)), F(2, 3))   # p-coefficient -lam/2+(1-lam) <= 0 needs lam >= 2/3
    s_co = F(3, 2) * lam + (1 - lam)
    r_co = c * (1 - lam)
    p_co = -lam / 2 + (1 - lam)
    assert p_co <= 0
    return max(s_co, r_co)

def cert_regionI(c):
    """Region I: e(S) <= s (no P1 term), B = s + c r."""
    c = F(c); lam = (c - 1) / (c + F(1, 2))       # 1.5 lam + (1-lam) = c (1-lam)
    v = F(3, 2) * lam + (1 - lam); assert v == c * (1 - lam) == F(3, 2) * c / (c + F(1, 2))
    return v

table = {6: F(18, 13), 5: F(15, 11), F(9, 2): F(27, 20), 4: F(4, 3), F(7, 2): F(4, 3), 3: F(4, 3)}
tableI = {6: F(18, 13), 5: F(15, 11), F(9, 2): F(27, 20), 4: F(4, 3), F(7, 2): F(21, 16), 3: F(9, 7)}
for c, v in table.items():
    got = cert(c); gI = cert_regionI(c)
    assert got == v and gI == tableI[c], (c, got, v, gI)
    print(f"c = {str(c):>4}  (deg+m <= {str(2*F(c)):>3})  ->  with P1 term: {got} = {float(got):.4f};  Region I (e(S)<=s): {gI} = {float(gI):.4f}")

# the values are attained by the LP adversary (so the certificates are optimal)
for c in table:
    c = F(c)
    if c >= 4:
        s = c / (c + F(1, 2)); r = 1 - s; p = F(0)
    else:                                   # s = n, p = n/3: A = B = 4/3
        s, r, p = F(1), F(0), F(1, 3)
    assert min(F(3, 2) * s - p / 2, s + p + c * r) == cert(c)

# old Lemma 4.1 values
for k, v in [(1, F(18, 13)), (F(5, 4), F(36, 25)), (F(4, 3), F(54, 37))]:
    assert F(9) / (F(15, 2) - k) == v
# old Lemma 4.2 (e(S) <= s + 2p): weights 4/5, 1/5 -> 7/5
lam = F(4, 5)
assert F(3, 2)*lam + (1-lam) == F(7, 5) and 6*(1-lam) == F(6, 5) and -lam/2 + 2*(1-lam) == 0
assert F(18, 13) < F(7, 5) < F(36, 25) < F(54, 37)
assert F(9, 7) < F(21, 16) < F(4, 3) < F(27, 20) < F(15, 11) < F(18, 13)
print("all LP certificates OK")
