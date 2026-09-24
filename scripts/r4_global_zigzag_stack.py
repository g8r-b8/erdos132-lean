"""R4-global: the Region-I 'tri/rhombus zigzag stack' (obstruction to one-layer/local accounting).
Row 0 = zigzag u_i=(2ic,0), v_i=((2i+1)c,h), c=cos e, h=sin e (S-row in Region I, u in K-row with
two outward exceptions v, v').  Each u has 2 rungs (a=2e), each v has 1 rung; row j = row 0 + j*W.
Checks min distance >= 1 (exact unit edges) and reports degrees / deficits per vertex type."""
import math, cmath, numpy as np
def build(e, periods=40, layers=4):
    c, h = math.cos(e), math.sin(e)
    R = lambda t: cmath.exp(1j * math.radians(t))
    u0 = 0j; vprev = complex(-c, h)
    q2 = u0 + R(math.degrees(e) - 120 - 2 * math.degrees(e))   # rung of u0 at angle e-120-a, a=2e
    W = q2 - vprev
    pts, lab = [], []
    for j in range(layers):
        for i in range(periods):
            pts.append(complex(2 * i * c, 0) + j * W); lab.append(('u', j, i))
            pts.append(complex((2 * i + 1) * c, h) + j * W); lab.append(('v', j, i))
    return np.array(pts), lab, W
for e_deg in [0.5, 2.0, 5.0]:
    X, lab, W = build(math.radians(e_deg))
    D = np.abs(X[:, None] - X[None, :]); np.fill_diagonal(D, 9)
    print(f"e={e_deg} deg: min dist={D.min():.12f}  |W|={abs(W):.6f}")
    A = np.abs(D - 1) < 1e-9
    for (t, j, i), row in zip(lab, A):
        if i == 20 and j <= 2:
            print(f"   type {t} layer {j}: deg={row.sum()}  def={(6 - row.sum()) / 2}")
