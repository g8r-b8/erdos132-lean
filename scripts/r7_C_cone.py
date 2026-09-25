"""R7/C: Cone lemma and Lemma AI (arc interior), exact checks.

Cone lemma. z_k, z_i, z_l on C(w,Delta) at angles -a, 0, b about w (a, b in (0,pi)).
If |y - z_i| < Delta then max(|y z_k|, |y z_l|) > |y z_i|.
Proof: with p = y - w, |y-z_k|^2 - |y-z_i|^2 = 2 p.(z_i - z_k) (as |z_k-w| = |z_i-w|), and
z_i - w = Delta e_0 = lam (z_i - z_k) + mu (z_i - z_l) with lam, mu > 0 (checked symbolically below).
If both differences were <= 0 then p.(z_i - w) <= 0, so |y-z_i|^2 = |p|^2 - 2 p.(z_i-w) + Delta^2 >= Delta^2.

Lemma AI. In any finite X (no distance in (R,Delta)) and for w in X, let z_1..z_N be X cap C(w,Delta) ordered by angle
(span <= pi/3). Then z_i has no Delta_2-partner for 3 <= i <= N-2.
(1) exact symbolic decomposition; (2) exact rational random test of the cone lemma (rational points on circles);
(3) exact check |w w*| = 2 Delta cos(ang/2) >= sqrt3 Delta for the second intersection w* of C(z_k,D), C(z_l,D);
(4) float consistency check of AI on ienjoymath's ring constructions (every w in X).
"""
import random, sys, math
from fractions import Fraction as F
import sympy as sp

# (1) symbolic
a, b, D = sp.symbols('a b Delta', positive=True)
e0 = sp.Matrix([1, 0])
zi = D * sp.Matrix([1, 0]); zk = D * sp.Matrix([sp.cos(a), -sp.sin(a)]); zl = D * sp.Matrix([sp.cos(b), sp.sin(b)])
lam = sp.cos(b / 2) / (2 * sp.sin(a / 2) * sp.sin((a + b) / 2))
mu = sp.cos(a / 2) / (2 * sp.sin(b / 2) * sp.sin((a + b) / 2))
res = sp.simplify(lam * (zi - zk) + mu * (zi - zl) - zi)
res = [sp.simplify(sp.expand_trig(sp.trigsimp(r.rewrite(sp.exp)))) for r in res]
assert all(sp.simplify(r) == 0 for r in res), res
print('(1) z_i - w = lam (z_i - z_k) + mu (z_i - z_l), lam = cos(b/2)/(2 sin(a/2) sin((a+b)/2)) > 0, mu > 0: OK')

# (2) exact rational test
random.seed(132)
def rpt(m, Dl):
    return (Dl * (1 - m * m) / (1 + m * m), Dl * 2 * m / (1 + m * m))
def d2(p, q): return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2
cnt = hit = 0
for trial in range(20000):
    Dl = F(random.randint(5, 200))
    ms = sorted(F(random.randint(-400, 400), 1000) for _ in range(3))   # angles in (-pi/2, pi/2) roughly
    if len(set(ms)) < 3: continue
    zk_, zi_, zl_ = (rpt(m, Dl) for m in ms)
    y = (F(random.randint(-3000, 3000), 10), F(random.randint(-3000, 3000), 10))
    di = d2(y, zi_)
    if di < Dl * Dl:
        cnt += 1
        assert max(d2(y, zk_), d2(y, zl_)) > di, (ms, y)
        hit += 1
print('(2) exact rational cone-lemma test: %d cases with |y z_i| < Delta, all satisfy max(|yz_k|,|yz_l|) > |yz_i|' % hit)

# (3) second intersection of C(z_k,Delta), C(z_l,Delta) other than w=0 is the reflection of w in line z_k z_l
for trial in range(2000):
    Dl = F(random.randint(5, 200))
    m1, m2 = F(random.randint(-268, 268), 1000), F(random.randint(-268, 268), 1000)  # |angle| < 0.53 rad each
    if m1 == m2: continue
    p, q = rpt(m1, Dl), rpt(m2, Dl)
    # reflection of 0 in line pq
    dx, dy = q[0] - p[0], q[1] - p[1]
    t = -(p[0] * dx + p[1] * dy) / (dx * dx + dy * dy)
    foot = (p[0] + t * dx, p[1] + t * dy)
    ws = (2 * foot[0], 2 * foot[1])
    assert d2(ws, p) == Dl * Dl and d2(ws, q) == Dl * Dl
    chord2 = d2(p, q)
    if chord2 <= Dl * Dl:                       # angular separation <= pi/3
        assert d2(ws, (0, 0)) >= 3 * Dl * Dl    # |w w*| >= sqrt3 Delta > Delta
print('(3) w* = reflection of w in z_k z_l, |w w*|^2 = 4Delta^2 - chord^2 >= 3 Delta^2 when chord <= Delta: OK')

print('r7_C_cone: all exact checks pass (part (4) is r7_C_cone_ring.py, needs numpy: run with python3)')
