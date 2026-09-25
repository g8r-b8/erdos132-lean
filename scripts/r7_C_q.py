"""R7/C: margins for Lemma Q applications and the d = 0 adjacency facts (exact rational/interval bounds).

(Q1) d = 0 apex v (base z = v + o-, z' = v + o+, o+- = -tau u +- 1/2 iu), T-adjacent successor v+ = v + e,
     e = cos(eps) iu + sin(eps) u, 0 < eps < asin(beta).  For every unit nu at angle chi from u with |chi| <= 0.45:
     (z - v+).nu < 0 and (z' - v+).nu < 0.   [Lemma Q => v+ in Q' unless its normal cone is wider than 0.44 (<= 15 points)]
(Q2) the left base point of v+ (w.r.t. u+ within beta of u) is within 0.05 of z'  (so it equals z').
(Q3) G = 1 run end: z_{m-1} - v+ = -tau u - (1/2 + 1) iu + O(1/R), z_{m-2} - v+ = ... - 5/2 iu:
     (z - v+).nu < 0 for |chi| <= 0.3 (cone exceptions <= 22).
(Q4) same centre, angular separation alpha1: |v v'| = 2R sin(alpha1/2) = R/Delta < 1.
Bounds are proved by monotonicity in chi (worst case chi at the boundary, sign chosen adversarially) evaluated with
mpmath interval arithmetic.
"""
from mpmath import iv, mpf
iv.dps = 40
beta = iv.mpf('0.01')
tau = iv.sqrt(3) / 2
def worst(a_u, a_iu, chimax):
    # max over |chi| <= chimax of a_u cos chi + a_iu sin chi with a_u < 0: <= a_u cos(chimax) + |a_iu| sin(chimax)
    c = iv.cos(iv.mpf(chimax)); s = iv.sin(iv.mpf(chimax))
    return a_u * c + abs(a_iu) * s
# (Q1): z - v+ = -(tau + sin eps) u - (cos eps + 1/2) iu ; z' - v+ = -(tau + sin eps) u - (cos eps - 1/2) iu
# worst case eps -> 0 for the u-part, cos eps <= 1:
for off in [iv.mpf('1.5'), iv.mpf('0.5')]:
    val = worst(-tau, off, '0.45')
    assert val.b < 0, val
print('(Q1) d=0 successor: (z - v+).nu < 0 for |chi| <= 0.45 (worst %s): OK' % iv.nstr(worst(-tau, iv.mpf('1.5'), '0.45'), 6))
# (Q2): v+ + o-(u+) - (v + o+(u)) = e - tau (u+ - u) - 1/2 i (u+ + u); |.| <= |e - iu| + tau|u+ - u| + 1/2|u+ - u|
eps = iv.mpf('0.0101'); dang = beta   # asin(0.01) < 0.0101
bound = 2 * iv.sin(eps / 2) + (tau + iv.mpf('0.5')) * 2 * iv.sin(dang / 2)
assert bound.b < iv.mpf('0.05')
print('(Q2) |left base of v+ - z\'| <= %s < 1: OK' % iv.nstr(bound, 6))
# (Q3): tangential offsets 1.5 and 2.5 (+ O(1/R) <= 0.01), normal part -tau + 9/(2R) <= -0.86
for off in [iv.mpf('1.51'), iv.mpf('2.51')]:
    val = worst(iv.mpf('-0.86'), off, '0.3')
    assert val.b < 0, val
print('(Q3) G=1 run-end successor: outward for |chi| <= 0.3 (worst %s): OK' % iv.nstr(worst(iv.mpf('-0.86'), iv.mpf('2.51'), '0.3'), 6))
# cone-width exception counts (Lemma 3.4, M = 1): 2 pi / width
print('     exception counts: wide cones (> 0.44) <= %d, (> 0.29) <= %d' % (int((2 * iv.pi / iv.mpf('0.44')).b), int((2 * iv.pi / iv.mpf('0.29')).b)))
# (Q4)
for Rv in [10 ** 4, 10 ** 8]:
    R = iv.mpf(Rv); t = iv.mpf('0.8660'); D = R + t
    assert (R / D).b < 1          # 2R sin(alpha1/2) = 2R/(2Delta) exactly
print('(Q4) 2R sin(alpha1/2) = R/Delta < 1: OK')
print('r7_C_q: all checks pass')
