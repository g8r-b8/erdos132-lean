"""Local case table for p=0, w2=(1,0), w1=e(-al), w3=e(be), r=w2+e(phi) (r strictly on w3 side),
D:=|r w1| (forced).  Cases: |pr| in {<=1, =D}, |w1w3| in {<=1, =D}; |rw3|<=1 is forced (proved).
Float sampling (+ bisection on the equality constraint); records realisability and local facts."""
import math, random
from collections import defaultdict
def pts(al, be, ph):
    return dict(p=(0, 0), w1=(math.cos(al), -math.sin(al)), w2=(1, 0), w3=(math.cos(be), math.sin(be)),
                r=(1+math.cos(ph), math.sin(ph)))
def cross(o, a, b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def inside_hull(P, x):
    """is point x strictly inside conv(P\\{x})? (brute force over triangles)"""
    others = [q for q in P if q != x]
    import itertools
    for a, b, c in itertools.combinations(others, 3):
        s1, s2, s3 = cross(a, b, x), cross(b, c, x), cross(c, a, x)
        if (s1 > 1e-12 and s2 > 1e-12 and s3 > 1e-12) or (s1 < -1e-12 and s2 < -1e-12 and s3 < -1e-12): return True
    return False
def classify(al, be, ph, tol=1e-9):
    P = pts(al, be, ph); D = math.dist(P['r'], P['w1'])
    if D <= 1 + 1e-9: return None
    kind = {}
    for a, b in [('p', 'r'), ('w1', 'w3'), ('r', 'w3'), ('w1', 'w2'), ('w2', 'w3')]:
        d = math.dist(P[a], P[b])
        if d <= 1 + tol: kind[a+b] = '<=1'
        elif abs(d - D) < 1e-7: kind[a+b] = 'D'
        else: return None
    # p must be extreme
    if inside_hull(list(P.values()), P['p']): return None
    key = (kind['pr'], kind['w1w3'], kind['rw3'])
    facts = ('w2 ext' if not inside_hull(list(P.values()), P['w2']) else 'w2 int',
             'w3 ext' if not inside_hull(list(P.values()), P['w3']) else 'w3 int')
    return key, facts, D
rng = random.Random(1); res = defaultdict(lambda: defaultdict(int)); Dr = defaultdict(lambda: [9, 0])
def rec(c):
    if c: res[c[0]][c[1]] += 1; Dr[c[0]][0] = min(Dr[c[0]][0], c[2]); Dr[c[0]][1] = max(Dr[c[0]][1], c[2])
for _ in range(200000):
    al, be = rng.uniform(0, math.pi/3), rng.uniform(0, math.pi/3); ph = rng.uniform(0, math.pi)
    rec(classify(al, be, ph))
    # equality |pr| = D : solve in ph by bisection of f = |r| - |r-w1|
    f = lambda ph: math.hypot(1+math.cos(ph), math.sin(ph)) - math.dist((1+math.cos(ph), math.sin(ph)), (math.cos(al), -math.sin(al)))
    xs = [i*math.pi/60 for i in range(1, 60)]
    for x0, x1 in zip(xs, xs[1:]):
        if f(x0)*f(x1) < 0:
            for _ in range(60):
                xm = (x0+x1)/2
                if f(x0)*f(xm) <= 0: x1 = xm
                else: x0 = xm
            rec(classify(al, be, (x0+x1)/2))
    # equality |w1w3| = D : choose be so that 2 sin((al+be)/2) = D(al,ph)
    D = math.dist((1+math.cos(ph), math.sin(ph)), (math.cos(al), -math.sin(al)))
    if 1 < D < 2:
        be2 = 2*math.asin(D/2) - al
        if 0 < be2 <= math.pi/3: rec(classify(al, be2, ph))
for k in sorted(res): print(k, dict(res[k]), 'D range %.4f..%.4f' % tuple(Dr[k]))
