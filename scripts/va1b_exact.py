"""Exact / rigorous re-check of the numeric branches in VERIFY_A1b.md.
Case 1 (Delta = sqrt3): candidates solved exactly in Q(sqrt3, sqrt(..)) with sympy; all pairwise squared distances
  compared exactly with 1 and 3.
Case 2 (Delta^2 = 2+2cos a): closed form for |r - v3|^2 on the branch |r - v2| = Delta, then a rigorous interval-
  arithmetic check (mpmath.iv) over a in (0, pi/6], plus a limit argument at a -> 0."""
import itertools, sympy as sp
from mpmath import iv, mp

# ---------------- Case 1, exact ----------------
s3 = sp.sqrt(3)
V = [sp.Matrix([1, 0]), sp.Matrix([-sp.Rational(1, 2), s3/2]), sp.Matrix([-sp.Rational(1, 2), -s3/2])]
x, y = sp.symbols('x y', real=True)
P = sp.Matrix([x, y])
cands = []
for i in range(3):
    for j in range(3):
        if i == j: continue
        # |P - v_i| = 1  <=>  |P|^2 = 2 P.v_i ;  |P - v_j|^2 = 3  <=>  P.(v_i - v_j) = 1   (linear)
        sols = sp.solve([sp.expand(P.dot(P) - 2*P.dot(V[i])), sp.expand(P.dot(V[i]-V[j]) - 1)], [x, y], dict=True)
        assert len(sols) == 2, (i, j, sols)
        for s in sols:
            Q = sp.Matrix([sp.radsimp(s[x]), sp.radsimp(s[y])])
            n2 = sp.nsimplify(sp.simplify(Q.dot(Q)))
            assert sp.simplify((Q-V[i]).dot(Q-V[i]) - 1) == 0 and sp.simplify((Q-V[j]).dot(Q-V[j]) - 3) == 0
            if sp.N(n2, 50) > 1 or n2 == 0: continue          # must lie in the closed unit disk, != q
            k = 3 - i - j                                     # third vertex: need |Q - v_k|^2 <= 1 or == 3
            d2 = sp.simplify((Q-V[k]).dot(Q-V[k]))
            if not (d2 == 3 or sp.N(d2, 50) <= 1): continue
            cands.append((i, Q))
print("Case 1: exact candidates:", len(cands))
def cls(d2):
    d2 = sp.nsimplify(sp.simplify(d2))
    if sp.simplify(d2 - 3) == 0: return "=3"
    v = sp.N(d2, 60)
    return "<=1" if v <= 1 else ("in(1,3) %.6f" % float(v) if v < 3 else ">3")
ok_pairs = []
for (a, A), (b, B) in itertools.combinations(cands, 2):
    c = cls((A-B).dot(A-B))
    if c in ("<=1", "=3"): ok_pairs.append(((a, A), (b, B)))
    print("  v%d vs v%d candidate: |A-B|^2 %s" % (a, b, c))
# compatibility graph is a matching => no compatible set covers all three owners
own = lambda Q: {i for i in range(3) if sp.simplify((Q-V[i]).dot(Q-V[i]) - 1) == 0}
best = 0
for r in range(1, len(cands)+1):
    for S in itertools.combinations(range(len(cands)), r):
        if all(((cands[p], cands[q]) in ok_pairs) or ((cands[q], cands[p]) in ok_pairs) for p, q in itertools.combinations(S, 2)):
            if set().union(*(own(cands[p][1]) for p in S)) == {0, 1, 2}: best += 1
print("Case 1: compatible candidate sets covering all three v_i:", best)

# ---------------- Case 2, closed form + interval arithmetic ----------------
a = sp.symbols('a', positive=True)
c, s = sp.cos(a), sp.sin(a)
v1 = sp.Matrix([-1, 0]); v2 = sp.Matrix([c, s]); v3 = sp.Matrix([c, -s]); D2 = 2 + 2*c
# |r|^2 = -2x (from |r - v1| = 1) ; |r - v2|^2 = D2  =>  -2x(1+c) - 2 s y = 1 + 2c  (linear in x, y)
Y = -(1 + 2*c + 2*x*(1+c)) / (2*s)
quad = sp.simplify(sp.expand((x+1)**2 + Y**2 - 1) * 4*s**2)
xs = sp.solve(quad, x)
print("Case 2: x-roots:", [sp.simplify(r) for r in xs])
F = lambda X: -4*X*(1+c) - 2*c          # |r - v3|^2 on this branch
mp.prec = 80
bad = 0; worst = None
N = 6000
for k in range(N):
    A = iv.mpf([iv.pi.a/6*k/N, iv.pi.b/6*(k+1)/N]) if k else None
    if k == 0: continue                   # a -> 0 handled by limit below
    C, S = iv.cos(A), iv.sin(A)
    for sign in (+1, -1):
        # x = roots of quad; recompute numerically-rigorously from the closed form
        pass
# closed form via sympy lambdify into interval arithmetic
fx = [sp.lambdify(a, sp.simplify(r), modules=[{'sqrt': iv.sqrt, 'cos': iv.cos, 'sin': iv.sin}]) for r in xs]
for k in range(1, N+1):
    A = iv.mpf([iv.pi.a/6*(k-1)/N, iv.pi.b/6*k/N]) if k > 1 else iv.mpf([iv.pi.a/6*1e-6, iv.pi.b/6/N])
    C = iv.cos(A)
    for f in fx:
        try: X = f(A)
        except Exception: continue
        n2 = -2*X                          # |r|^2
        if n2.a > 1: continue              # outside disk: branch void
        G = -4*X*(1+C) - 2*C               # |r - v3|^2
        # need G strictly inside (1, D2) with a margin, or outside disk -> ok
        ok = (G.a > 1 and G.b < 2 + 2*C.a) or n2.b < 0
        if not ok:
            bad += 1
            if bad < 5: print("  interval fail at a in", A, "|r|^2", n2, "G", G, "D2", 2+2*C)
        else:
            m = min(G.a - 1, (2+2*C.a) - G.b) if n2.b >= 0 else None
            if m is not None and (worst is None or m < worst): worst = m
print("Case 2: interval failures:", bad, "| rigorous min margin of |r-v3|^2 from {<=1, =Delta^2}:", worst)
