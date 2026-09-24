"""Adversarial float check of the proved local lemmas on greedy2 sets, at every hull vertex p with
exactly 3 Delta2-neighbours (no core assumption needed):  F1 (al,be<=60), L1' (r off line, |r w_opp|=D,
|r w_same|<=1), middle-lemma (<=1 r per side), F3 (outer nbrs' other nbrs strictly inner),
(D,D)-exclusion, dichotomy (|pr|=D or [w_opp r] crosses open (p w2))."""
import sys, math, random, itertools
import r2_local_tgreedy2 as G2
from r2_local_tgreedy import stats, TOL
def cr(o, a, b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def segx(a, b, c, d):
    return cr(a, b, c)*cr(a, b, d) < -1e-12 and cr(c, d, a)*cr(c, d, b) < -1e-12
viol = {}; checked = 0
def bad(k): viol[k] = viol.get(k, 0)+1
for s in range(int(sys.argv[1]), int(sys.argv[2])):
    rng = random.Random(s)
    for tr in range(int(sys.argv[3])):
        D = rng.uniform(1.01, 1.95); X = G2.run(D, 24, rng, 0.3)
        ds = sorted({round(math.dist(a, b), 7) for a, b in itertools.combinations(X, 2)})
        if len(ds) < 2 or abs(ds[-2]-1) > 1e-6 or abs(ds[-1]-D) > 1e-6: continue
        t, mu, core, H, adj = stats(X)
        isD = lambda i, j: abs(math.dist(X[i], X[j])-D) < 1e-7
        for p in H:
            if len(adj[p]) != 3: continue
            checked += 1
            ws = adj[p]; P = X[p]
            # angular order: middle = the one with the other two strictly on opposite sides
            for w2 in ws:
                o = [w for w in ws if w != w2]
                if cr(P, X[w2], X[o[0]])*cr(P, X[w2], X[o[1]]) < 0: break
            w1, w3 = o
            if cr(P, X[w2], X[w1]) > 0: w1, w3 = w3, w1   # w1 below line p->w2, w3 above
            for x, y in ((w1, w2), (w2, w3)):
                if math.dist(X[x], X[y]) > 1+1e-9: bad('F1')
            side = {}
            for r in adj[w2]:
                if r == p: continue
                c = cr(P, X[w2], X[r])
                if abs(c) < 1e-9: bad('L1 online'); continue
                opp, same = (w1, w3) if c > 0 else (w3, w1)
                side[c > 0] = side.get(c > 0, 0)+1
                if r != opp and not isD(r, opp): bad('L1 D to opposite')
                if math.dist(X[r], X[same]) > 1+1e-9: bad('L1 same<=1')
                if r not in H: bad('r extreme')
                if isD(p, r) and isD(w1, w3): bad('(D,D)')
                if not isD(p, r) and not segx(X[opp], X[r], P, X[w2]): bad('dichotomy')
            if any(v > 1 for v in side.values()): bad('middle lemma')
            for wo, wi in ((w1, w2), (w3, w2)):
                for r1 in adj[wo]:
                    if r1 == p: continue
                    if not (cr(P, X[wo], X[r1])*cr(P, X[wo], X[wi]) > 1e-12): bad('F3')
print('checked', checked, 'violations', viol)
