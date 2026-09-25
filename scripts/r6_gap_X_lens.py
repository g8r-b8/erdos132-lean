"""Thin lens K = D(c1,R) cap D(c2,R) of width W: greedy max-contact (A-points allowed, score >= 2),
seeded with a unit chord on the top arc at the middle.  Reports Def - 2|A| (whole configuration, honest:
every vertex counted, no interior idealisation)."""
import math, cmath, json, sys
from r6_gap_X_disk import Packing, Region
for R in (100, 400, 1600):
    for W in (1.8, 2.6, 3.5, 5.0):
        for sd in range(2):
            K = Region('lens', R, width=W)
            P = Packing(K, allowA=True, seed=sd)
            c = K.c[0]  # top arc centre is c1 = -i(R - W/2)
            th = 2*math.asin(0.5/R)
            for j in (0, 1):
                P.add(c + R*cmath.exp(1j*(math.pi/2 + (j-0.5)*th)), gen=False)
            for i in range(len(P.pts)): P.gen(i)
            P.run()
            st = P.stats()
            n, A = st['n'], st['A']
            print(json.dumps(dict(R=R, W=W, seed=sd, n=n, A=A, Def=st['Def'], DefMinus2A=st['DefMinus2A'],
                  per_A=round(st['DefMinus2A']/max(A, 1), 3), Adeg=st['Adeg'], mind=st['mind'])), flush=True)
