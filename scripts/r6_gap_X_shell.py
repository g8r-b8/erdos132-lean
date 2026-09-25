"""Adversarial test of the Euler-shell bound on full disks / bands (float).
For each configuration: Def - 2|A| versus the proved floor
  max over rho of  -( 3*|shell(rho)| + 2*t*|A|/R + 3 )  (case ii)  / -(2*pi*t + 3 + 3|shell|) (case i),  t = rho + 1/2,
we simply report the weaker of the two floors: floor(rho) = -(3|shell| + max(2t|A|/R, 2*pi*t) + 3)."""
import math, random, json, sys
from r6_gap_X_disk import Packing, Region, seed_disk_pattern
def floor_best(P, R, A):
    dep = [P.K.depth(z) for z in P.pts]
    best = -1e18
    for rho10 in range(0, int(10*R)):
        rho = rho10/10
        if R <= rho + 0.5: break
        sh = sum(1 for d in dep if rho <= d < rho+1)
        t = rho + 0.5
        fl = -(3*sh + max(2*t*A/R, 2*math.pi*t) + 3)
        best = max(best, fl)
    return best
rows = []
for R in (6, 9, 12, 16, 22):
    for mode in ('A-greedy', 'tri4', 'tri2'):
        for sd in range(3):
            P = Packing(Region('disk', R), allowA=True, seed=sd)
            if mode == 'A-greedy':
                P.add(complex(R, 0), gen=False); P.add(complex(R*math.cos(2*math.asin(0.5/R)), R*math.sin(2*math.asin(0.5/R))))
            else:
                seed_disk_pattern(P, R, 4 if mode == 'tri4' else 2)
            P.run()
            st = P.stats()
            fl = floor_best(P, R, st['A'])
            rows.append((R, mode, sd, st['n'], st['A'], st['Def'], st['DefMinus2A'], round(fl, 1), st['mind'] > 1-1e-9))
            print(rows[-1], flush=True)
viol = [r for r in rows if r[6] < r[7]]
print('violations of proved floor:', viol)
