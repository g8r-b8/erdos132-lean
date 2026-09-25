#!/usr/bin/env python3
"""r7_B_rules.py -- adversarial beam search of the Region II discharging (report section 3), FLOAT screen.

Uses B1's flat growth model and rule engine (copies: r6_below_rule_check_B1copy.py, r6_below_cluster_search.py),
at Region II values of t in [sqrt3/2 + 0.03, 1], seeding y at the depths of the two heavy types:
A (h = sqrt3/2) and D_II (h in [0, 1 - t]).  The beam maximises the final charge after discharging.
Also records which heavy types occur (only A and Dtype expected) and the max raw v.
"""
import math, sys, importlib.util, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("rc", os.path.join(HERE, "r6_below_rule_check_B1copy.py"))
rc = importlib.util.module_from_spec(spec); spec.loader.exec_module(rc)
cs = rc.cs
TYPES = collections.Counter(); MAXV = [0]

orig = rc.run_rules
def run_rules(pts, t):
    R = [p for p in pts if p[2] == 'R']
    for y in R:
        nb = [q for q in pts if q is not y and cs.unit(y, q)]
        v = len(nb) + sum(1 for q in nb if q[2] != 'R')
        MAXV[0] = max(MAXV[0], v)
        if v >= 8:
            K = [rc.ang(y, q) for q in nb if q[2] == 'K']; Dd = [rc.ang(y, q) for q in nb if q[2] == 'D']
            if len(nb) == 6 and len(K) == 2 and all(rc.near(abs(k), 30) for k in K):
                TYPES['A'] += 1
            elif len(nb) == 5 and len(K) == 2 and len(Dd) == 1:
                TYPES['Dtype'] += 1
            else:
                TYPES[('OTHER', len(nb), tuple(round(k) for k in K), tuple(round(d) for d in Dd))] += 1
    return orig(pts, t)
rc.run_rules = run_rules

def main():
    maxR = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = math.sqrt(3) / 2 + 0.03
    tot = 0; nseen = 0; unk = []
    for t in [t0, 0.91, 0.93, 0.95, 0.97, 0.99, 1.0]:
        hs = [math.sqrt(3) / 2] + [(1 - t) * k / 4 for k in range(5)]
        wt = 0
        for h in hs:
            (w, pts), u, ns = rc.search(t, h, maxR)
            wt = max(wt, w); nseen += ns; unk += u
        tot = max(tot, wt)
        print(f"t={t:.4f}: max final charge = {wt:.3f}", flush=True)
    print("configs visited:", nseen, " max final charge:", tot, " max raw v:", MAXV[0])
    print("heavy-type occurrences:", dict(TYPES))
    print("rule anomalies:", len(unk), unk[:8])

if __name__ == '__main__':
    main()
