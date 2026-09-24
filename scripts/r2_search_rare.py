"""Question (a) on verified sets: multiplicities of all distances (tolerance 1e-20 on 30-digit data).
usage: .venv/bin/python r2_search_rare.py *_mp.json"""
import sys, json, itertools
import mpmath as mp
mp.mp.dps = 40
for fn in sys.argv[1:]:
    d = json.load(open(fn)); P = [(mp.mpf(a), mp.mpf(b)) for a, b in d['X']]; D = mp.mpf(d['D']); n = len(P)
    ds = sorted(mp.sqrt((P[i][0]-P[j][0])**2 + (P[i][1]-P[j][1])**2) for i, j in itertools.combinations(range(n), 2))
    cls = []
    for x in ds:
        if cls and abs(x - cls[-1][0]) < mp.mpf('1e-20'): cls[-1][1] += 1
        else: cls.append([x, 1])
    mult = sorted(((c, float(x)) for x, c in cls), reverse=True)
    rare = [x for x, c in cls if c <= n and abs(x - D) > mp.mpf('1e-20')]
    print(f"{fn}: n={n} distinct={len(cls)} top multiplicities={[(c, round(x, 6)) for c, x in mult[:4]]} "
          f"mu(Delta)={[c for x, c in cls if abs(x-D) < mp.mpf('1e-20')][0]} #rare non-diameter distances={len(rare)} "
          f"min gap between distinct distances={mp.nstr(min(cls[i+1][0]-cls[i][0] for i in range(len(cls)-1)), 4)}")
