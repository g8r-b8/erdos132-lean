import math, random
from r6_gap_X_aspect import trial
rng = random.Random(7); best = 0
for start in range(6):
    X = [(rng.uniform(-.97, .97), rng.uniform(-.97, .97)) for _ in range(rng.choice([3, 4, 6]))]
    q = trial(X) or 0
    for it in range(250):
        Y = [(x+rng.gauss(0, .05), y+rng.gauss(0, .05)) for x, y in X]
        qq = trial(Y)
        if qq and qq > q: X, q = Y, qq
    best = max(best, q); print(start, len(X), round(q, 3), flush=True)
print('hill-climb max ratio', best)
