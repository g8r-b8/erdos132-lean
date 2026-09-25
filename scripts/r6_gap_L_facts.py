"""R6-B-gap/L: random adversarial test of fact (F3): a neutral pair transition across a chord of
length D > 1 (rungs e at b, e' at b' = b + D, |q' - q| = 1, both rungs strictly below the chord line)
has theta' < theta (angles in (180,360) measured from the chord direction).  Also (F1): D = 1 forces
e = e' (or a degenerate coincidence).  Floats only (sanity check; the proofs are one-line identities)."""
import math, random
random.seed(1)
bad = 0; n = 0; minmargin = 9
for _ in range(400000):
    D = random.choice([1.0, random.uniform(1, 3)])
    th = random.uniform(math.pi, 2 * math.pi)
    e = complex(math.cos(th), math.sin(th)); q = e
    # q' on circle(q,1) and on circle(D,1): intersection points
    c = complex(D, 0); dd = abs(c - q)
    if dd > 2 or dd < 1e-12: continue
    mid = (q + c) / 2; h = math.sqrt(max(0.0, 1 - (dd / 2) ** 2)); nrm = (c - q) / dd * 1j
    for qq in (mid + h * nrm, mid - h * nrm):
        ep = qq - c
        if ep.imag >= 0 or q.imag >= 0: continue            # both rungs strictly on the inner side
        if abs(qq) < 1 - 1e-12 or abs(q - c) < 1 - 1e-12: continue   # min distance 1
        thp = math.atan2(ep.imag, ep.real) % (2 * math.pi)
        n += 1
        if D == 1.0:
            if abs(ep - e) > 1e-7 and abs(qq) > 1 + 1e-9 and abs(q - c) > 1 + 1e-9: bad += 1
        else:
            minmargin = min(minmargin, th - thp)
            if not thp < th: bad += 1
print('cases', n, 'violations', bad, 'min (theta - theta\') over D>1 cases (rad)', minmargin)
