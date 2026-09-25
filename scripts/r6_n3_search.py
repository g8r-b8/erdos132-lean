"""R6 / Theorem N3: adversarial float search in the relaxed 'slot model' (sanity check of Lemmas P, M, H, Pin).

Model of a good point y (angles psi from the outer normal n0, heights c = cos psi):
  K-row neighbour : h - eps <= c <= h and |psi| < 90 + eps0
  D neighbour     : c >= h + t - eps            (in S or not; for an upper bound on v every D counts as S)
  int-K neighbour : c < h
  D-D pairs       : |c1 - c2| <= 2 tau*          (Lemma DN)
  K-D pair, D higher by > 2 sin eps0 / cos eps0 : exception, |t - (c_D - c_K)| <= 0.041  (Lemma Pin)
Neighbours pairwise >= 60 degrees. The relaxation is sound: every configuration of a real good y satisfies it.
We search random angle sets and all type assignments and record every configuration with v = deg + m >= 9,
checking that it is one of F6, F5, HF1, HF2, cap (and never both fan-type and cap-type t-ranges).
"""
import math, random, itertools

eps0 = 1 / 50; eps = math.tan(eps0); taus = 0.0245
random.seed(6)


def feasible_types(psis, h, t):
    """yield type tuples (K/D/I) consistent with the model"""
    opts = []
    for p in psis:
        c = math.cos(math.radians(p)); o = []
        if h - eps <= c <= h and abs(p) < 90 + math.degrees(eps0): o.append('K')
        if c >= h + t - eps: o.append('D')
        if c < h: o.append('I')
        if not o: return
        opts.append(o)
    for ty in itertools.product(*opts):
        cs = [math.cos(math.radians(p)) for p in psis]
        good = True
        for i, j in itertools.combinations(range(len(psis)), 2):
            if ty[i] == ty[j] == 'D' and abs(cs[i] - cs[j]) > 2 * taus: good = False
            for a, b in ((i, j), (j, i)):
                if ty[a] == 'K' and ty[b] == 'D':
                    dc = cs[b] - cs[a]
                    if dc > 2 * math.sin(eps0) / math.cos(eps0) + 1e-9 and abs(t - dc) > 0.041: good = False
        if good: yield ty


def classify(psis, ty):
    S = sorted((p, k) for p, k in zip(psis, ty) if k in 'KD')
    kinds = ''.join(k for _, k in S)
    near = lambda p, q, tol=3.5: abs(p - q) <= tol
    ang = [p for p, _ in S]
    if len(S) == 4 and kinds == 'KDDK' and all(near(a, b) for a, b in zip(ang, (-90, -30, 30, 90))):
        return 'F6' if len(psis) == 6 else 'F5'
    if len(S) == 3 and len(psis) == 6:
        if kinds == 'KDK' and near(ang[0], -60) and near(ang[1], 0) and near(ang[2], 60): return 'cap'
        if kinds in ('KDK', 'KKD', 'DKK', 'KDD', 'DDK'):
            if all(any(near(a, b) for b in (-90, -30, 30, 90)) for a in ang): return 'HF'
    return None


def rand_angles(k):
    for _ in range(1000):
        base = random.uniform(-180, 180)
        if k == 6:
            return [((base + 60 * i + 180) % 360) - 180 for i in range(6)]
        a = sorted(random.uniform(-180, 180) for _ in range(k))
        gaps = [(a[(i + 1) % k] - a[i]) % 360 for i in range(k)]
        if min(gaps) >= 60: return a
    return None


found = {}; bad = []; trials = 0
for it in range(200000):
    k = random.choice([5, 6])
    ps = rand_angles(k)
    if ps is None: continue
    # bias towards symmetric configurations half the time
    if random.random() < 0.5 and k == 6:
        off = random.choice([0, 30]) + random.uniform(-3, 3)
        ps = [((off + 60 * i + 180) % 360) - 180 for i in range(6)]
    if random.random() < 0.3 and k == 5:
        ps = [-90 + random.uniform(-1, 1), -30 + random.uniform(-1, 1), 30 + random.uniform(-1, 1),
              90 + random.uniform(-1, 1), random.uniform(152, 208)]
    h = random.choice([random.uniform(0, 1), random.uniform(0, 0.05), random.uniform(0.45, 0.55)])
    t = random.choice([random.uniform(0, 1.5), random.uniform(0.8, 0.95), random.uniform(0.45, 0.55), random.uniform(0, 0.05)])
    for ty in feasible_types(ps, h, t):
        trials += 1
        m = sum(1 for x in ty if x in 'KD'); v = len(ps) + m
        if v >= 9:
            c = classify(ps, ty)
            if c is None: bad.append((ps, ty, h, t))
            else:
                found[c] = found.get(c, 0) + 1
                if c == 'cap': assert 0.43 <= t <= 0.57
                else: assert 0.74 <= t <= 0.99
print(f"type-assignments tested: {trials}; heavy configurations by class: {found}; unclassified: {len(bad)}")
for b in bad[:5]: print("  UNCLASSIFIED", b)
assert not bad
print("slot-model search: every v >= 9 configuration is F6/F5/HF/cap with the pinned t-range")
