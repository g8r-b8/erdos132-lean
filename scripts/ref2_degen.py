"""Second referee (REFEREE2_A2.md): adversarial search against §8 (degenerate regime,
Delta > 1.94 Delta2) of WRITEUP_A2.md, targeting Step 4 (I <= |B| + |W|).

Scale Delta = 1, Delta2 = r in (1/2, 1/1.94).  Star: y = 0, A on the unit circle (all pairwise
chords <= r).  K = D(y,r) ∩ ∩_a D(a,r).  For fixed W = {y} ∪ A the best B (for mu(Delta2) - n)
is the set of vertices of ∂K (a point interior to a single W-arc adds 1 to I and 1 to n: neutral;
δ plays no role in §8).  So
     excess(W) = [extreme A-pair at distance r] + sum_{b vertex} (#W-circles through b) - #vertices - |W|
and §8 claims mu(Delta2) - n <= 1, i.e. excess <= 1.

To stress the degenerate-arc case (J_w = {b}, three or more W-circles through one vertex) the
search *constructs* concurrencies: new A-points are placed on C(y,1) ∩ C(b,r) for current
vertices b, so C(a,r) passes through b exactly (up to rounding).  Coincidence tolerance 1e-9;
we report the smallest non-coincident gap seen to show the classification is unambiguous.
Floating point; this is a falsification search, not a proof.
"""
import math, random, cmath

TOL = 1e-9

def circ_int(c1, c2, r1, r2):
    d = abs(c2 - c1)
    if d < 1e-15 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    h = math.sqrt(max(h2, 0.0))
    u = (c2 - c1) / d
    m = c1 + a*u
    return [m + 1j*h*u, m - 1j*h*u]

def analyse(W, r, stats):
    pts = []
    for i in range(len(W)):
        for j in range(i+1, len(W)):
            pts += circ_int(W[i], W[j], r, r)
    verts = []
    for p in pts:
        if all(abs(p - w) <= r + TOL for w in W):
            if all(abs(p - q) > 1e-7 for q in verts):
                verts.append(p)
    I = 0
    for b in verts:
        for w in W:
            g = abs(abs(b - w) - r)
            if g <= TOL:
                I += 1
            else:
                stats['gap'] = min(stats['gap'], g)
    A = W[1:]
    angs = sorted(cmath.phase(a) for a in A)
    pair = 0
    if len(A) >= 2:
        # A within an arc < 120deg; extreme pair
        ext = abs(cmath.exp(1j*angs[0]) - cmath.exp(1j*angs[-1]))
        pair = 1 if abs(ext - r) <= TOL else 0
    return pair + I - len(verts) - len(W), verts

def valid(A, r):
    for i in range(len(A)):
        for j in range(i+1, len(A)):
            if abs(A[i] - A[j]) > r + TOL or abs(A[i]-A[j]) < 1e-6:
                return False
    return True

random.seed(12345)
stats = {'gap': 1.0}
best = -10; bestcfg = None; trials = 0
for trial in range(4000):
    r = random.uniform(0.5001, 1/1.94 - 1e-4)
    theta_max = 2*math.asin(r/2)            # max angular separation within A
    A = [cmath.exp(1j*random.uniform(-0.3, 0.3))]
    # optionally force extreme pair at exact distance r
    if random.random() < 0.5:
        A.append(A[0]*cmath.exp(1j*theta_max))
    for step in range(random.randint(1, 9)):
        W = [0j] + A
        _, verts = analyse(W, r, stats)
        cands = []
        for b in verts:
            cands += [p for p in circ_int(0j, b, 1.0, r)]
        if random.random() < 0.3 or not cands:
            cands.append(cmath.exp(1j*random.uniform(-0.3, 0.3)))
        a = random.choice(cands)
        if valid(A + [a], r):
            A.append(a)
    W = [0j] + A
    ex, verts = analyse(W, r, stats)
    trials += 1
    if ex > best:
        best, bestcfg = ex, (r, len(A), len(verts))
    assert ex <= 1, ("COUNTEREXAMPLE to mu(Delta2) <= n+1", r, A)
print(f"{trials} constructed star configurations; max [mu(Delta2) - n] = {best} at (r, |A|, #vertices) = {bestcfg}")
print(f"smallest non-coincident |dist - r| seen: {stats['gap']:.2e} (vs tolerance {TOL:g})")

# also: count configurations with a vertex on >= 3 W-circles (degenerate arcs actually exercised)
random.seed(7); multi = 0
for trial in range(1500):
    r = random.uniform(0.5001, 1/1.94 - 1e-4)
    A = [cmath.exp(1j*random.uniform(-0.2, 0.2))]
    for step in range(6):
        _, verts = analyse([0j]+A, r, stats)
        c = []
        for b in verts: c += circ_int(0j, b, 1.0, r)
        if c:
            a = random.choice(c)
            if valid(A+[a], r): A.append(a)
    W = [0j]+A
    ex, verts = analyse(W, r, stats)
    if any(sum(abs(abs(b-w)-r) <= TOL for w in W) >= 3 for b in verts):
        multi += 1
    assert ex <= 1
print(f"{multi}/1500 concurrency-constructed configurations had a vertex on >= 3 W-circles; all satisfy the bound")
