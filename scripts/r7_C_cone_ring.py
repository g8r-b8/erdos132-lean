"""R7/C: float consistency of Lemma AI on ienjoymath ring constructions (sanity; run with python3 + numpy)."""
import sys, math
# (4) consistency on ienjoymath constructions (floats, sanity only)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from ring16 import ring_core, spectrum, construction
import numpy as np
TOL = 1e-9
def ai_check(X, label):
    X = np.array(X); sp_ = spectrum(list(X)); D2v, Dv = sp_[-2][0], sp_[-1][0]
    M = np.abs(X[:, None] - X[None, :])
    S = (np.abs(M - D2v) < TOL).any(1)
    maxN = 0; checked = 0
    for wi in range(len(X)):
        Z = np.nonzero(np.abs(M[wi] - Dv) < TOL)[0]
        maxN = max(maxN, len(Z))
        if len(Z) < 5: continue
        ang = np.angle(X[Z] - X[wi]); ref = ang[0]
        order = Z[np.argsort(np.angle(np.exp(1j * (ang - ref))))]
        for zi_ in order[2:-2]:
            checked += 1
            assert not S[zi_], (label, wi, zi_)
    print('(4) %s: n=%d, max |X cap C(w,Delta)| = %d, interior points checked = %d, AI holds' % (label, len(X), maxN, checked))
for m in [8, 12, 20]:
    v, us, Dd, D2 = ring_core(m); ai_check(v + us, 'ring core m=%d' % m)
for n in [100, 300]:
    m = 2 * math.ceil(3 * n / 14); X, g, D2 = construction(m, n); ai_check(X, 'ienjoymath full n=%d' % n)
print('r7_C_cone: all checks pass')

# (5) adversarial random sets (floats, sanity): w, N >= 5 points on an arc of C(w,1) (span <= pi/3), plus random
# points in the disc intersection (so Delta = 1 is the diameter); some extra points placed at a chosen distance
# rho from an interior arc point.  Delta_2 := second-largest distance (no distance in (Delta_2, Delta) by definition).
import random
random.seed(7)
viol = tested = 0
for trial in range(4000):
    N = random.randint(5, 9)
    span = random.uniform(0.05, math.pi / 3)
    angs = sorted(random.uniform(0, span) for _ in range(N))
    Z = [complex(math.cos(t), math.sin(t)) for t in angs]
    X = [0j] + Z
    for _ in range(random.randint(0, 6)):
        for _t in range(50):
            p = complex(random.uniform(-0.2, 1.2), random.uniform(-0.2, 1.2))
            if all(abs(p - q) <= 1 - 1e-6 for q in X): X.append(p); break
    i = random.randint(2, N - 3)
    rho = random.uniform(0.5, 0.999)
    for _t in range(200):
        phi = random.uniform(0, 2 * math.pi)
        p = Z[i] + rho * complex(math.cos(phi), math.sin(phi))
        if all(abs(p - q) <= 1 - 1e-6 for q in X if q != Z[i]): X.append(p); break
    ds = sorted({round(abs(p - q), 9) for a_, p in enumerate(X) for q in X[a_ + 1:]})
    D, D2 = ds[-1], ds[-2]
    if abs(D - 1) > 1e-6: continue
    S = [any(abs(abs(p - q) - D2) < 1e-8 for q in X) for p in X]
    Zi = [X.index(z) for z in Z]
    for j in range(2, N - 2):
        tested += 1
        if S[Zi[j]]: viol += 1
print('(5) random adversarial sets: %d interior arc points tested, violations of AI: %d' % (tested, viol))
assert viol == 0
