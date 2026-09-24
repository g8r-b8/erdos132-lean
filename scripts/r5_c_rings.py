"""R5/C: search over unions of t concentric C_m-symmetric rings (dihedral phases 0 or 1/2 step,
optionally free phases, optional centre point) for profiles with many frequent top distances.

Each ring i: r_i e^{2 pi i (j + phi_i)/m}, j = 0..m-1, r_1 = 1.  Distances come in C_m-orbits, so
the whole profile is computed from O(t^2 m) orbit distances.  Coincidence equations between
pairs of orbit distances are solved with fsolve from random starts (DOF = t-1 radii
[+ t-1 phases if free]); every solution is profiled and tested against the targets
    T1: mu2 + mu3 > 5n/2         T2: mu2 + mu3 + mu4 > 3n
    T3: min(mu2, mu3) > n        T4: min(mu2, mu3, mu4) > n
Float guidance only (tol 1e-9 after polishing); interesting hits are re-checked with
r5_c_exact.py.
Usage: python3 r5_c_rings.py m t [free] [centre] [trials]
"""
import sys, itertools, random
import numpy as np
from scipy.optimize import fsolve

TOL = 1e-9
import os
TOP = int(os.environ.get('TOP', '0'))


def orbits(m, t, centre):
    """list of (i, k_ring_i_to_ring_j..., weight) describing orbit distance functions.
    item = (i, j, k, w): distance between ring i vertex 0 and ring j vertex k; w = #pairs."""
    O = []
    for i in range(t):
        for k in range(1, m // 2 + 1):
            w = m if 2 * k != m else m // 2
            O.append((i, i, k, w))
    for i, j in itertools.combinations(range(t), 2):
        for k in range(m):
            O.append((i, j, k, m))
    if centre:
        for i in range(t):
            O.append((i, -1, 0, m))
    return O


def odist(o, r, ph, m):
    i, j, k, w = o
    if j == -1:
        return r[i]
    a = 2 * np.pi * (k + ph[j] - ph[i]) / m
    return np.sqrt(max(r[i] ** 2 + r[j] ** 2 - 2 * r[i] * r[j] * np.cos(a), 0.0))


def profile(m, t, centre, r, ph, O):
    ds = sorted(((odist(o, r, ph, m), o[3]) for o in O), key=lambda z: -z[0])
    if ds[-1][0] < 1e-4 * ds[0][0]:
        return None  # (nearly) coincident points
    vals, mu = [], []
    for d, w in ds:
        if vals and abs(vals[-1] - d) < 1e-7:
            mu[-1] += w
        else:
            vals.append(d); mu.append(w)
    return vals, mu


def params(x, t, free, dihedral_ph):
    r = np.concatenate([[1.0], x[:t - 1]])
    if free:
        ph = np.concatenate([[0.0], x[t - 1:2 * t - 2]])
    else:
        ph = np.array(dihedral_ph, float)
    return r, ph


def run(m, t, free=False, centre=False, trials=20000, seed=1):
    rng = random.Random(seed)
    O = orbits(m, t, centre)
    n = t * m + (1 if centre else 0)
    dof = (t - 1) * (2 if free else 1)
    best = {}
    hits = []
    phase_choices = [p for p in itertools.product([0.0, 0.5], repeat=t - 1)] if not free else [None]
    for trial in range(trials):
        dph = [0.0] + list(rng.choice(phase_choices)) if not free else None
        x0 = np.array([rng.uniform(0.05, 1.3) for _ in range(t - 1)] +
                      ([rng.uniform(0, 1) for _ in range(t - 1)] if free else []))
        if TOP:  # equations only among the TOP largest orbit distances at x0
            r0, p0 = params(x0, t, free, dph)
            ordr = sorted(range(len(O)), key=lambda a: -odist(O[a], r0, p0, m))[:TOP]
            eqs = [tuple(rng.sample(ordr, 2)) for _ in range(dof)]
        else:
            eqs = [tuple(rng.sample(range(len(O)), 2)) for _ in range(dof)]

        def F(x):
            r, ph = params(x, t, free, dph)
            return [odist(O[a], r, ph, m) - odist(O[b], r, ph, m) for a, b in eqs]
        try:
            x, info, ier, msg = fsolve(F, x0, full_output=True)
        except Exception:
            continue
        if ier != 1 or max(abs(v) for v in F(x)) > 1e-11:
            continue
        r, ph = params(x, t, free, dph)
        if np.any(r[1:] <= 1e-6):
            continue
        P = profile(m, t, centre, r, ph, O)
        if P is None:
            continue
        vals, mu = P
        if len(mu) < 4:
            continue
        m1, m2, m3, m4 = mu[:4]
        key = (tuple(np.round(r, 7)), tuple(np.round(ph % 1, 7)))
        sc = {'T1': m2 + m3 - 2.5 * n, 'T2': m2 + m3 + m4 - 3 * n,
              'T3': min(m2, m3) - n, 'T4': min(m2, m3, m4) - n}
        for kk, v in sc.items():
            if kk not in best or v > best[kk][0]:
                best[kk] = (v, mu[:7], key)
        if sc['T1'] > 0 or sc['T2'] > 0 or sc['T4'] > 0:
            hits.append((sc, mu[:7], key))
    return n, best, hits


if __name__ == "__main__":
    m = int(sys.argv[1]); t = int(sys.argv[2])
    free = len(sys.argv) > 3 and sys.argv[3] == '1'
    centre = len(sys.argv) > 4 and sys.argv[4] == '1'
    trials = int(sys.argv[5]) if len(sys.argv) > 5 else 20000
    n, best, hits = run(m, t, free, centre, trials)
    print(f"m={m} t={t} free={free} centre={centre} n={n}")
    for k, v in sorted(best.items()):
        print(" best", k, "score", round(v[0], 3), "mults", v[1], "params", v[2])
    seen = set()
    for sc, mu, key in hits:
        if key in seen:
            continue
        seen.add(key)
        print(" HIT", {k: round(v, 2) for k, v in sc.items()}, mu, key)
