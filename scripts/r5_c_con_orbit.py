"""R5/C/constr: orbit-beam search.  State = C_m-invariant set X; a move adds a whole C_m-orbit of a
candidate point c (c = intersection of two circles centred in X with radii among the top-R distance
values of X, reduced mod rotation), or removes an orbit.  The profile is recomputed from scratch, so
rankings may shift.  Float guidance only.
Usage: python3 r5_c_con_orbit.py obj start m steps B
   start in {ring, reg, F<k>, reg3 (m-gon + 3m-gon), rot (two rotated rings)}
"""
import sys, math
import numpy as np
from r5_c_con_search import (reg, ring, Fmk, top_mults, objectives, score, circ_int_all)


def rot(m, j):
    a = 2 * np.pi * j / m
    return np.array([[math.cos(a), -math.sin(a)], [math.sin(a), math.cos(a)]])


import os
DIH = os.environ.get('DIH', '0') == '1'


def orbit(c, m):
    O = [rot(m, j) @ c for j in range(m)]
    if DIH:
        cc = np.array([c[0], -c[1]])
        for j in range(m):
            q = rot(m, j) @ cc
            if min(np.linalg.norm(q - o) for o in O) > 1e-7:
                O.append(q)
    return np.array(O)


def canon(c, m):
    a = math.atan2(c[1], c[0]) % (2 * np.pi / m)
    if DIH and a > np.pi / m:
        a = 2 * np.pi / m - a
    r = np.hypot(*c)
    return np.array([r * math.cos(a), r * math.sin(a)])


def orbit_cands(X, m, R=5):
    vals, _ = top_mults(X, R)
    C = circ_int_all(X, np.sqrt(vals))
    C = np.array([canon(c, m) for c in C])
    key = np.round(C * 1e7).astype(np.int64)
    _, idx = np.unique(key, axis=0, return_index=True)
    C = C[idx]
    # include centre
    C = C[np.hypot(C[:, 0], C[:, 1]) > 1e-6]
    return C


def orbit_beam(X0, m, obj, steps=4, B=5, maxn=90, Nb=None):
    # orbits bookkeeping: X stored as list of orbit reps
    def build(reps):
        return np.vstack([orbit(r, m) for r in reps])
    reps0 = []
    for x in X0:
        c = canon(x, m)
        if not any(np.linalg.norm(c - r) < 1e-7 for r in reps0):
            reps0.append(c)
    beamset = [(score(top_mults(X0)[1], len(X0), obj), reps0)]
    best = beamset[0]
    seen = set()
    for st in range(steps):
        cand = []
        for sc, reps in beamset:
            X = build(reps)
            if len(X) + m <= maxn:
                for c in orbit_cands(X, m):
                    Y = np.vstack([X, orbit(c, m)])
                    D = np.sqrt(((Y[:, None] - Y[None]) ** 2).sum(-1))
                    np.fill_diagonal(D, 9)
                    if D.min() < 1e-5:
                        continue
                    mu = top_mults(Y)[1]
                    cand.append((score(mu, len(Y), obj), reps + [c]))
            if len(reps) > 2:
                for i in range(len(reps)):
                    r2 = reps[:i] + reps[i + 1:]
                    cand.append((score(top_mults(build(r2))[1], len(build(r2)), obj), r2))
        nb = []
        for sc, reps in sorted(cand, key=lambda t: -t[0]):
            h = hash(tuple(sorted(tuple(np.round(r, 6)) for r in reps)))
            if h in seen:
                continue
            seen.add(h)
            nb.append((sc, reps))
            if len(nb) >= B:
                break
        if not nb:
            break
        beamset = nb
        for t in beamset:
            if t[0] > best[0]:
                best = t
        sc, reps = beamset[0]
        mu = top_mults(build(reps))[1]
        print(f"   step {st}: n={len(build(reps))} mu={mu} {obj}={objectives(mu, len(build(reps)))[obj]:+.1f}", flush=True)
    return best[0], build(best[1]), best[1]


def start(name, m):
    if name == 'ring':
        return ring(m)
    if name == 'reg':
        return reg(m)
    if name.startswith('F'):
        return Fmk(m, m) if name == 'Fall' else None
    if name == 'reg3':
        return np.vstack([reg(m), reg(3 * m, 0.7, 0.13)])
    if name == 'rot':
        return np.vstack([ring(m), ring(m) @ rot(2 * m, 1).T * 0.9])
    raise ValueError(name)


if __name__ == "__main__":
    obj, name, m = sys.argv[1], sys.argv[2], int(sys.argv[3])
    steps = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    B = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    X0 = start(name, m)
    sc, Y, reps = orbit_beam(X0, m, obj, steps, B)
    mu = top_mults(Y)[1]
    print(f"{obj} {name} m={m}: start mu={top_mults(X0)[1]} -> n={len(Y)} mu={mu} "
          f"all={ {k: round(v, 1) for k, v in objectives(mu, len(Y)).items()} }")
    print("   reps:", [tuple(np.round(r, 10)) for r in reps], flush=True)
