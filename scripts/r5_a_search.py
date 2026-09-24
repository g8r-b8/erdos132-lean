"""R5/A: float search for sets with mu_j > n for all 2 <= j <= J (Delta_1 > Delta_2 > ... decreasing).

Float guidance only (squared distances grouped with relative tolerance 1e-9); every claimed record is
re-verified exactly by r5_a_exact.py from the recipe (same op conventions, see that file).

Usage (miniforge python3 with numpy):
  python3 r5_a_search.py beam  <seed> <J> <depth> <width> [orbit=0|m]   # point / orbit beam search
  python3 r5_a_search.py seeds                                       # profile table of seeds
seeds: ring<m> (m-gon + m servers), ringalt<m>, poly<m>, polyc<m> (polygon+centre)
"""
from __future__ import annotations
import sys, json, itertools, math
import numpy as np

TOL = 1e-9


# ---------------------------------------------------------------- recipes (float replay)
def replay(recipe):
    N = recipe["N"]; z = np.exp(2j * np.pi / N)
    P = []
    for op in recipe["ops"]:
        k = op[0]
        if k == "poly":
            m = op[1]; P += [z ** (t * (N // m)) for t in range(m)]
        elif k == "origin":
            P.append(0j)
        elif k == "cyc":
            P.append(sum(z ** a for a in op[1]) if op[1] else 0j)
        elif k == "rot":
            P.append(z ** op[2] * P[op[1]])
        elif k == "conj":
            P.append(np.conj(P[op[1]]))
        elif k == "orbit":
            i, m = op[1], op[2]; P += [z ** (t * (N // m)) * P[i] for t in range(1, m)]
        elif k == "cc":
            _, i, j, (a, b), (c, d), s = op
            P.append(cc_point(P[i], P[j], abs(P[a] - P[b]) ** 2, abs(P[c] - P[d]) ** 2, s))
        else:
            raise ValueError(op)
    return np.array(P, complex)


def cc_point(p, q, R1, R2, s):
    v = q - p; d2 = abs(v) ** 2
    A = (R1 - R2 + d2) / (2 * d2); H = R1 / d2 - A * A
    if H < -1e-12:
        return None
    return p + A * v + s * 1j * v * math.sqrt(max(H, 0.0))


def seed_recipe(name):
    import re
    kind, m = re.match(r"([a-z]+)(\d+)", name).groups(); m = int(m)
    N = m * 4 // math.gcd(m, 4)
    ops = [["poly", m]]
    if kind in ("ring", "ringalt"):
        k2 = (m - 3) // 2 if m % 2 else m // 2 - 1   # chord step of Delta_2 of the m-gon
        for j in range(m):
            if kind == "ringalt" and j % 2:
                continue
            ops.append(["cc", j, (j + 1) % m, [0, k2], [0, k2], 1])
    elif kind == "polyc":
        ops.append(["origin"])
    return {"N": N, "ops": ops, "name": name}


# ---------------------------------------------------------------- profiles
def classes_of(vals):
    """vals: 1-d array of squared distances. Returns decreasing class values and multiplicities."""
    v = np.sort(vals)[::-1]
    if len(v) == 0:
        return np.array([]), np.array([], int)
    brk = np.nonzero(v[:-1] - v[1:] > TOL * np.maximum(1.0, v[1:]))[0]
    starts = np.concatenate([[0], brk + 1]); ends = np.concatenate([brk + 1, [len(v)]])
    return v[starts], ends - starts


def profile(X):
    X = np.asarray(X)
    n = len(X); iu = np.triu_indices(n, 1)
    d2 = np.abs(X[:, None] - X[None]) ** 2
    return classes_of(d2[iu])


def stats(mults, n):
    rare = [j + 1 for j in range(1, len(mults)) if mults[j] <= n]
    return {"first_rare": rare[0] if rare else None, "s_rare": len(rare), "mu_delta": int(mults[-1])}


def objective(mults, n, J):
    """(hard, soft): hard = min_{2<=j<=J} mu_j - n ; soft = -sum deficits below n+1 (bigger is better)."""
    top = np.array(mults[1:J], int)
    if len(top) < J - 1:
        top = np.concatenate([top, np.zeros(J - 1 - len(top), int)])
    return int(top.min() - n), -int(np.maximum(0, n + 1 - top).sum())


# ---------------------------------------------------------------- candidates
def candidates(X, radii_idx, vals, pair_of_class, max_pairs=None, rng=None):
    """All intersections of circle(p_i, r_a) and circle(p_j, r_b), r's from top classes.
    Returns list of (point, op) with op a recipe 'cc' op."""
    n = len(X); out = []
    pairs = list(itertools.combinations(range(n), 2))
    if max_pairs and len(pairs) > max_pairs:
        rng.shuffle(pairs); pairs = pairs[:max_pairs]
    for (i, j) in pairs:
        for ka in radii_idx:
            for kb in radii_idx:
                R1, R2 = vals[ka], vals[kb]
                for s in (1, -1):
                    c = cc_point(X[i], X[j], R1, R2, s)
                    if c is None:
                        continue
                    out.append((c, ["cc", i, j, list(pair_of_class[ka]), list(pair_of_class[kb]), s]))
                    if abs(cc_point(X[i], X[j], R1, R2, 1) - cc_point(X[i], X[j], R1, R2, -1)) < 1e-12:
                        break
    return out


def class_reps(X):
    n = len(X); iu = np.triu_indices(n, 1)
    d2 = (np.abs(X[:, None] - X[None]) ** 2)[iu]
    vals, mults = classes_of(d2)
    reps = []
    for v in vals:
        k = int(np.argmin(np.abs(d2 - v)))
        reps.append((int(iu[0][k]), int(iu[1][k])))
    return vals, mults, reps


def orbit_points(c, m, N):
    z = np.exp(2j * np.pi / N)
    return [z ** (t * (N // m)) * c for t in range(1, m)]


def beam(seed, J, depth, width, orbit=0, per_state=60, max_pairs=4000, extra_orbit_conj=False, seedrng=0,
         log=True, K=None, collect=None):
    rng = np.random.default_rng(seedrng)
    rec0 = seed_recipe(seed) if isinstance(seed, str) else seed
    N = rec0["N"]
    X0 = replay(rec0)
    vals, mults, _ = class_reps(X0)
    states = [(objective(mults, len(X0), J), rec0["ops"], X0)]
    best_overall = states[0]
    if log:
        print(f"seed {rec0.get('name')} n={len(X0)} mults={list(mults[:J+3])} obj={states[0][0]}", flush=True)
    for dep in range(depth):
        new_states = []
        seen = set()
        for (sc, ops, X) in states:
            vals, mults, reps = class_reps(X)
            KK = K or (J + 2)
            ridx = list(range(0, min(KK, len(vals))))
            cands = candidates(X, ridx, vals, reps, max_pairs, rng)
            scored = []
            n = len(X)
            base_d2 = (np.abs(X[:, None] - X[None]) ** 2)[np.triu_indices(n, 1)]
            for c, op in cands:
                if np.min(np.abs(X - c)) < 1e-6:
                    continue
                add = [c] + (orbit_points(c, orbit, N) if orbit else [])
                if extra_orbit_conj:
                    add = add + [np.conj(a) for a in add]
                A = np.array(add)
                # dedupe orbit points
                if len(A) > 1:
                    dA = np.abs(A[:, None] - A[None]) + np.eye(len(A))
                    if dA.min() < 1e-6:
                        continue
                if np.min(np.abs(X[:, None] - A[None])) < 1e-6:
                    continue
                cross = (np.abs(X[:, None] - A[None]) ** 2).ravel()
                inner = (np.abs(A[:, None] - A[None]) ** 2)[np.triu_indices(len(A), 1)]
                v2, m2 = classes_of(np.concatenate([base_d2, cross, inner]))
                o = objective(m2, n + len(A), J)
                scored.append((o, c, op, A))
            scored.sort(key=lambda t: t[0], reverse=True)
            for o, c, op, A in scored[:per_state]:
                key = tuple(sorted(np.round(np.concatenate([X, A]), 6).tolist(), key=lambda z: (z.real, z.imag)))
                if key in seen:
                    continue
                seen.add(key)
                nops = ops + [op]
                if orbit:
                    nops = nops + [["orbit", n, orbit]]
                if extra_orbit_conj:
                    nops = nops + [["conj", t] for t in range(n, n + (orbit or 1))]
                new_states.append((o, nops, np.concatenate([X, A])))
        if not new_states:
            break
        new_states.sort(key=lambda t: t[0], reverse=True)
        if collect is not None:
            for o_, ops_, X_ in new_states:
                _, mm_ = profile(X_)
                collect.append((len(X_), [int(x) for x in mm_[:8]], stats(mm_, len(X_))))
        states = new_states[:width]
        if states[0][0] > best_overall[0]:
            best_overall = states[0]
        if log:
            s = states[0]; _, mm = profile(s[2])
            print(f" depth {dep+1}: best obj={s[0]} n={len(s[2])} mults={list(mm[:J+3])} {stats(mm, len(s[2]))}",
                  flush=True)
    return best_overall, rec0


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "seeds":
        for nm in ["poly5", "poly7", "poly9", "ring5", "ring7", "ring9", "ring11", "ring6", "ring8", "ringalt8",
                   "ringalt12", "polyc6", "polyc12"]:
            X = replay(seed_recipe(nm)); v, m = profile(X)
            print(nm, len(X), list(m[:8]), stats(m, len(X)))
    elif cmd == "beam":
        seed, J, depth, width = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        orbit = int(sys.argv[6]) if len(sys.argv) > 6 else 0
        (o, ops, X), rec0 = beam(seed, J, depth, width, orbit)
        rec = {"N": rec0["N"], "ops": ops, "name": f"beam-{seed}-J{J}-orb{orbit}"}
        print("BEST", o, json.dumps(rec))


def gadget_stats(X, J, K=None):
    """For every two-circle candidate point c (radii among the top K classes), check admissibility (no
    distance from c to X falls strictly above Delta_J unless it equals one of Delta_1..Delta_J) and count
    its incidences with classes 1..J.  Returns the best admissible candidates by total degree into
    classes 2..J, and a histogram of that total degree."""
    vals, mults, reps = class_reps(X)
    K = K or J + 2
    cands = candidates(X, list(range(min(K, len(vals)))), vals, reps)
    hist = {}; best = []
    if len(vals) < J:
        return {}, []
    lo = vals[J - 1] * (1 - 1e-9)
    for c, op in cands:
        d2 = np.abs(X - c) ** 2
        if d2.min() < 1e-10:
            continue
        big = d2[d2 > lo]
        deg = [int(np.sum(np.abs(d2 - vals[j]) < 1e-9 * max(1, vals[j]))) for j in range(J)]
        if sum(deg) != len(big):          # some distance above Delta_J is new
            continue
        tot = sum(deg[1:])
        hist[tot] = hist.get(tot, 0) + 1
        best.append((tot, deg, op))
    best.sort(key=lambda t: -t[0])
    return hist, best[:5]


if __name__ == "__main__" and sys.argv[1] == "gadgets":
    J = int(sys.argv[2])
    for nm in sys.argv[3:]:
        rec = json.load(open(nm)) if nm.endswith(".json") else seed_recipe(nm)
        X = replay(rec); h, b = gadget_stats(X, J)
        _, m = profile(X)
        print(nm, "n=", len(X), "top mults", list(m[:J]), "admissible-candidate histogram of deg into classes 2..J:",
              dict(sorted(h.items())), "best:", [(t, d) for t, d, _ in b[:3]])
