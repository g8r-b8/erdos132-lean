"""R5/C/constr: beam / greedy augmentation search for planar sets with many frequent TOP distances.

Targets (mu_j = multiplicity of the j-th largest distance, n = |X|):
  C1: mu2+mu3 - 5n/2      C2: mu2+mu3+mu4 - 3n      C3: min(mu2,mu3,mu4) - n
  C4: mu1+mu2+mu3 - 3n    sJ: min(mu2..muJ) - n  (J = 3,4,5)
A move adds a point (intersection of two circles centred in X with radii among the top-R distance
values of X -- ranking is recomputed from scratch, so distances may shift rank) or deletes a point.
Float guidance only (classes merged at relative tol 1e-9); records must be re-verified exactly.
"""
import sys, itertools, math
import numpy as np

TOL = 1e-9


def reg(m, r=1.0, phase=0.0):
    a = 2 * np.pi * np.arange(m) / m + phase
    return np.c_[r * np.cos(a), r * np.sin(a)]


def sqd(X):
    return ((X[:, None] - X[None]) ** 2).sum(-1)


def top_mults(X, J=6):
    """(values, mults) of the J largest distinct (squared) distances"""
    D = sqd(X)
    iu = np.triu_indices(len(X), 1)
    d = np.sort(D[iu])[::-1]
    vals, mults = [], []
    for x in d:
        if vals and abs(vals[-1] - x) <= TOL * max(1.0, x):
            mults[-1] += 1
        else:
            if len(vals) == J:
                break
            vals.append(x); mults.append(1)
    return vals, mults


def objectives(mu, n):
    mu = list(mu) + [0] * (6 - len(mu))
    return {'C1': mu[1] + mu[2] - 2.5 * n, 'C2': mu[1] + mu[2] + mu[3] - 3 * n,
            'C3': min(mu[1:4]) - n, 'C4': mu[0] + mu[1] + mu[2] - 3 * n,
            's3': min(mu[1:3]) - n, 's4': min(mu[1:4]) - n, 's5': min(mu[1:5]) - n}


def score(mu, n, obj):
    """primary objective + small smooth tie-breaker"""
    o = objectives(mu, n)
    mu = list(mu) + [0] * (6 - len(mu))
    if obj in ('s3', 's4', 's5', 'C3'):
        J = {'s3': 3, 's4': 4, 's5': 5, 'C3': 4}[obj]
        smooth = sum(min(m_ - n, 0) for m_ in mu[1:J]) + 0.01 * sum(mu[1:J])
        return o[obj] + 0.1 * smooth / max(n, 1)
    return o[obj] + 0.001 * sum(mu[:5])


def circ_int_all(X, radii):
    """all intersections of circles centred at X[a], X[b] with radii r, s in radii (vectorised)"""
    n = len(X)
    A, B = np.triu_indices(n, 1)
    P, Q = X[A], X[B]
    dv = Q - P
    d = np.linalg.norm(dv, axis=1)
    u = dv / d[:, None]
    w = np.c_[-u[:, 1], u[:, 0]]
    out = []
    for r in radii:
        for s in radii:
            a = (r * r - s * s + d * d) / (2 * d)
            h2 = r * r - a * a
            ok = h2 >= -1e-12
            h = np.sqrt(np.clip(h2, 0, None))
            base = P + a[:, None] * u
            out.append((base + h[:, None] * w)[ok])
            out.append((base - h[:, None] * w)[ok])
    C = np.vstack(out) if out else np.zeros((0, 2))
    # dedupe
    key = np.round(C * 1e7).astype(np.int64)
    _, idx = np.unique(key, axis=0, return_index=True)
    C = C[idx]
    dmin = np.sqrt(((C[:, None] - X[None]) ** 2).sum(-1)).min(1)
    return C[dmin > 1e-5]


def add_moves(X, R=5, J=6):
    vals, _ = top_mults(X, R)
    radii = np.sqrt(vals)
    C = circ_int_all(X, radii)
    return C


def eval_add(X, C, base_D, J=6):
    """top-J mults of X u {c} for each candidate c (fast merge with the old distance multiset)"""
    n = len(X)
    iu = np.triu_indices(n, 1)
    old = np.sort(base_D[iu])[::-1]
    # old distinct classes (enough of them)
    ov, om = [], []
    for x in old:
        if ov and abs(ov[-1] - x) <= TOL * max(1, x):
            om[-1] += 1
        else:
            if len(ov) == J + 2:
                break
            ov.append(x); om.append(1)
    ov = np.array(ov)
    DC = ((C[:, None] - X[None]) ** 2).sum(-1)
    L = len(ov) - 1
    tolv = TOL * np.maximum(1, ov[:L])
    cnt = (np.abs(DC[:, :, None] - ov[None, None, :L]) <= tolv).sum(1)  # M x L
    matched = (np.abs(DC[:, :, None] - ov[None, None, :L]) <= tolv).any(2)
    extra = ((DC > ov[L - 1] + TOL) & ~matched).any(1)
    base = np.array(om[:L])[None] + cnt
    res = [list(r[:J]) for r in base]
    for i in np.nonzero(extra)[0]:
        dd = DC[i][DC[i] > ov[L - 1] + TOL]
        vals = list(ov[:L]); mu = list(base[i])
        for x in sorted(dd[~matched[i][DC[i] > ov[L - 1] + TOL]], reverse=True):
            k = int(np.searchsorted(-np.array(vals), -x - TOL * max(1, x)))
            if k < len(vals) and abs(vals[k] - x) <= TOL * max(1, x):
                mu[k] += 1
            elif k > 0 and abs(vals[k - 1] - x) <= TOL * max(1, x):
                mu[k - 1] += 1
            else:
                vals.insert(k, x); mu.insert(k, 1)
        res[i] = mu[:J]
    return res


def beam(X0, obj, steps=10, B=6, R=5, allow_del=True, maxn=80, verbose=False, per=3):
    beamset = [(score(top_mults(X0)[1], len(X0), obj), X0)]
    best = beamset[0]
    seen = set()
    history = []
    for st in range(steps):
        cand = []
        for sc, X in beamset:
            n = len(X)
            if n < maxn:
                C = add_moves(X, R)
                if len(C):
                    mus = eval_add(X, C, sqd(X))
                    scs = np.array([score(mu, n + 1, obj) for mu in mus])
                    order = np.argsort(-scs)[:B * per]
                    for o in order:
                        cand.append((scs[o], np.vstack([X, C[o]])))
            if allow_del and n > 14:
                for i in range(n):
                    Y = np.delete(X, i, 0)
                    cand.append((score(top_mults(Y)[1], n - 1, obj), Y))
        nb = []
        for sc, Y in sorted(cand, key=lambda t: -t[0]):
            k = tuple(sorted(map(tuple, np.round(Y, 6).tolist())))
            h = hash(k)
            if h in seen:
                continue
            seen.add(h)
            # recompute exactly (float) to avoid merge artefacts
            mu = top_mults(Y)[1]
            nb.append((score(mu, len(Y), obj), Y))
            if len(nb) >= B:
                break
        if not nb:
            break
        beamset = nb
        for sc, Y in beamset:
            if sc > best[0]:
                best = (sc, Y)
        if verbose:
            sc, Y = beamset[0]
            mu = top_mults(Y)[1]
            print(f"  step {st}: n={len(Y)} mu={mu} obj={objectives(mu, len(Y))[obj]:+.1f}", flush=True)
        history.append(beamset[0])
    return best


# ---------------------------------------------------------------- starting sets
def ring(m):
    V = reg(m)
    D2 = 2 * np.cos(np.pi / m) if m % 2 == 0 else 2 * np.cos(3 * np.pi / (2 * m))
    S = []
    for j in range(m):
        th = 2 * np.pi * (j + .5) / m
        u = np.array([np.cos(th), np.sin(th)])
        c = V[j] @ u
        t = -c + np.sqrt(c * c - 1 + D2 ** 2)
        S.append(-t * u)
    return np.vstack([V, S])


def Fmk(m, k):
    X = ring(m)
    vals, _ = top_mults(X, 3)
    D3 = math.sqrt(vals[2])
    c = math.cos(math.pi / m)
    rho = -c + math.sqrt(c * c - 1 + D3 ** 2)
    P = [-rho * np.array([np.cos(2 * np.pi * (j + .5) / m), np.sin(2 * np.pi * (j + .5) / m)]) for j in range(k)]
    return np.vstack([X] + ([np.array(P)] if P else []))


def reuleaux(m, per):
    """points on a Reuleaux m-gon (m odd): vertices + `per` points on each arc (symmetric)"""
    V = reg(m)
    D = np.linalg.norm(V[0] - V[(m - 1) // 2])
    pts = [V]
    for j in range(m):
        # arc centred at V[j] between V[j+(m-1)/2] and V[j+(m+1)/2]
        a1 = V[(j + (m - 1) // 2) % m] - V[j]; a2 = V[(j + (m + 1) // 2) % m] - V[j]
        t1, t2 = math.atan2(a1[1], a1[0]), math.atan2(a2[1], a2[0])
        if t2 < t1:
            t2 += 2 * math.pi
        for s in range(1, per + 1):
            t = t1 + (t2 - t1) * s / (per + 1)
            pts.append((V[j] + D * np.array([math.cos(t), math.sin(t)]))[None])
    return np.vstack(pts)


def starts():
    S = {}
    for m in (7, 9, 11, 13):
        S[f'ring{m}'] = ring(m)
        S[f'F{m},{(m-1)//2}'] = Fmk(m, (m - 1) // 2)
        S[f'reg{m}'] = reg(m)
    for m in (8, 10, 12):
        S[f'ring{m}'] = ring(m)
    S['reu5_2'] = reuleaux(5, 2); S['reu7_1'] = reuleaux(7, 1)
    S['reg7+reg21'] = np.vstack([reg(7), reg(21, 0.8, 0.1)])
    return S


if __name__ == "__main__":
    obj = sys.argv[1]
    names = sys.argv[2].split(',') if len(sys.argv) > 2 else None
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    B = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    S = starts()
    for name, X in S.items():
        if names and name not in names:
            continue
        mu0 = top_mults(X)[1]
        sc, Y = beam(X, obj, steps=steps, B=B)
        mu = top_mults(Y)[1]
        print(f"{obj} {name}: start n={len(X)} mu={mu0} -> best n={len(Y)} mu={mu} "
              f"obj={objectives(mu, len(Y))[obj]:+.1f}  all={ {k: round(v, 1) for k, v in objectives(mu, len(Y)).items()} }", flush=True)
