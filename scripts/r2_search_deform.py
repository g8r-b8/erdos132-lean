"""Idea 1: deform known extremal structures.  Start from a symmetric configuration with many Delta/Delta2
equalities, keep a random SUBSET of them containing no alternating 4-cycle (Lemma T), maximise slack
(all dropped/other pairs < 1 - s), genericise in the kernel, test no-4-concyclic.
usage: python3 r2_search_deform.py <family> <m> <trials> <seed>
families: cdl (even m-gon, antipodal Delta, offset h-1 Delta2, servers on alternate edges),
          odd (odd m-gon, offset k Delta, offset k-1 Delta2, servers on adjacent pairs),
          cdlall (even m-gon, servers on all edges considered)"""
import sys, json, math, itertools, time
import numpy as np
from r2_search_common import *

def build(family, m):
    if family in ('cdl', 'cdlall'):
        h = m // 2
        V = np.array([[math.cos(2*math.pi*i/m), math.sin(2*math.pi*i/m)] for i in range(m)])
        s = np.linalg.norm(V[0] - V[h-1]); V /= s; D = 2 / s
        E1 = [(i, i + h) for i in range(h)]
        E2 = [tuple(sorted((i, (i + h - 1) % m))) for i in range(m)]
        step = 2 if family == 'cdl' else 1
        srv_pairs = [(j, (j + 1) % m) for j in range(0, m, step)]
    else:
        k = m // 2
        V = np.array([[math.cos(2*math.pi*i/m), math.sin(2*math.pi*i/m)] for i in range(m)])
        s = np.linalg.norm(V[0] - V[k-1]); V /= s; D = np.linalg.norm(V[0] - V[k])
        E1 = sorted(set(tuple(sorted((i, (i + k) % m))) for i in range(m)))
        E2 = sorted(set(tuple(sorted((i, (i + k - 1) % m))) for i in range(m)))
        srv_pairs = [(j, (j + 1) % m) for j in range(m)]
    pts = list(V); c = V.mean(0)
    for a, b in srv_pairs:
        A, B = V[a], V[b]; mid = (A + B) / 2; d = np.linalg.norm(B - A); hg = math.sqrt(1 - d * d / 4)
        nr = np.array([-(B - A)[1], (B - A)[0]]) / d
        u = min([mid + hg * nr, mid - hg * nr], key=lambda x: np.linalg.norm(x - c))
        idx = len(pts); pts.append(u); E2 += [tuple(sorted((a, idx))), tuple(sorted((b, idx)))]
    return np.array(pts), D, sorted(set(E2)), sorted(set(E1))

def alt4(E2, E1):
    """alternating 4-cycles a-b (E1), c-d (E1), a-c (E2), b-d (E2)."""
    S2 = set(E2); out = []
    for (a, b), (c, d) in itertools.combinations(E1, 2):
        for (x, y) in ((c, d), (d, c)):
            if len({a, b, x, y}) < 4: continue
            if tuple(sorted((a, x))) in S2 and tuple(sorted((b, y))) in S2: out.append((a, b, x, y))
    return out

def deg_ok(n, E2, E1):
    d2 = [0]*n; d1 = [0]*n
    for i, j in E2: d2[i] += 1; d2[j] += 1
    for i, j in E1: d1[i] += 1; d1[j] += 1
    return max(d2) <= 3 and max(d1) <= 3

def main():
    fam, m, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = np.random.default_rng(seed)
    X0, D0, E2full, E1full = build(fam, m)
    n0 = len(X0)
    print(f"{fam} m={m}: n={n0} mu2={len(E2full)} mu1={len(E1full)} alt4={len(alt4(E2full, E1full))}")
    best = {}; t0 = time.time(); stats = dict(tried=0, realised=0, valid=0, forced_cc=0)
    for tr in range(trials):
        # random subset: drop each E1 edge w.p. p1, each E2 w.p. p2, then fix alt 4-cycles greedily
        p1 = rng.uniform(0, 0.7); p2 = rng.uniform(0, 0.4)
        E1 = [e for e in E1full if rng.random() > p1]
        E2 = [e for e in E2full if rng.random() > p2]
        if not E1: E1 = [E1full[rng.integers(len(E1full))]]
        while True:
            cyc = alt4(E2, E1)
            if not cyc: break
            a, b, x, y = cyc[rng.integers(len(cyc))]
            opts = [('1', tuple(sorted((a, b)))), ('1', tuple(sorted((x, y)))),
                    ('2', tuple(sorted((a, x)))), ('2', tuple(sorted((b, y))))]
            w = np.array([1.0, 1.0, 0.6, 0.6]); w /= w.sum()
            typ, e = opts[rng.choice(4, p=w)]
            if typ == '1' and len(E1) > 1: E1.remove(e)
            elif typ == '2': E2.remove(e)
            else: E2.remove(opts[2][1])
        # optionally drop isolated/useless vertices: vertices with no kept edges
        used = set(itertools.chain(*E2, *E1))
        keep = sorted(used); idx = {v: i for i, v in enumerate(keep)}
        X = X0[keep] + rng.normal(0, rng.choice([1e-3, 1e-2, 3e-2]), (len(keep), 2))
        E2s = [(idx[a], idx[b]) for a, b in E2]; E1s = [(idx[a], idx[b]) for a, b in E1]
        n = len(keep); exc = len(E2s) - n
        stats['tried'] += 1
        if exc < 1: continue
        r = realise(X, D0, E2s, E1s)
        if r is None: continue
        X, D, s = r
        stats.setdefault("s_by_exc", {}).setdefault(exc, []).append(round(s, 4))
        if s < 1e-4: continue
        stats['realised'] += 1
        for g in range(3):
            X, D = genericize(X, D, E2s, E1s, rng, size=1e-2)
        A = analyse(X, D)
        if not (A['maxother'] < 1 - 1e-5 and A['D'] > 1 + 1e-5 and A['mu1'] >= 1): continue
        if A['cc'] < 1e-7:
            stats['forced_cc'] += 1; continue
        stats['valid'] += 1
        key = A['n']
        if (A['exc'], A['t']) > best.get(key, ((-99, -99), None))[0]:
            best[key] = ((A['exc'], A['t']), dict(X=X.tolist(), D=D, E2=A['E2'], E1=A['E1'], cc=A['cc'],
                                                   slack=1 - A['maxother']))
            print(f"  tr{tr} n={A['n']} exc={A['exc']} t={A['t']} mu1={A['mu1']} cc={A['cc']:.2e} "
                  f"slack={1-A['maxother']:.2e} D={D:.5f}", flush=True)
    print("stats", stats, f"time {time.time()-t0:.0f}s")
    for k in sorted(best): print(" best n", k, best[k][0])
    json.dump({str(k): v[1] for k, v in best.items()},
              open(f"deform_{fam}_m{m}_s{seed}.json", "w"))

if __name__ == '__main__':
    main()
