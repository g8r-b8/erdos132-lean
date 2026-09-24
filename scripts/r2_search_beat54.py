"""Q1: can non-convex no-4-concyclic sets beat mu(Delta2)/n = 5/4?  Sample combinatorial types
hull = odd Reuleaux m-gon (all offset-k Delta chords), unit chords C from offsets {k-1, k-2},
servers (interior, 2 unit edges) on hull pairs of offset 1 or 2; hull Delta2-degree <= 3; no alternating
4-cycle; counting condition 4*mu2 > 5*n (optionally >= with --ge).  Then realise (SLSQP max slack) and check.
usage: python3 r2_search_beat54.py m samples seed [ge]"""
import sys, math, itertools, json
import numpy as np
from r2_search_common import *
from r2_search_deform import alt4
m, samples, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); ge = len(sys.argv) > 4
k = m // 2; rng = np.random.default_rng(seed)
V = np.array([[math.cos(2*math.pi*i/m), math.sin(2*math.pi*i/m)] for i in range(m)])
s = np.linalg.norm(V[0] - V[k-1]); V /= s; D0 = np.linalg.norm(V[0] - V[k])
E1 = sorted(set(tuple(sorted((i, (i + k) % m))) for i in range(m)))
chords = sorted(set(tuple(sorted((i, (i + o) % m))) for i in range(m) for o in (k - 1, k - 2)))
spairs = sorted(set(tuple(sorted((i, (i + o) % m))) for i in range(m) for o in (1, 2)))
tried = ok = 0; best = None; seen = set()
for it in range(samples):
    # grow C greedily in random order (deg <= 3, alt4-free) up to a random target size >= k+1
    deg = np.zeros(m, int); C = []; target = rng.integers(k + 1, m + 1)
    for q in rng.permutation(len(chords)):
        a, b = chords[q]
        if deg[a] < 3 and deg[b] < 3 and not alt4(C + [(a, b)], E1):
            C.append((a, b)); deg[a] += 1; deg[b] += 1
            if len(C) >= target: break
    C = sorted(C)
    S = []
    for pr in rng.permutation(len(spairs)):
        a, b = spairs[pr]
        nbC = lambda v: set(y for x, y in C if x == v) | set(x for x, y in C if y == v)
        if nbC(a) & nbC(b): continue          # a server there collapses onto the common chord-neighbour
        if deg[a] < 3 and deg[b] < 3 and rng.random() < 0.9: S.append((a, b)); deg[a] += 1; deg[b] += 1
    n = m + len(S); mu2 = len(C) + 2 * len(S)
    if not (4 * mu2 > 5 * n or (ge and 4 * mu2 >= 5 * n)): continue
    key = (tuple(C), tuple(sorted(S)))
    if key in seen: continue
    seen.add(key); tried += 1
    pts = list(V); c0 = V.mean(0); E2s = list(C)
    for a, b in S:
        A, B = V[a], V[b]; mid = (A + B) / 2; d = np.linalg.norm(B - A); hg = math.sqrt(max(1 - d*d/4, 1e-4))
        nr = np.array([-(B - A)[1], (B - A)[0]]) / d
        u = min([mid + hg * nr, mid - hg * nr], key=lambda x: np.linalg.norm(x - c0))
        idx = len(pts); pts.append(u); E2s += [(a, idx), (b, idx)]
    X0 = np.array(pts) + rng.normal(0, 0.02, (len(pts), 2))
    r = realise(X0, D0, E2s, E1, cap=0.02, maxiter=300)
    if r is None or r[2] < 1e-4:
        continue
    X, D, sl = r
    for g in range(3): X, D = genericize(X, D, E2s, E1, rng, size=5e-3)
    A = analyse(X, D)
    if valid(A):
        ok += 1
        print(f"VALID m={m} n={A['n']} mu2={A['mu2']} ratio={A['mu2']/A['n']:.4f} t={A['t']} cc={A['cc']:.2e} C={C} S={S}", flush=True)
        json.dump(dict(X=X.tolist(), D=D, E2=A['E2'], E1=A['E1']), open(f"beat54_m{m}_{ok}.json", "w"))
    else:
        Mm = dist_matrix(X) + 9*np.eye(len(X)); i0, j0 = np.unravel_index(Mm.argmin(), Mm.shape)
        nb = lambda v: sorted(set(b for a, b in A['E2'] if a == v) | set(a for a, b in A['E2'] if b == v))
        print(f"  collapse {i0}(nb {nb(i0)}) ~ {j0}(nb {nb(j0)}) m={m}", flush=True)
        print(f"  realised but invalid: slack {sl:.3g} cc={A['cc']:.1e} minsep={A['minsep']:.1e} ratio={mu2/n:.3f}", flush=True)
print(f"m={m}: types passing counting={tried}, valid={ok}")
