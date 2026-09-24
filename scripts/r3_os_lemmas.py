"""R3/OS angle, part B: adversarial tests of candidate pyramid lemmas (floating point, sanity only).

 T1  global Lemma 1:  L(i,j) > min(L(i,j-1), L(i+1,j-1)) for all i and 2 <= j <= floor(n/2)   (cyclic, no diameter)
 T2  one-sided row maxima increase:  max row j < max row j+1  (Q = B_0..B_{r+1}, B_0B_{r+1} = diam Q)
 T3  one-sided: every entry of row j+1 exceeds the MAX of row j-? (checked: entry > max of its two children)
Random strictly convex polygons from sorted random vectors (Valtr-style) and near-regular perturbations.
Usage: python3 r3_os_lemmas.py [trials]
"""
import numpy as np, sys
rng = np.random.default_rng(1)
T = int(sys.argv[1]) if len(sys.argv) > 1 else 20000


def rand_convex(n):
    k = rng.integers(3)
    if k == 0:
        v = rng.normal(size=(n, 2))
    elif k == 1:
        v = rng.exponential(size=(n, 2)) * rng.choice([-1, 1], size=(n, 2))
    else:
        th = np.sort(rng.uniform(0, 2*np.pi, n)); r = 1 + rng.normal(0, 0.02, n)
        P = np.c_[r*np.cos(th), r*np.sin(th)]
        c = P.mean(0); o = np.argsort(np.arctan2(P[:, 1]-c[1], P[:, 0]-c[0])); P = P[o]
        return P if is_convex(P) else None
    v -= v.mean(0); v = v[np.argsort(np.arctan2(v[:, 1], v[:, 0]))]
    P = np.cumsum(v, 0)
    return P if is_convex(P) else None


def is_convex(P):
    A, B, C = P, np.roll(P, -1, 0), np.roll(P, -2, 0)
    cr = (B-A)[:, 0]*(C-B)[:, 1] - (B-A)[:, 1]*(C-B)[:, 0]
    return cr.min() > 1e-9 or cr.max() < -1e-9


def L(P, i, j):
    n = len(P); return np.linalg.norm(P[i % n] - P[(i+j) % n])


bad1 = bad2 = bad3 = tot = tot_os = 0
ex1 = ex2 = None
for t in range(T):
    n = int(rng.integers(6, 16)); P = rand_convex(n)
    if P is None: continue
    tot += 1; m = n // 2
    for j in range(2, m+1):
        for i in range(n):
            if not L(P, i, j) > min(L(P, i, j-1), L(P, i+1, j-1)) + 1e-12:
                bad1 += 1; ex1 = ex1 or (n, i, j); break
        else: continue
        break
    # one-sided: take a diameter, larger side
    Dm = np.linalg.norm(P[:, None]-P[None], axis=2); a, b = np.unravel_index(np.argmax(Dm), Dm.shape)
    a, b = min(a, b), max(a, b)
    side1 = list(range(a, b+1)); side2 = list(range(b, n)) + list(range(0, a+1))
    Q = P[side1] if len(side1) >= len(side2) else P[side2]
    q = len(Q); r = q - 2
    if r < 3: continue
    tot_os += 1
    rows = [[np.linalg.norm(Q[s]-Q[s+j]) for s in range(q-j)] for j in range(1, q)]
    mx = [max(x) for x in rows]
    if any(mx[j] >= mx[j+1] for j in range(r-1)):   # rows 1..r (exclude the diameter row)
        bad2 += 1; ex2 = ex2 or (q, np.round(mx, 3))
    for j in range(1, r):
        if any(not rows[j][s] > max(rows[j-1][s], rows[j-1][s+1]) for s in range(q-1-j)):
            bad3 += 1; break
print("polygons", tot, " T1 global Lemma1 violations:", bad1, "example", ex1)
print("one-sided samples", tot_os, " T2 row-max increase violations:", bad2, "example", ex2)
print("  T3 'parent > max(children)' violations:", bad3)
