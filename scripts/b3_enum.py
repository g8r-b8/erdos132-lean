"""Angle B3, step 1: combinatorial enumeration of candidate distance-colourings of a strictly convex n-gon.

Vertices 0..n-1 in convex cyclic order.  Each of the C(n,2) pairs gets a colour 1..D (1 = smallest distance,
D = diameter).  We keep only colourings satisfying the elementary necessary conditions (proved in angle_B3.md):

  (T) triangle rigidity: for a pair {i,j} and two vertices w != w' on the same open arc of the polygon cut by i,j
      (hence strictly on the same side of line ij), (c(iw),c(jw)) != (c(iw'),c(jw')).
  (Q) quadrilateral inequality: for i<j<k<l, |ik|+|jl| > |ij|+|kl| and > |jk|+|li|.  Ordinal form: the sorted
      diagonal colours are NOT dominated coordinatewise by the sorted colours of either pair of opposite sides.
  (X) diameter segments pairwise intersect: two vertex-disjoint colour-D pairs must cross (interleave cyclically).
  (count) at least F classes have size >= n+1 and all D colours occur.

Usage: b3_enum.py n D [F] [noT]   -- colourings with >= F colour classes of size >= n+1 (default F = D-2, i.e. k <= 2)
Outputs canonical (dihedral-reduced) colourings as strings, one per line, to stdout; summary to stderr.
"""
import sys, itertools

def setup(n, use_T=True):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    idx = {p: t for t, p in enumerate(pairs)}
    def e(i, j):
        return idx[(i, j) if i < j else (j, i)]
    # order edges: by cyclic length then position -> sides first
    order = sorted(range(len(pairs)), key=lambda t: (min(pairs[t][1] - pairs[t][0], n - pairs[t][1] + pairs[t][0]), pairs[t]))
    pos = {t: s for s, t in enumerate(order)}
    cons = [[] for _ in pairs]  # constraints keyed by the step at which they become fully assigned
    # (T)
    for i, j in (pairs if use_T else []):
        arc1 = list(range(i + 1, j)); arc2 = [w for w in range(n) if w not in arc1 and w not in (i, j)]
        for arc in (arc1, arc2):
            for w, w2 in itertools.combinations(arc, 2):
                es = (e(i, w), e(j, w), e(i, w2), e(j, w2))
                cons[max(pos[x] for x in es)].append(('T', es))
    # (Q)
    for i, j, k, l in itertools.combinations(range(n), 4):
        d = (e(i, k), e(j, l))
        for s in ((e(i, j), e(k, l)), (e(j, k), e(i, l))):
            es = d + s
            cons[max(pos[x] for x in es)].append(('Q', es))
    # (X) disjoint non-crossing pairs
    for (i, j), (k, l) in itertools.combinations(pairs, 2):
        if len({i, j, k, l}) < 4:
            continue
        cross = (i < k < j) != (i < l < j)
        if not cross:
            es = (e(i, j), e(k, l))
            cons[max(pos[x] for x in es)].append(('X', es))
    return pairs, e, order, cons

def ok(con, c, D):
    t, es = con
    if t == 'T':
        a, b, a2, b2 = (c[x] for x in es)
        return not (a == a2 and b == b2)
    if t == 'Q':
        x = sorted((c[es[0]], c[es[1]])); y = sorted((c[es[2]], c[es[3]]))
        return not (x[0] <= y[0] and x[1] <= y[1])
    if t == 'X':
        return not (c[es[0]] == D and c[es[1]] == D)

def dihedral_images(n, pairs, e, col):
    out = []
    for r in range(n):
        for s in (1, -1):
            m = lambda v: (s * v + r) % n
            out.append(tuple(col[e(m(i), m(j))] for i, j in pairs))
    return out

def enumerate_colourings(n, D, profile_ok, profile_prune, use_T=True):
    pairs, e, order, cons = setup(n, use_T)
    N = len(pairs)
    c = [0] * N
    cnt = [0] * (D + 1)
    seen = set(); res = []
    stats = [0]
    def rec(step):
        stats[0] += 1
        if step == N:
            if profile_ok(cnt):
                key = min(dihedral_images(n, pairs, e, c))
                if key not in seen:
                    seen.add(key); res.append(key)
            return
        t = order[step]
        for col in range(1, D + 1):
            c[t] = col; cnt[col] += 1
            if profile_prune(cnt, N - step - 1) and all(ok(k, c, D) for k in cons[step]):
                rec(step + 1)
            cnt[col] -= 1
        c[t] = 0
    rec(0)
    return pairs, res, stats[0]

def profile_generic(n, D, F):
    """k <= D - F with F classes of multiplicity >= n+1 ('frequent'); every colour used at least once.
    No assumption about which colour is frequent (Hopf-Pannwitz is NOT assumed)."""
    T = n + 1
    def okf(cnt):
        return sum(1 for x in range(1, D + 1) if cnt[x] >= T) >= F and all(cnt[x] >= 1 for x in range(1, D + 1))
    def prune(cnt, rem):
        s = sorted(cnt[1:], reverse=True)
        need = sum(max(0, T - v) for v in s[:F]) + sum(1 for v in s[F:] if v == 0)
        return need <= rem
    return okf, prune

if __name__ == '__main__':
    n = int(sys.argv[1]); D = int(sys.argv[2]); F = int(sys.argv[3]) if len(sys.argv) > 3 else D - 2
    use_T = not (len(sys.argv) > 4 and sys.argv[4] == 'noT')   # ablation: drop (T), keep (Q),(X)
    okf, prune = profile_generic(n, D, F)
    pairs, res, nodes = enumerate_colourings(n, D, okf, prune, use_T)
    print(f"n={n} D={D} F={F} use_T={use_T}: {len(res)} canonical colourings, {nodes} search nodes", file=sys.stderr)
    for r in res:
        print(''.join(map(str, r)))
