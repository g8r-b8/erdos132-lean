"""Second referee (REFEREE2_A2.md): exhaustive check of the §7.2 ownership/pairing
bookkeeping of WRITEUP_A2.md, in the abstract combinatorial model it actually uses.

Model (everything the §7.2 counting argument relies on):
  * K-row and D-row: vertices with a partial "right T-neighbour" map that is injective,
    so each row is a disjoint union of directed paths and directed cycles (cycles >= 3).
  * Rungs: a partial matching K-row <-> D-row                                   (R1)
  * (R2)     rung (v0,z0), v1=right(v0), z1=right(z0) exist, v1 matched  => match(v1)=z1
  * (R2-sym) rung (v0,z0), v1=right(v0), z1=right(z0) exist, z1 matched  => match(z1)=v1
  * rhombus = rung (v0,z0) with rung (v1,z1), v1=right(v0), z1=right(z0).  Geometrically
    this forces z0-v0 = z1-v1; three parallel rungs are impossible, so
        mode "resonant":  no two consecutive rhombi (v0->v1->v2 all rhombus-linked)  (R3)
        mode "generic":   no rhombus at all (tau < cos(beta/2))
Claim checked:  #pure T-edges + #rungs <= (4/3)|S| (resonant), <= (5/4)|S| (generic),
exactly (no additive constant), and we also recompute the per-rung charging of the write-up
and assert the claimed per-rung/pair ratios.

We enumerate all row structures up to isomorphism (multisets of path/cycle lengths) with
|K|,|D| <= NMAX and all partial matchings.  Exact Fractions throughout.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
import sys

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5


def partitions_paths_cycles(m):
    """All multisets of components (('P',len) / ('C',len>=3)) with total size m."""
    comps = [('P', L) for L in range(1, m + 1)] + [('C', L) for L in range(3, m + 1)]
    out = []

    def rec(i, rem, cur):
        if rem == 0:
            out.append(list(cur)); return
        if i == len(comps):
            return
        kind, L = comps[i]
        # use comps[i] j times
        j = 0
        while j * L <= rem:
            rec(i + 1, rem - j * L, cur + [comps[i]] * j)
            j += 1
    rec(0, m, [])
    return out


def build_right(struct):
    right = {}
    idx = 0
    for kind, L in struct:
        vs = list(range(idx, idx + L)); idx += L
        for a, b in zip(vs, vs[1:]):
            right[a] = b
        if kind == 'C':
            right[vs[-1]] = vs[0]
    return right, idx


def matchings(nk, nd):
    for k in range(0, min(nk, nd) + 1):
        for ks in combinations(range(nk), k):
            for ds in permutations(range(nd), k):
                yield dict(zip(ks, ds))


def check(struct_k, struct_d, mode, stats):
    rK, nk = build_right(struct_k)
    rD, nd = build_right(struct_d)
    tedges = len(rK) + len(rD)
    leftK = {b: a for a, b in rK.items()}
    for M in matchings(nk, nd):
        Minv = {z: v for v, z in M.items()}
        ok = True
        rhomb = set()
        for v0, z0 in M.items():
            v1, z1 = rK.get(v0), rD.get(z0)
            if v1 is None or z1 is None:
                continue
            if v1 in M and M[v1] != z1: ok = False; break          # R2
            if z1 in Minv and Minv[z1] != v1: ok = False; break    # R2-sym
            if M.get(v1) == z1:
                rhomb.add(v0)
        if not ok:
            continue
        if mode == 'generic' and rhomb:
            continue
        if mode == 'resonant' and any(rK.get(v) in rhomb for v in rhomb):
            continue   # two consecutive rhombi = three parallel rungs
        E = tedges + len(M)
        V = nk + nd
        bound = F(4, 3) if mode == 'resonant' else F(5, 4)
        r = F(E, V)
        stats['n'] += 1
        if r > stats['max']:
            stats['max'] = r; stats['arg'] = (struct_k, struct_d, M)
        assert E <= bound * V, ("VIOLATION", mode, struct_k, struct_d, M, E, V)
        # --- recompute the write-up's charging and check per-rung claims ---
        owner = {}
        gap = {}
        for v, z in M.items():
            def walk(start, right, matched):
                x, k = start, 1
                owner[('K' if right is rK else 'D', start)] = v
                while True:
                    nx = right.get(x)
                    if nx is None:
                        return k, False
                    if nx in matched:
                        return k, True
                    x = nx; k += 1
                    owner[('K' if right is rK else 'D', x)] = v
            k, rk = walk(v, rK, M)
            d, rd = walk(z, rD, Minv)
            e = 1 + k + d - (not rk) - (not rd)
            if rk and rd:
                assert (k, d) == (1, 1) or (k >= 2 and d >= 2), ("gap claim fails", k, d)
            gap[v] = (k, d, e, rk and rd)
        # pairing: rhombus rung -> successor, successor not rhombus, injective
        total_owned = sum(g[0] + g[1] for g in gap.values())
        unowned_edges = 0
        for side, right, n in (('K', rK, nk), ('D', rD, nd)):
            for x in range(n):
                if (side, x) not in owner and x in right:
                    unowned_edges += 1
        assert unowned_edges + sum(g[2] for g in gap.values()) == E
        used = set()
        charged = F(0)
        for v, (k, d, e, br) in gap.items():
            if (k, d) == (1, 1) and br:
                v1 = rK[v]
                assert v1 in M and not (gap[v1][:2] == (1, 1) and gap[v1][3]), "successor is rhombus"
                assert v1 not in used
                used.add(v1)
                k1, d1, e1, _ = gap[v1]
                assert F(e + e1, 2 + k1 + d1) <= F(4, 3)
        for v, (k, d, e, br) in gap.items():
            if v in used or ((k, d) == (1, 1) and br):
                continue
            assert F(e, k + d) <= F(5, 4)


for mode in ('generic', 'resonant'):
    stats = {'n': 0, 'max': F(0), 'arg': None}
    for nk in range(1, NMAX + 1):
        for nd in range(1, NMAX + 1):
            for sk in partitions_paths_cycles(nk):
                for sd in partitions_paths_cycles(nd):
                    check(sk, sd, mode, stats)
    print(f"mode={mode}: {stats['n']} admissible configurations, max e/|S| = {stats['max']} "
          f"(= {float(stats['max']):.4f}) at {stats['arg']}")
print("all assertions passed")
