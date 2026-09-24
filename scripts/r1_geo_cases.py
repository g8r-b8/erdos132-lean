"""r1_geo_cases.py -- exact (integer chord-index) check of the R1 case tree on the known D = m+1 examples.

For P = R_M minus holes (M = n+1 or n+2, n = 2m+1), distances are chord indices min(k, M-k) (distinct indices <=>
distinct lengths).  We compute D(P), the diameters, their short spans in P, and which case of the R1 case tree
(A1 / A2 / B1 / B2) each diameter falls in; we also re-check Altman Lemmas 2 and 3 on the tight larger sides.
Run: python3 r1_geo_cases.py
"""
from itertools import combinations


def analyse(M, holes):
    pts = [v for v in range(M) if v not in holes]
    n = len(pts)
    m = (n - 1) // 2
    ch = lambda a, b: min((a - b) % M, (b - a) % M)
    dist = {}
    for i, j in combinations(range(n), 2):
        dist[(i, j)] = dist[(j, i)] = ch(pts[i], pts[j])
    vals = sorted(set(dist.values()), reverse=True)          # d_1 > d_2 > ... (larger index = longer)
    rank = {v: r + 1 for r, v in enumerate(vals)}
    D = len(vals)
    diam = [(i, j) for i, j in combinations(range(n), 2) if rank[dist[(i, j)]] == 1]
    out = []
    def side(i, j):  # closed side from i forward to j
        k = j - i if j > i else j - i + n
        return [(i + t) % n for t in range(k + 1)]
    def dcount(S):
        return len({dist[(x, y)] for x, y in combinations(S, 2)})
    for (i, j) in diam:
        s1 = (j - i) % n
        sigma = min(s1, n - s1)
        big = side(i, j) if s1 >= n - s1 else side(j, i)
        q = len(big)
        dQ = dcount(big)
        uniq = sum(1 for x, y in combinations(big, 2) if rank[dist[(x, y)]] == 1) == 1
        case = None
        if sigma == m - 1:
            c2, c3 = big[1:], big[:-1]
            u2 = sum(1 for x, y in combinations(c2, 2) if rank[dist[(x, y)]] == 1) == 1
            u3 = sum(1 for x, y in combinations(c3, 2) if rank[dist[(x, y)]] == 1) == 1
            case = "A1" if (u2 and u3) else "A2"
        elif sigma == m:
            case = "B1-type(isolated)" if uniq else "B2-type"
        else:
            case = "SPAN-VIOLATION"
        # Altman lemma checks on the larger side, with the side's own distance ranks
        sv = sorted({dist[(x, y)] for x, y in combinations(big, 2)}, reverse=True)
        e = {v: r + 1 for r, v in enumerate(sv)}
        L = lambda a, b: e[dist[(big[a - 1], big[b - 1])]]
        ok = True
        if uniq and dQ == q - 1:
            for k in range(1, q // 2 + 1):
                ok &= L(k, q - k + 1) == 2 * k - 1
            for k in range(2, (q + 1) // 2 + 1):
                ok &= L(k, q - k + 2) == L(k - 1, q - k + 1) == 2 * k - 2
            lem = "L2" + ("ok" if ok else "FAIL")
        elif dQ == q - 2:
            for k in range(2, q // 2 + 1):
                ok &= L(k, q - k + 1) == 2 * k - 2
            for k in range(2, (q + 1) // 2 + 1):
                ok &= L(k, q - k + 2) == L(k - 1, q - k + 1) == 2 * k - 3
            lem = "L3" + ("ok" if ok else "FAIL")
        else:
            lem = f"slack(D(S)={dQ},|S|={q})"
        out.append(((pts[i], pts[j]), sigma, case, lem))
    return n, m, D, out


def main():
    for n in (9, 11, 13, 15, 17):
        m = (n - 1) // 2
        M = n + 1
        n_, m_, D, out = analyse(M, {0})
        print(f"n={n} R_{M}-1: D={D} (m+1={m+1}) diameters={len(out)} cases={sorted(set(o[2] for o in out))} lemmas={sorted(set(o[3] for o in out))}")
        M = n + 2
        for g in range(1, M // 2 + 1):
            n_, m_, D, out = analyse(M, {0, g})
            if D != m + 1:
                continue
            print(f"n={n} R_{M}-{{0,{g}}}: D={D} diameters={len(out)} cases={sorted(set(o[2] for o in out))} lemmas={sorted(set(o[3] for o in out))}")


if __name__ == "__main__":
    main()
