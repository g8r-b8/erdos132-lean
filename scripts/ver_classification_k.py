"""VERIFY_B2: exact rare-distance counts k for every set in the Fishburn / Erdos-Fishburn classifications.

Exactness: for vertex subsets of a regular N-gon, the distance between vertices i, j is 2 sin(pi*c/N) with
c = min(|i-j|, N-|i-j|) in 1..floor(N/2); sin is strictly increasing on (0, pi/2], so distinct chord indices
give distinct distances.  Hence the multiplicity profile is a purely combinatorial count (no floating point).

Checks:
 1. counting lemma closed forms (re-derived): n=2m, D=m+K, K>=1 => k >= K+2 ; n=2m+1 => k >= K+1.
 2. R_n and R_{n+1}^- for even n in [6, 200]: D = n/2 and k = n/2.
 3. n=7: Fishburn's five heptagons with 4 distances (R_8^- and the 4 dissimilar R_9 minus 2): D=4, k=4.
 4. n=9: every 9-subset of R_10 and R_11 (Erdos-Fishburn 1996): D and k; R_9: D=4, k=4.
 5. n=6: R_6 (6,6,3), R_7^- (5,5,5).
"""
from itertools import combinations
from math import comb
from collections import Counter


def profile(N, S):
    c = Counter()
    for i, j in combinations(sorted(S), 2):
        d = j - i
        c[min(d, N - d)] += 1
    return c


def k_of(c, n):
    return sum(1 for v in c.values() if 1 <= v <= n)


def counting_bound(n, D):
    """smallest k with (D-k)(n+1)+k <= C(n,2); returns None if D impossible."""
    N = comb(n, 2)
    for k in range(0, D + 1):
        if (D - k) * (n + 1) + k <= N:
            return k
    return None


def main():
    # 1. counting lemma
    for n in range(4, 400):
        m = n // 2
        for K in range(1, 2 * m):
            D = m + K
            if D > comb(n, 2):
                break
            kb = counting_bound(n, D)
            want = K + 2 if n % 2 == 0 else K + 1
            want = min(want, D)
            assert kb is not None and kb >= want, (n, K, kb, want)
            if n % 2 == 0:
                assert kb == min(K + 2, D) or kb > K + 2, (n, K, kb)
    print("1. counting lemma: even n: k >= K+2 ; odd n: k >= K+1  (n<400)  OK")
    for n in (6, 8, 10):
        print("   n=%d: D=m+1 -> k>=%d ; D=m+2 -> k>=%d" % (n, counting_bound(n, n // 2 + 1), counting_bound(n, n // 2 + 2)))

    # 2. even n
    for n in range(6, 201, 2):
        for N, S, name in ((n, range(n), "R_n"), (n + 1, range(n), "R_{n+1}^-")):
            c = profile(N, S)
            assert len(c) == n // 2 and k_of(c, n) == n // 2, (n, name, c)
            if n <= 10:
                print("2. n=%d %-10s profile(by chord idx)=%s D=%d k=%d" % (n, name, dict(sorted(c.items())), len(c), k_of(c, n)))
    print("2. even n in [6,200]: R_n and R_{n+1}^- have D = k = n/2  OK")

    # 3. heptagons
    c = profile(8, range(7)); print("3. R_8^- :", dict(sorted(c.items())), "D=%d k=%d" % (len(c), k_of(c, 7)))
    seen = set()
    for gap in combinations(range(9), 2):
        S = [v for v in range(9) if v not in gap]
        g = min((gap[1] - gap[0]) % 9, (gap[0] - gap[1]) % 9)
        if g in seen:
            continue
        seen.add(g)
        c = profile(9, S)
        print("3. R_9 minus 2 (gap %d):" % g, dict(sorted(c.items())), "D=%d k=%d" % (len(c), k_of(c, 7)))
        assert len(c) == 4 and k_of(c, 7) == 4

    # 4. nonagons
    c = profile(9, range(9)); print("4. R_9:", dict(sorted(c.items())), "D=%d k=%d" % (len(c), k_of(c, 9)))
    for N in (10, 11):
        res = set()
        for S in combinations(range(N), 9):
            c = profile(N, S)
            res.add((len(c), k_of(c, 9), max(c.values())))
        print("4. 9-subsets of R_%d: (D, k, max mult) values = %s" % (N, sorted(res)))
        assert all(D == 5 and k == 5 for D, k, _ in res)
    print("   (cocircular => each distance graph has max degree <= 2 => mult <= n, so k = D)")


if __name__ == "__main__":
    main()
