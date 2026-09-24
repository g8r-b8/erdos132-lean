"""R3 / AE': global max number of "hits" of a point u off the circle on the vertices of R_N.

u hits vertex z^a (z = e^{2 pi i/N}) if |u - z^a| = c_j = |1 - z^j| for some 1 <= j <= N/2.
Any u with >= 2 hits is an intersection point of two circles C(1, c_i), C(z^b, c_j) (after rotation;
b <= N/2 after reflection).  We enumerate all of them in floating point (tolerance 1e-7, so no
true hit is missed), then CONFIRM the best configurations exactly in Q(z) (sympy, arithmetic mod
Phi_N): from three hits solve w z^a + wb z^{-a} - tau = Y + 1/Y (unknowns w, wb, tau, Cramer), check
wb = conj(w), tau = w*wb - 1 != 0, w != 0, and every claimed hit equation exactly.
(w = conj(u); tau = |u|^2 - 1.)

Usage: python3 r3_cyc_hits.py NMAX [NMIN]
EXACT_MAX is exact: every float candidate with more float-hits than the running exact max is checked.
"""
import sys
import numpy as np
import sympy as sp

TOL = 1e-7


def float_scan(N):
    z = np.exp(2j * np.pi * np.arange(N) / N)
    ch = np.abs(1 - z[1:N // 2 + 1])            # c_1..c_{N/2}, increasing
    best = {}
    pts = []
    for b in range(1, N // 2 + 1):
        p0, p1 = 1.0 + 0j, z[b]
        d = abs(p1 - p0)
        for r0 in ch:
            for r1 in ch:
                if r0 + r1 < d - 1e-12 or abs(r0 - r1) > d + 1e-12:
                    continue
                a = (r0 * r0 - r1 * r1 + d * d) / (2 * d)
                h2 = r0 * r0 - a * a
                h = np.sqrt(max(h2, 0.0))
                e = (p1 - p0) / d
                m = p0 + a * e
                for s in ((1, -1) if h > 1e-12 else (1,)):
                    pts.append(m + s * h * 1j * e)
    U = np.array(pts)
    mod = np.abs(U)
    U = U[(np.abs(mod - 1) > 1e-6) & (mod > 1e-6)]
    parts = []
    for s0 in range(0, len(U), 20000):        # chunked to keep memory small
        D = np.abs(U[s0:s0 + 20000, None] - z[None, :])          # |u - z^a|
        idx = np.searchsorted(ch, D)
        lo = np.abs(D - ch[np.clip(idx - 1, 0, len(ch) - 1)])
        hi = np.abs(D - ch[np.clip(idx, 0, len(ch) - 1)])
        parts.append(np.minimum(lo, hi) < TOL)
    hitmask = np.concatenate(parts) if parts else np.zeros((0, N), bool)
    hits = hitmask.sum(axis=1)
    return U, hits, hitmask, ch, z


def exact_check(N, u, hitmask_row, ch):
    """Return number of exactly confirmed hits (or -1 if the exact solve fails)."""
    x = sp.Symbol('x')
    Phi = sp.Poly(sp.cyclotomic_poly(N, x), x, domain='QQ')

    def red(p):
        return sp.Poly(p, x, domain='QQ').rem(Phi)

    def zp(k):
        return red(x ** (k % N))

    def conj(p):
        # z -> z^{-1}
        s = sp.Poly(0, x, domain='QQ')
        for (k,), c in p.terms():
            s += c * zp(-k)
        return red(s)

    def mul(p, q):
        return red(p * q)

    def inv(p):
        return sp.Poly(sp.invert(p.as_expr(), Phi.as_expr(), x), x, domain='QQ')

    zf = np.exp(2j * np.pi * np.arange(N) / N)
    hitlist = []
    for a in np.nonzero(hitmask_row)[0]:
        dist = abs(u - zf[a])
        j = int(np.argmin(np.abs(ch - dist))) + 1
        hitlist.append((int(a), j))
    if len(hitlist) < 3:
        return len(hitlist)
    def det3(M):
        t = sp.Poly(0, x, domain='QQ')
        for perm, sgn in (((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1),
                          ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)):
            t += sgn * mul(mul(M[0][perm[0]], M[1][perm[1]]), M[2][perm[2]])
        return red(t)
    from itertools import combinations
    for tri in combinations(hitlist, 3):
        rows = [[zp(a), zp(-a), red(-1 + 0 * x), red(x ** j + x ** ((-j) % N))] for (a, j) in tri]
        A = [[r[0], r[1], r[2]] for r in rows]
        rhs = [r[3] for r in rows]
        dA = det3(A)
        if dA.is_zero:
            continue
        di = inv(dA)
        sol = []
        for c in range(3):
            Ac = [[(rhs[i] if k == c else A[i][k]) for k in range(3)] for i in range(3)]
            sol.append(mul(det3(Ac), di))
        w, wb, tau = sol
        ok = (red(wb - conj(w)).is_zero and red(tau - (mul(w, wb) - 1)).is_zero
              and not tau.is_zero and not w.is_zero)
        if not ok:
            continue
        wnum = complex(sum(complex(c) * np.exp(2j * np.pi * k / N) for (k,), c in w.terms()))
        if abs(np.conj(wnum) - u) > 1e-6:
            continue
        cnt = 0
        for (a, j) in hitlist:
            lhs = red(mul(w, zp(a)) + mul(wb, zp(-a)) - tau - zp(j) - zp(-j))
            cnt += lhs.is_zero
        return cnt          # exact hit count of this u (all true hits are in hitlist)
    return 2                # no consistent triple: at most 2 true hits


if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    top = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    overall = []
    for N in range(top if top > 1 else 3, NMAX + 1):
        U, hits, hm, ch, z = float_scan(N)
        if len(U) == 0:
            print(N, 'none'); continue
        mx = int(hits.max())
        order = np.argsort(-hits)
        seen, best, ncheck = set(), 2, 0
        for i in order:
            if hits[i] <= best:
                break
            key = (round(U[i].real, 6), round(U[i].imag, 6))
            if key in seen:
                continue
            seen.add(key)
            ncheck += 1
            best = max(best, exact_check(N, U[i], hm[i], ch))
        print(f"N={N:3d} float_max={mx:2d} EXACT_MAX={best:2d} (exact checks: {ncheck})", flush=True)
        mx = best
        overall.append((mx, N))
    print('GLOBAL', max(overall))
