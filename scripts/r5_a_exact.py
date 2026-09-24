"""R5/A: exact arithmetic for point sets in a tower Q(zeta_N)(sqrt rho_1)(sqrt rho_2)...

Run with the repo venv (needs mpmath only):  .venv/bin/python problems/132/scripts/r5_a_exact.py <recipe.json>

Representation
  * base field K0 = Q(zeta_N), 4 | N (so i = zeta_N^(N/4) is available); elements are tuples of
    Fractions in the power basis 1, z, ..., z^(phi-1) reduced mod Phi_N.
  * tower element = dict {mask: base-vector}, meaning sum_mask c_mask * prod_{k in mask} sqrt(rho_k),
    where every radicand rho_k is a REAL, POSITIVE element of the lower tower (checked exactly for
    realness: conj(rho) == rho canonically; numerically for positivity).  sqrt(rho_k) is the positive
    real root.  Complex conjugation acts on the base only (fixes every sqrt(rho_k)).
  * Soundness: if the canonical form of x - y is empty then x == y (sufficient condition; if the tower
    were degenerate some equal numbers might not be recognised -- the checker then reports
    "numerically equal but NOT proven" instead of silently merging).
  * Distinct classes are separated numerically at 60 significant digits (reported gap).

Recipe ops (also produced by r5_a_search.py, whose float replay uses identical conventions):
  ["poly", m, r_idx_or_null]   add the regular m-gon zeta_m^t (t=0..m-1)   (radius 1)
  ["cc", i, j, [a,b], [c,d], s] add p_i + A (p_j-p_i) + s*i*(p_j-p_i)*sqrt(H) with
                               R1=|p_a-p_b|^2, R2=|p_c-p_d|^2, d2=|p_j-p_i|^2, A=(R1-R2+d2)/(2 d2),
                               H = R1/d2 - A^2   (intersection of circle(p_i, sqrt R1), circle(p_j, sqrt R2))
  ["rot", i, k]                add zeta_N^k * p_i
  ["orbit", i, m]              add zeta_m^t * p_i for t = 1..m-1
  ["conj", i]                  add conj(p_i)
  ["origin"]                   add 0
  ["cyc", [a1, a2, ...]]       add zeta_N^a1 + zeta_N^a2 + ...
"""
from __future__ import annotations
import json, sys
from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60


def cyclotomic_poly(N):
    """Integer coefficients (low -> high) of Phi_N, by exact division of x^N - 1."""
    def pdiv(a, b):  # exact division of integer polys, low->high
        a = a[:]; q = [0] * (len(a) - len(b) + 1)
        for k in range(len(q) - 1, -1, -1):
            c = a[k + len(b) - 1] // b[-1]; q[k] = c
            for t in range(len(b)):
                a[k + t] -= c * b[t]
        assert all(v == 0 for v in a[:len(b) - 1])
        return q
    p = [-1] + [0] * (N - 1) + [1]
    for d in range(1, N):
        if N % d == 0:
            p = pdiv(p, cyclotomic_poly(d))
    return p


class Tower:
    def __init__(self, N):
        assert N % 4 == 0, "need 4 | N so that i is in the base field"
        self.N = N
        self.phi_poly = cyclotomic_poly(N)
        self.phi = len(self.phi_poly) - 1
        # reduction table: x^k for 0 <= k < 2N as base vectors
        self.red = []
        v = [Fraction(0)] * self.phi; v[0] = Fraction(1)
        for k in range(2 * N):
            self.red.append(tuple(v))
            # multiply v by x
            top = v[-1]
            w = [Fraction(0)] + v[:-1]
            if top:
                for t in range(self.phi):
                    w[t] -= top * self.phi_poly[t]
            v = w
        self.zeta_num = mp.exp(2j * mp.pi / N)
        self.rad = []       # radicands (tower elements)
        self.rad_num = []   # numeric positive sqrt values
        self.zero = {}

    # ---------- base field ----------
    def bmul(self, a, b):
        prod = [Fraction(0)] * (2 * self.phi - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        prod[i + j] += x * y
        out = [Fraction(0)] * self.phi
        for k, c in enumerate(prod):
            if c:
                r = self.red[k]
                for t in range(self.phi):
                    if r[t]:
                        out[t] += c * r[t]
        return tuple(out)

    def bconj(self, a):
        out = [Fraction(0)] * self.phi
        for k, c in enumerate(a):
            if c:
                r = self.red[(self.N - k) % self.N]
                for t in range(self.phi):
                    if r[t]:
                        out[t] += c * r[t]
        return tuple(out)

    def binv(self, a):
        """Solve a*x = 1 in Q(zeta_N) by Gaussian elimination on the multiplication matrix."""
        n = self.phi
        cols = []
        for k in range(n):
            e = [Fraction(0)] * n; e[k] = Fraction(1)
            cols.append(self.bmul(a, tuple(e)))
        M = [[cols[k][r] for k in range(n)] + [Fraction(1 if r == 0 else 0)] for r in range(n)]
        for c in range(n):
            piv = next(r for r in range(c, n) if M[r][c] != 0)
            M[c], M[piv] = M[piv], M[c]
            inv = 1 / M[c][c]
            M[c] = [x * inv for x in M[c]]
            for r in range(n):
                if r != c and M[r][c] != 0:
                    f = M[r][c]
                    M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        return tuple(M[r][n] for r in range(n))

    def bnum(self, a):
        return mp.fsum(c * self.zeta_num ** k for k, c in enumerate(a) if c) if any(a) else mp.mpc(0)

    # ---------- tower ----------
    def const(self, q):
        q = Fraction(q)
        if q == 0:
            return {}
        v = [Fraction(0)] * self.phi; v[0] = q
        return {0: tuple(v)}

    def zeta(self, k):
        return {0: self.red[k % self.N]}

    def _addto(self, acc, mask, vec):
        if mask in acc:
            s = tuple(x + y for x, y in zip(acc[mask], vec))
            if any(s):
                acc[mask] = s
            else:
                del acc[mask]
        elif any(vec):
            acc[mask] = vec

    def add(self, x, y):
        out = dict(x)
        for m, v in y.items():
            self._addto(out, m, v)
        return out

    def neg(self, x):
        return {m: tuple(-c for c in v) for m, v in x.items()}

    def sub(self, x, y):
        return self.add(x, self.neg(y))

    def scale(self, x, q):
        q = Fraction(q)
        return {m: tuple(c * q for c in v) for m, v in x.items()} if q else {}

    def mul(self, x, y):
        out = {}
        for m1, v1 in x.items():
            for m2, v2 in y.items():
                c = self.bmul(v1, v2)
                if not any(c):
                    continue
                common = m1 & m2
                term = {m1 ^ m2: c}
                k = 0
                while common:
                    if common & 1:
                        term = self.mul(term, self.rad[k])
                    common >>= 1; k += 1
                for m, v in term.items():
                    self._addto(out, m, v)
        return out

    def conj(self, x):
        return {m: self.bconj(v) for m, v in x.items()}

    def inv(self, x):
        assert x, "division by zero"
        top = max(x.keys())
        if top == 0:
            return {0: self.binv(x[0])}
        k = top.bit_length() - 1
        bit = 1 << k
        a = {m: v for m, v in x.items() if not m & bit}
        b = {m ^ bit: v for m, v in x.items() if m & bit}
        # x = a + b sqrt(rho_k);  1/x = (a - b sqrt rho) / (a^2 - b^2 rho)
        den = self.sub(self.mul(a, a), self.mul(self.mul(b, b), self.rad[k]))
        num = self.sub(a, {m | bit: v for m, v in b.items()})
        return self.mul(num, self.inv(den))

    def num(self, x):
        s = mp.mpc(0)
        for m, v in x.items():
            t = self.bnum(v); k = 0; mm = m
            while mm:
                if mm & 1:
                    t *= self.rad_num[k]
                mm >>= 1; k += 1
            s += t
        return s

    def sqrt_real(self, rho):
        """Positive square root of a real positive tower element (new radical unless already known)."""
        assert not self.sub(rho, self.conj(rho)), "radicand not provably real"
        val = self.num(rho)
        assert abs(val.imag) < mp.mpf(10) ** -40 and val.real > 0, f"radicand not positive: {val}"
        if not rho:
            return {}
        for k, r in enumerate(self.rad):
            if not self.sub(rho, r):
                return {1 << k: self.red[0]}
        # perfect square of a rational? (cheap special case)
        if list(rho.keys()) == [0] and not any(rho[0][1:]):
            q = rho[0][0]
            from math import isqrt
            if q.numerator >= 0 and isqrt(q.numerator) ** 2 == q.numerator and isqrt(q.denominator) ** 2 == q.denominator:
                return self.const(Fraction(isqrt(q.numerator), isqrt(q.denominator)))
        c = self._sqrt_in_tower(rho, val.real)
        if c is not None:
            return c
        self.rad.append(rho)
        self.rad_num.append(mp.sqrt(val.real))
        return {1 << (len(self.rad) - 1): self.red[0]}

    def _sqrt_in_tower(self, rho, val):
        """Try to find c in the REAL subtower with c^2 = rho (PSLQ guess, then exact proof c*c == rho).
        Real subtower basis: (zeta^k + zeta^-k) * prod sqrt(rho_S), k = 0..phi/2-1 (plus 1)."""
        basis = []
        half = self.phi // 2
        for mask in range(1 << len(self.rad)):
            for k in range(half):
                e = self.add(self.zeta(k), self.zeta(-k)) if k else self.const(1)
                e = {mask: e[0]} if mask else e
                basis.append(e)
        if len(basis) > 64:
            return None
        with mp.workdps(120):
            h = mp.sqrt(mp.mpf(val))
            # recompute numerics at higher precision
            zn = mp.exp(2j * mp.pi / self.N)
            rn = []
            for r in self.rad:
                rn.append(None)
            def num_hp(x):
                s = mp.mpc(0)
                for m, v in x.items():
                    t = mp.fsum(c * zn ** k for k, c in enumerate(v) if c); kk = 0; mm = m
                    while mm:
                        if mm & 1:
                            if rn[kk] is None:
                                rn[kk] = mp.sqrt(num_hp(self.rad[kk]).real)
                            t *= rn[kk]
                        mm >>= 1; kk += 1
                    s += t
                return s
            h = mp.sqrt(num_hp(rho).real)
            vec = [h] + [num_hp(b).real for b in basis]
            try:
                rel = mp.pslq(vec, maxcoeff=10 ** 8, maxsteps=10 ** 5)
            except Exception:
                rel = None
        if not rel or rel[0] == 0:
            return None
        c = {}
        for coef, b in zip(rel[1:], basis):
            if coef:
                c = self.add(c, self.scale(b, Fraction(-coef, rel[0])))
        if self.sub(self.mul(c, c), rho):
            return None
        if self.num(c).real < 0:
            c = self.neg(c)
        return c

    def abs2(self, x):
        return self.mul(x, self.conj(x))


def build(recipe, T=None, verbose=False):
    """Replay a recipe exactly. Returns (tower, list of points)."""
    N = recipe["N"]
    T = T or Tower(N)
    P = []
    I = T.zeta(N // 4)
    for op in recipe["ops"]:
        kind = op[0]
        if kind == "poly":
            m = op[1]; assert N % m == 0
            for t in range(m):
                P.append(T.zeta(t * (N // m)))
        elif kind == "origin":
            P.append({})
        elif kind == "cyc":
            acc = {}
            for a in op[1]:
                acc = T.add(acc, T.zeta(a))
            P.append(acc)
        elif kind == "rot":
            P.append(T.mul(T.zeta(op[2]), P[op[1]]))
        elif kind == "conj":
            P.append(T.conj(P[op[1]]))
        elif kind == "orbit":
            i, m = op[1], op[2]; assert N % m == 0
            base = P[i]
            for t in range(1, m):
                P.append(T.mul(T.zeta(t * (N // m)), base))
        elif kind == "cc":
            _, i, j, (a, b), (c, d), s = op
            R1 = T.abs2(T.sub(P[a], P[b])); R2 = T.abs2(T.sub(P[c], P[d]))
            v = T.sub(P[j], P[i]); d2 = T.abs2(v); id2 = T.inv(d2)
            A = T.mul(T.add(T.sub(R1, R2), d2), T.scale(id2, Fraction(1, 2)))
            H = T.sub(T.mul(R1, id2), T.mul(A, A))
            base = T.add(P[i], T.mul(A, v))
            if not H:
                P.append(base)
                continue
            # numeric target
            Hn = T.num(H).real
            tgt = T.num(base) + s * 1j * T.num(v) * mp.sqrt(Hn)
            # avoid tower degeneracy: if the target is a rotation / reflection of an existing point,
            # use that exact form after PROVING it lies on both circles (<= 2 intersection points,
            # the right one is picked numerically).
            found = None
            for t, Q in enumerate(P):
                qn = T.num(Q)
                for refl in (False, True):
                    qq = mp.conj(qn) if refl else qn
                    if abs(abs(qq) - abs(tgt)) > mp.mpf(10) ** -30:
                        continue
                    for k in range(N):
                        if abs(T.zeta_num ** k * qq - tgt) < mp.mpf(10) ** -40:
                            cand = T.mul(T.zeta(k), T.conj(Q) if refl else Q)
                            if not T.sub(T.abs2(T.sub(cand, P[i])), R1) and not T.sub(T.abs2(T.sub(cand, P[j])), R2):
                                found = cand
                            break
                    if found is not None:
                        break
                if found is not None:
                    break
            if found is not None:
                P.append(found)
            else:
                h = T.sqrt_real(H)
                P.append(T.add(base, T.scale(T.mul(T.mul(I, v), h), s)))
        else:
            raise ValueError(op)
        if verbose:
            print(" op", op, "->", len(P), "points; radicals:", len(T.rad), flush=True)
    return T, P


def exact_profile(T, P, tol_exp=-40):
    """All squared distances; classes grouped numerically, equality inside a class proven exactly.
    Returns list of (value_float, multiplicity, proven_flag) in DECREASING order, plus min gap."""
    n = len(P)
    items = []
    for i in range(n):
        for j in range(i + 1, n):
            e = T.abs2(T.sub(P[i], P[j]))
            items.append((T.num(e).real, e, (i, j)))
    # distinct points
    assert all(v > mp.mpf(10) ** tol_exp for v, _, _ in items), "coincident points"
    items.sort(key=lambda t: t[0], reverse=True)
    classes = []
    for v, e, pr in items:
        if classes and abs(classes[-1]["v"] - v) < mp.mpf(10) ** tol_exp:
            c = classes[-1]
            if T.sub(e, c["rep"]):
                c["proven"] = False
            c["mult"] += 1; c["pairs"].append(pr)
        else:
            classes.append({"v": v, "rep": e, "mult": 1, "proven": True, "pairs": [pr]})
    gaps = [classes[k]["v"] - classes[k + 1]["v"] for k in range(len(classes) - 1)]
    return classes, (min(gaps) if gaps else None)


def report(recipe, name=""):
    T, P = build(recipe)
    classes, gap = exact_profile(T, P)
    n = len(P)
    mults = [c["mult"] for c in classes]
    allproven = all(c["proven"] for c in classes)
    rare = [k + 1 for k in range(1, len(mults)) if mults[k] <= n]   # 1-based index j >= 2
    print(f"[{name}] n={n} D={len(mults)} radicals={len(T.rad)} all-classes-proven={allproven} "
          f"min-gap(sq.dist)={mp.nstr(gap, 5)}")
    print(f"   mults (decreasing distance) = {mults}")
    print(f"   sq-dist values = {[mp.nstr(c['v'], 12) for c in classes[:8]]} ...")
    print(f"   rare non-diam indices j (mu_j <= n): {rare[:6]}{'...' if len(rare) > 6 else ''}  s'={len(rare)}  "
          f"mu(delta)={mults[-1]}")
    for J in range(3, 7):
        if len(mults) >= J:
            print(f"   J={J}: min_(2<=j<=J) mu_j - n = {min(mults[1:J]) - n}")
    return n, mults, allproven, gap


if __name__ == "__main__":
    for path in sys.argv[1:]:
        with open(path) as f:
            data = json.load(f)
        recs = data if isinstance(data, list) else [data]
        for r in recs:
            report(r, r.get("name", path))
