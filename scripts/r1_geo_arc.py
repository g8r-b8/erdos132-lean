"""r1_geo_arc.py -- sanity check of the Arc Rigidity Lemma (R1, route A).

Lemma R.  Let M in {2m+2, 2m+3}, let V be s consecutive vertices of the regular M-gon R_M on the circle G,
and let w be a point such that V u {w} is strictly convex with w inserted between the last and the first
vertex of V.  If every distance |w v| (v in V) is a chord length of R_M, and s >= m+2, then w lies on G
(hence is a vertex of R_M).

Check: every such w has chord distance to v_0 and v_1, so w is one of the <= 2 intersection points of two
circles with chord radii.  We enumerate all chord pairs, keep the intersection on the inner side of line
v_0 v_1, and test the remaining conditions with mpmath at 60 digits (sanity check only; the proof is in the
report).  We also report the off-circle w that exist for s = m+1 (sharpness).
Run:  uv run --with mpmath python r1_geo_arc.py
"""
import sys
from mpmath import mp, mpf, cos, sin, pi, sqrt

mp.dps = 60
TOL = mpf(10) ** -40


def run(M, s):
    P = [(cos(2 * pi * k / M), sin(2 * pi * k / M)) for k in range(M)]
    V = P[:s]
    chords = sorted({2 * sin(pi * j / M) for j in range(1, M // 2 + 1)})
    def d(a, b):
        return sqrt((a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2)
    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    found = []
    v0, v1 = V[0], V[1]
    L = d(v0, v1)
    for r0 in chords:
        for r1 in chords:
            # circle-circle intersection
            a = (r0 ** 2 - r1 ** 2 + L ** 2) / (2 * L)
            h2 = r0 ** 2 - a ** 2
            if h2 <= 0:
                continue
            h = sqrt(h2)
            ex = ((v1[0] - v0[0]) / L, (v1[1] - v0[1]) / L)
            base = (v0[0] + a * ex[0], v0[1] + a * ex[1])
            for sg in (1, -1):
                w = (base[0] - sg * h * ex[1], base[1] + sg * h * ex[0])
                # all distances to V must be chords
                if not all(min(abs(d(w, v) - c) for c in chords) < TOL for v in V):
                    continue
                # strict convexity of polygon v_0..v_{s-1}, w (counterclockwise)
                poly = V + [w]
                k = len(poly)
                if not all(cross(poly[i], poly[(i + 1) % k], poly[(i + 2) % k]) > TOL for i in range(k)):
                    continue
                onG = abs(w[0] ** 2 + w[1] ** 2 - 1) < TOL
                found.append((onG, float(w[0]), float(w[1])))
    uniq = []
    for f in found:
        if not any(abs(f[1] - g[1]) < 1e-20 and abs(f[2] - g[2]) < 1e-20 for g in uniq):
            uniq.append(f)
    return uniq


def main():
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    bad = 0
    for m in range(2, mmax + 1):
        for M in (2 * m + 2, 2 * m + 3):
            for s in (m + 1, m + 2):
                res = run(M, s)
                off = [r for r in res if not r[0]]
                tag = "LEMMA" if s >= m + 2 else "sharp?"
                print(f"m={m} M={M} s={s} [{tag}] candidates={len(res)} off-circle={len(off)}"
                      + (f" e.g. {off[0][1:]}" if off else ""))
                if s >= m + 2 and off:
                    bad += 1
    print("Lemma R violations:", bad)


if __name__ == "__main__":
    main()
