"""R2: independent Newton polish of a candidate (points + prescribed Δ₂=1 / Δ edge lists) at high
precision, then output the polished points for r2_verify.py.

Usage: python3 r2_polish.py in.json out.txt [dps]
in.json keys: X (list of [x,y] strings), D (string), E2 (unit edges), E1 (Δ edges).
Unknowns: all coordinates and Δ; equations |xi-xj|^2 = 1 (E2), = Δ^2 (E1). Minimum-norm Gauss-Newton
steps (J^T (J J^T)^{-1} F), which converge quadratically when J has full row rank.
Prints the final residual and the smallest singular value of J (Kantorovich-type sanity).
"""
import sys, json
import mpmath as mp


def main():
    dps = int(sys.argv[3]) if len(sys.argv) > 3 else 80
    mp.mp.dps = dps
    d = json.load(open(sys.argv[1]))
    X = [[mp.mpf(a), mp.mpf(b)] for a, b in d["X"]]
    D = mp.mpf(d["D"]); E2 = [tuple(e) for e in d["E2"]]; E1 = [tuple(e) for e in d["E1"]]
    n = len(X); N = 2 * n + 1

    def F(z):
        out = []
        for i, j in E2:
            out.append((z[2*i]-z[2*j])**2 + (z[2*i+1]-z[2*j+1])**2 - 1)
        for i, j in E1:
            out.append((z[2*i]-z[2*j])**2 + (z[2*i+1]-z[2*j+1])**2 - z[N-1]**2)
        return mp.matrix(out)

    def J(z):
        rows = []
        for (i, j), isD in [(e, False) for e in E2] + [(e, True) for e in E1]:
            r = [mp.mpf(0)] * N
            dx = z[2*i]-z[2*j]; dy = z[2*i+1]-z[2*j+1]
            r[2*i], r[2*i+1], r[2*j], r[2*j+1] = 2*dx, 2*dy, -2*dx, -2*dy
            if isD:
                r[N-1] = -2*z[N-1]
            rows.append(r)
        return mp.matrix(rows)

    z = [c for p in X for c in p] + [D]
    for it in range(40):
        f = F(z)
        if mp.norm(f) < mp.mpf(10) ** (-(dps - 8)):
            break
        A = J(z)
        y = mp.lu_solve(A * A.T, f)
        dz = A.T * y
        z = [z[k] - dz[k] for k in range(N)]
    res = mp.norm(F(z))
    sv = mp.svd_r(J(z), compute_uv=False)
    print("residual", mp.nstr(res, 5), "sigma_min(J)", mp.nstr(min(sv[k] for k in range(len(sv))), 5), "Delta", mp.nstr(z[N-1], 20))
    with open(sys.argv[2], "w") as fh:
        for i in range(n):
            fh.write(mp.nstr(z[2*i], dps - 5) + " " + mp.nstr(z[2*i+1], dps - 5) + "\n")


if __name__ == "__main__":
    main()
