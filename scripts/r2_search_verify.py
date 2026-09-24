"""High-precision re-verification (pure mpmath, run with the repo .venv python which has mpmath).
Loads a JSON {X, D, E2, E1}; re-solves the equality system (E2: |xi-xj|=1, E1: |xi-xj|=Delta) by
min-norm Newton at 60 digits to residual < 1e-45; then reports
  - max residual, smallest singular value of J (sqrt of min eig of J J^T) -> full row rank certificate
    heuristics (Newton-Kantorovich: an exact solution lies within ~ |r|/sigma_min of the computed one),
  - gap1 = 1 - max(other distance)  (must be > 0),  Delta - 1,
  - min over all 4-subsets of |sin arg crossratio| (0 iff concyclic or collinear) and the argmin quad,
  - min over 3-subsets of |twice signed area| (collinearity, info only),
  - degrees, hull size, 2-core, t.
usage: .venv/bin/python r2_search_verify.py file.json"""
import sys, json, itertools
import mpmath as mp
mp.mp.dps = 60

def load(fn):
    d = json.load(open(fn))
    X = [[mp.mpf(str(c)) for c in p] for p in d['X']]
    return X, mp.mpf(str(d['D'])), [tuple(e) for e in d['E2']], [tuple(e) for e in d['E1']]

def resid(z, n, E2, E1):
    r = []
    for i, j in E2: r.append((z[2*i]-z[2*j])**2 + (z[2*i+1]-z[2*j+1])**2 - 1)
    for i, j in E1: r.append((z[2*i]-z[2*j])**2 + (z[2*i+1]-z[2*j+1])**2 - z[2*n]**2)
    return r

def jac(z, n, E2, E1):
    rows = []
    for (i, j), isD in [(e, False) for e in E2] + [(e, True) for e in E1]:
        row = [mp.mpf(0)] * (2*n+1)
        gx, gy = 2*(z[2*i]-z[2*j]), 2*(z[2*i+1]-z[2*j+1])
        row[2*i], row[2*i+1], row[2*j], row[2*j+1] = gx, gy, -gx, -gy
        if isD: row[2*n] = -2*z[2*n]
        rows.append(row)
    return mp.matrix(rows)

def main(fn):
    X, D, E2, E1 = load(fn); n = len(X)
    z = [c for p in X for c in p] + [D]
    for it in range(30):
        r = resid(z, n, E2, E1); mr = max(abs(x) for x in r)
        if mr < mp.mpf('1e-50'): break
        J = jac(z, n, E2, E1); rv = mp.matrix(r)
        y = mp.lu_solve(J * J.T, rv); dz = J.T * y
        z = [z[k] - dz[k] for k in range(len(z))]
    r = resid(z, n, E2, E1); mr = max(abs(x) for x in r)
    J = jac(z, n, E2, E1); ev = mp.eigsy(J * J.T)[0]
    smin = mp.sqrt(min(ev[k] for k in range(len(E2)+len(E1))))
    P = [(z[2*i], z[2*i+1]) for i in range(n)]; D = z[2*n]
    dist = lambda a, b: mp.sqrt((P[a][0]-P[b][0])**2 + (P[a][1]-P[b][1])**2)
    S2, S1 = set(E2), set(E1); mo = mp.mpf(0); mind = mp.mpf(10)
    for i in range(n):
        for j in range(i+1, n):
            d = dist(i, j); mind = min(mind, d)
            if (i, j) in S2: assert abs(d-1) < mp.mpf('1e-40')
            elif (i, j) in S1: assert abs(d-D) < mp.mpf('1e-40')
            else: mo = max(mo, d)
    Zc = [mp.mpc(p[0], p[1]) for p in P]
    ccmin, ccq = mp.mpf(1), None
    for q in itertools.combinations(range(n), 4):
        a, b, c, d = (Zc[k] for k in q)
        cr = (a-c)*(b-d)/((a-d)*(b-c)); v = abs(cr.imag)/abs(cr)
        if v < ccmin: ccmin, ccq = v, q
    colmin = min(abs((P[j][0]-P[i][0])*(P[k][1]-P[i][1]) - (P[j][1]-P[i][1])*(P[k][0]-P[i][0]))
                 for i, j, k in itertools.combinations(range(n), 3))
    # hull (monotone chain, exact-ish in mp), 2-core, t
    idx = sorted(range(n), key=lambda i: (P[i][0], P[i][1]))
    cross = lambda o, a, b: (P[a][0]-P[o][0])*(P[b][1]-P[o][1]) - (P[a][1]-P[o][1])*(P[b][0]-P[o][0])
    lo, up = [], []
    for i in idx:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], i) <= 0: lo.pop()
        lo.append(i)
    for i in reversed(idx):
        while len(up) >= 2 and cross(up[-2], up[-1], i) <= 0: up.pop()
        up.append(i)
    H = set(lo[:-1] + up[:-1])
    adj = {i: set() for i in range(n)}
    for i, j in E2: adj[i].add(j); adj[j].add(i)
    core = set(range(n)); ch = True
    while ch:
        ch = False
        for v in list(core):
            if len(adj[v] & core) < 2: core.discard(v); ch = True
    t = sum(1 for v in core if v in H and len(adj[v] & core) == 3)
    deg2 = max(len(adj[v]) for v in range(n))
    deg1 = [0]*n
    for i, j in E1: deg1[i] += 1; deg1[j] += 1
    print(f"{fn}: n={n} mu2={len(E2)} mu1={len(E1)} exc={len(E2)-n} |hull|={len(H)} t={t} "
          f"maxdeg2={deg2} maxdeg1={max(deg1)}")
    print(f"  residual={mp.nstr(mr,3)} sigma_min(J)={mp.nstr(smin,5)} Delta={mp.nstr(D,25)}")
    print(f"  gap 1-max(other)={mp.nstr(1-mo,6)}  Delta-1={mp.nstr(D-1,6)}  min pair dist={mp.nstr(mind,6)}")
    print(f"  min |sin arg CR| over 4-subsets={mp.nstr(ccmin,6)} at {ccq};  min |2*area| over triples={mp.nstr(colmin,6)}")
    ok = mr < mp.mpf('1e-40') and 1-mo > mp.mpf('1e-6') and D-1 > mp.mpf('1e-6') and ccmin > mp.mpf('1e-8')
    print("  VERIFIED" if ok else "  NOT VERIFIED")
    out = fn.replace('.json', '_mp.json')
    json.dump(dict(X=[[mp.nstr(c, 30) for c in p] for p in P], D=mp.nstr(D, 30), E2=E2, E1=E1,
                   gap=mp.nstr(1-mo, 8), cc=mp.nstr(ccmin, 8), ccq=ccq, t=t, exc=len(E2)-n), open(out, 'w'))

if __name__ == '__main__':
    for fn in sys.argv[1:]: main(fn)
