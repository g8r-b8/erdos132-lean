"""R2 common tools: realise a combinatorial type (E2 = pairs at distance 1 = Delta2, E1 = pairs at
distance Delta = diameter, Delta a free variable), with every other pair < 1 - margin, and check
no-4-concyclic.  Floating point exploration only; candidates are re-verified with mpmath
(r2_search_verify.py).

Concyclicity measure: for points a,b,c,d (complex), cross ratio CR = (a-c)(b-d)/((a-d)(b-c)) is real
iff the four points are concyclic or collinear.  cc(a,b,c,d) = |Im CR| / |CR| = |sin arg CR| in [0,1],
scale/rotation invariant.  4 concyclic <=> cc = 0 (or 4 collinear)."""
import numpy as np, itertools, math
from scipy.optimize import minimize
from scipy.spatial import ConvexHull

EQ_TOL = 1e-9

_quad_cache = {}
def quads(n):
    if n not in _quad_cache:
        _quad_cache[n] = np.array(list(itertools.combinations(range(n), 4)), dtype=int).reshape(-1, 4)
    return _quad_cache[n]

def cc_all(X):
    """min over 4-subsets of |sin arg crossratio|, and the argmin quadruple."""
    n = len(X)
    if n < 4: return 1.0, None
    Z = X[:, 0] + 1j * X[:, 1]
    Q = quads(n); a, b, c, d = (Z[Q[:, k]] for k in range(4))
    cr = (a - c) * (b - d) / ((a - d) * (b - c))
    v = np.abs(cr.imag) / np.abs(cr)
    v = np.nan_to_num(v, nan=0.0)
    k = int(np.argmin(v)); return float(v[k]), tuple(Q[k])

def cc_vals(X):
    n = len(X); Z = X[:, 0] + 1j * X[:, 1]
    Q = quads(n); a, b, c, d = (Z[Q[:, k]] for k in range(4))
    cr = (a - c) * (b - d) / ((a - d) * (b - c))
    return np.abs(cr.imag) / np.abs(cr), Q

def dist_matrix(X):
    return np.sqrt(((X[:, None, :] - X[None, :, :]) ** 2).sum(-1))

def classify(X, D, tol=EQ_TOL):
    """Return (E2, E1, maxother) from actual geometry: E2 pairs with |d-1|<tol, E1 pairs |d-D|<tol,
    maxother = max distance among other pairs."""
    n = len(X); M = dist_matrix(X); E2 = []; E1 = []; mo = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            d = M[i, j]
            if abs(d - 1) < tol: E2.append((i, j))
            elif abs(d - D) < tol: E1.append((i, j))
            else: mo = max(mo, d)
    return E2, E1, mo

# ---------------- equality system ----------------
def resid(z, n, E2, E1):
    X = z[:2 * n].reshape(n, 2); D = z[-1]; r = []
    for i, j in E2: r.append(((X[i] - X[j]) ** 2).sum() - 1.0)
    for i, j in E1: r.append(((X[i] - X[j]) ** 2).sum() - D * D)
    return np.array(r)

def jac(z, n, E2, E1):
    X = z[:2 * n].reshape(n, 2); D = z[-1]
    m = len(E2) + len(E1); J = np.zeros((m, 2 * n + 1)); k = 0
    for i, j in E2:
        g = 2 * (X[i] - X[j]); J[k, 2*i:2*i+2] = g; J[k, 2*j:2*j+2] = -g; k += 1
    for i, j in E1:
        g = 2 * (X[i] - X[j]); J[k, 2*i:2*i+2] = g; J[k, 2*j:2*j+2] = -g; J[k, -1] = -2 * D; k += 1
    return J

def newton(z, n, E2, E1, iters=60, tol=1e-13):
    for _ in range(iters):
        r = resid(z, n, E2, E1)
        if len(r) == 0 or np.max(np.abs(r)) < tol: return z, True
        J = jac(z, n, E2, E1)
        z = z - np.linalg.lstsq(J, r, rcond=None)[0]
        if not np.all(np.isfinite(z)): return z, False
    r = resid(z, n, E2, E1)
    return z, (len(r) == 0 or np.max(np.abs(r)) < 1e-11)

def dof(z, n, E2, E1):
    """dimension of solution variety at z modulo rigid motions (3)."""
    if not E2 and not E1: return 2 * n + 1 - 3
    J = jac(z, n, E2, E1); s = np.linalg.svd(J, compute_uv=False)
    rank = int(np.sum(s > 1e-8 * max(1, s[0])))
    return 2 * n + 1 - 3 - rank

def kernel(z, n, E2, E1):
    J = jac(z, n, E2, E1)
    if J.shape[0] == 0: return np.eye(len(z))
    U, s, Vt = np.linalg.svd(J)
    rank = int(np.sum(s > 1e-8 * max(1, s[0])))
    return Vt[rank:].T

# ---------------- slack optimisation ----------------
def realise(X0, D0, E2, E1, cap=0.03, sep=0.02, maxiter=200):
    """Maximise s <= cap subject to: E2 distances = 1, E1 = Delta, other pairs d^2 <= (1-s)^2,
    other pairs d >= sep, Delta >= 1 + s.  Returns (X, D, s) or None."""
    n = len(X0); E = set(E2) | set(E1)
    others = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in E]
    oi = np.array([p[0] for p in others], int); oj = np.array([p[1] for p in others], int)
    z0 = np.concatenate([X0.ravel(), [D0], [0.0]])
    N = 2 * n + 1

    def eqf(w): return resid(w[:N], n, E2, E1)
    def eqj(w):
        J = jac(w[:N], n, E2, E1); return np.hstack([J, np.zeros((J.shape[0], 1))])
    def inf(w):
        X = w[:2*n].reshape(n, 2); D = w[2*n]; s = w[-1]
        d2 = ((X[oi] - X[oj]) ** 2).sum(-1)
        return np.concatenate([(1 - s) ** 2 - d2, d2 - sep * sep, [D - 1 - s]])
    def inj(w):
        X = w[:2*n].reshape(n, 2); s = w[-1]; m = len(oi)
        J = np.zeros((2 * m + 1, N + 1)); g = 2 * (X[oi] - X[oj]); r = np.arange(m)
        J[r, 2*oi] = -g[:, 0]; J[r, 2*oi+1] = -g[:, 1]; J[r, 2*oj] = g[:, 0]; J[r, 2*oj+1] = g[:, 1]
        J[r, -1] = -2 * (1 - s)
        J[m + r, 2*oi] = g[:, 0]; J[m + r, 2*oi+1] = g[:, 1]; J[m + r, 2*oj] = -g[:, 0]; J[m + r, 2*oj+1] = -g[:, 1]
        J[2*m, 2*n] = 1; J[2*m, -1] = -1
        return J
    cons = []
    if E2 or E1: cons.append({'type': 'eq', 'fun': eqf, 'jac': eqj})
    if len(oi): cons.append({'type': 'ineq', 'fun': inf, 'jac': inj})
    bounds = [(None, None)] * N + [(-1, cap)]
    try:
        res = minimize(lambda w: -w[-1], z0, jac=lambda w: np.concatenate([np.zeros(N), [-1.0]]),
                       constraints=cons, bounds=bounds, method='SLSQP',
                       options={'maxiter': maxiter, 'ftol': 1e-12})
    except Exception:
        return None
    w = res.x
    if not np.all(np.isfinite(w)): return None
    z, ok = newton(w[:N], n, E2, E1)
    if not ok: return None
    X = z[:2*n].reshape(n, 2); D = z[-1]
    return X, D, float(w[-1])

def genericize(X, D, E2, E1, rng, size=3e-3, tries=4):
    """random step in kernel of the constraint Jacobian + reprojection; keeps inequalities if possible."""
    n = len(X); z = np.concatenate([X.ravel(), [D]])
    K = kernel(z, n, E2, E1)
    if K.shape[1] == 0: return X, D
    for _ in range(tries):
        dz = K @ rng.standard_normal(K.shape[1]); dz *= size / (np.linalg.norm(dz) + 1e-30)
        z2, ok = newton(z + dz, n, E2, E1)
        if ok:
            X2 = z2[:2*n].reshape(n, 2); e2, e1, mo = classify(X2, z2[-1])
            if set(e2) == set(E2) and set(e1) == set(E1) and mo < 1 - 1e-6 and z2[-1] > 1:
                return X2, z2[-1]
        size /= 3
    return X, D

# ---------------- analysis ----------------
def hull_vertices(X):
    try:
        h = ConvexHull(X); return set(int(v) for v in h.vertices)
    except Exception:
        return set(range(len(X)))

def two_core(n, E):
    adj = {i: set() for i in range(n)}
    for i, j in E: adj[i].add(j); adj[j].add(i)
    alive = set(range(n)); changed = True
    while changed:
        changed = False
        for v in list(alive):
            if len(adj[v] & alive) < 2: alive.discard(v); changed = True
    return alive, adj

def analyse(X, D):
    n = len(X); E2, E1, mo = classify(X, D)
    H = hull_vertices(X); core, adj = two_core(n, E2)
    degc = {v: len(adj[v] & core) for v in core}
    t = sum(1 for v in core if v in H and degc[v] == 3)
    ccm, q = cc_all(X)
    Mm = dist_matrix(X) + 9 * np.eye(n); minsep = float(Mm.min()) if n > 1 else 9.0
    if not np.isfinite(ccm): ccm = 0.0
    deg2 = [len(adj[v]) for v in range(n)]
    deg1 = [0] * n
    for i, j in E1: deg1[i] += 1; deg1[j] += 1
    return dict(n=n, mu2=len(E2), mu1=len(E1), exc=len(E2) - n, t=t, maxother=mo, D=D,
                cc=ccm, ccq=q, minsep=minsep, E2=E2, E1=E1, hull=H, core=core, degc=degc,
                maxdeg2=max(deg2) if n else 0, maxdeg1=max(deg1) if n else 0)

def valid(A, margin=1e-5, ccmin=1e-7):
    # min separation added after beam artefacts with coincident points (cross ratio 0/0 = nan slipped through)
    return (A['maxother'] < 1 - margin and A['D'] > 1 + margin and A['cc'] > ccmin
            and A['mu1'] >= 1 and A['minsep'] > 1e-3)

def pattern(X, A):
    """For each deg-3 hull vertex p of G' with nbrs w1,w2,w3 (angular order): deg_G(w2), w2 extreme?,
    other nbrs r of w2 and whether |r w1| or |r w3| = Delta."""
    n = len(X); E2 = A['E2']; E1 = set(A['E1']); H = A['hull']
    adj = {i: set() for i in range(n)}
    for i, j in E2: adj[i].add(j); adj[j].add(i)
    out = []
    for p in sorted(A['core']):
        if p not in H or A['degc'][p] != 3: continue
        nb = sorted(adj[p])
        # angular order inside a half-plane: sort by angle relative to the direction away from centroid
        c = X.mean(0); base = math.atan2(*(X[p] - c)[::-1])
        ang = lambda w: (math.atan2(*(X[w] - X[p])[::-1]) - base) % (2 * math.pi)
        nb = sorted(nb, key=ang)
        w1, w2, w3 = nb[0], nb[len(nb)//2], nb[-1]
        rs = []
        for r in adj[w2] - {p}:
            f1 = (min(r, w1), max(r, w1)) in E1; f3 = (min(r, w3), max(r, w3)) in E1
            rs.append((r, 'w1' if f1 else '', 'w3' if f3 else ''))
        out.append(dict(p=p, deg_p=len(adj[p]), w=(w1, w2, w3), deg_w2=len(adj[w2]), w2_ext=w2 in H,
                        r=rs))
    return out
