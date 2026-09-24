"""Direct construction of the odd 'Reuleaux + all servers + chord block' family from angles.
Hull: Reuleaux-type polygon p_0..p_{m-1}, m=2k+1, all offset-k chords = Delta.  Along the Delta-cycle
v_t = t(k+1) mod m, the star path turns by pi - alpha_{v_{t+1}}; need sum alpha = pi and closure.
Chord c_i = |p_i p_{i+k-1}| has c_i^2 = Delta^2 (1 - g(alpha_{i-1}/2, alpha_{i+k}/2)), g(a,b)=8 sin a sin b cos(a+b).
Matched chords i in S={0..k-2}  <->  Delta-cycle edges at even positions t in {m-2, 0, 2, .., 2k-6}.
Design: along the matched stretch the half-angles alternate increasing / decreasing (ratio r), then Newton
(min-norm) on [sum, closure(2), g=kappa on matched]; servers s_i at unit distance from p_i, p_{i+1}.
usage: python3 r2_search_reuleaux.py m r seed [climb_iters]"""
import sys, math, json
import numpy as np
from r2_search_common import *
from r2_search_margin import climb

def g(a, b): return 8 * np.sin(a) * np.sin(b) * np.cos(a + b)

def hull_from_angles(al, D, m, k):
    v = [(t * (k + 1)) % m for t in range(m)]
    P = np.zeros((m, 2)); phi = 0.0; pos = np.zeros(2)
    for t in range(m):
        P[v[t]] = pos; pos = pos + D * np.array([math.cos(phi), math.sin(phi)])
        phi += math.pi - al[v[(t + 1) % m]]
    return P, pos  # pos should return to P[v0]=0 (closure)

def eqs(w, m, k, matched):
    al, kap = w[:m], w[m]; D = 1 / math.sqrt(1 - kap)
    _, clo = hull_from_angles(al, D, m, k)
    r = [al.sum() - math.pi, clo[0], clo[1]]
    for (u, x) in matched: r.append(g(al[u] / 2, al[x] / 2) - kap)
    return np.array(r)

def main():
    m = int(sys.argv[1]); ratio = float(sys.argv[2]); seed = int(sys.argv[3])
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = np.random.default_rng(seed); k = m // 2
    v = [(t * (k + 1)) % m for t in range(m)]
    tpos = [(m - 2 + 2 * j) % m for j in range(k - 1)]          # matched edge positions
    matched = [(v[t], v[(t + 1) % m]) for t in tpos]
    # design: stretch s=0..2k-3 starting at t=m-2
    base = math.pi / m; al = np.full(m, base)
    for j in range(k - 1):
        t0 = (m - 2 + 2 * j) % m
        al[v[t0]] = base * ratio ** (j - (k - 2) / 2)
        al[v[(t0 + 1) % m]] = base * ratio ** (-(j - (k - 2) / 2))
    for t in (2 * k - 4, 2 * k - 3, 2 * k - 2):                  # the 3 free vertices: large angles
        al[v[t]] = base * ratio ** ((k - 2) / 2) * 1.3
    al *= math.pi / al.sum()
    kap = min(g(al[u] / 2, al[x] / 2) for u, x in matched)
    w = np.concatenate([al, [kap]])
    for it in range(100):
        r = eqs(w, m, k, matched)
        if np.max(np.abs(r)) < 1e-14: break
        J = np.zeros((len(r), m + 1)); h = 1e-7
        for c in range(m + 1):
            w2 = w.copy(); w2[c] += h; J[:, c] = (eqs(w2, m, k, matched) - r) / h
        w = w - np.linalg.lstsq(J, r, rcond=None)[0]
    # angle-space SLSQP: maximise min over unmatched Delta-edges of g/kappa - 1 (capped), equalities kept
    from scipy.optimize import minimize
    unm = [((i - 1) % m, (i + k) % m) for i in range(k - 1, m)]
    cap = float(sys.argv[5]) if len(sys.argv) > 5 else 0.3
    def ineq(y):
        al, kap = y[:m], y[m]
        return np.array([g(al[u] / 2, al[x] / 2) / kap - 1 - y[-1] for u, x in unm] + list(al - 0.2 * math.pi / m))
    res = minimize(lambda y: -y[-1], np.concatenate([w, [0.0]]), method='SLSQP',
                   constraints=[{'type': 'eq', 'fun': lambda y: eqs(y[:m + 1], m, k, matched)},
                                {'type': 'ineq', 'fun': ineq}],
                   bounds=[(None, None)] * (m + 1) + [(-1, cap)], options={'maxiter': 500, 'ftol': 1e-14})
    w = res.x[:m + 1]
    for it in range(50):
        r = eqs(w, m, k, matched)
        if np.max(np.abs(r)) < 1e-15: break
        J = np.zeros((len(r), m + 1)); h = 1e-7
        for c in range(m + 1):
            w2 = w.copy(); w2[c] += h; J[:, c] = (eqs(w2, m, k, matched) - r) / h
        w = w - np.linalg.lstsq(J, r, rcond=None)[0]
    # genericise inside the angle family: random kernel steps (keep min unmatched g/kappa > 1)
    eps = float(sys.argv[6]) if len(sys.argv) > 6 else 0.05
    def newton_w(w):
        for it in range(50):
            r = eqs(w, m, k, matched)
            if np.max(np.abs(r)) < 1e-15: return w, True
            J = np.zeros((len(r), m + 1)); h = 1e-7
            for c in range(m + 1):
                w2 = w.copy(); w2[c] += h; J[:, c] = (eqs(w2, m, k, matched) - r) / h
            w = w - np.linalg.lstsq(J, r, rcond=None)[0]
        return w, np.max(np.abs(eqs(w, m, k, matched))) < 1e-13
    def ming(w): return min(g(w[u] / 2, w[x] / 2) / w[m] for u, x in unm), w[:m].min()
    for rep in range(5):
        r = eqs(w, m, k, matched); J = np.zeros((len(r), m + 1)); h = 1e-7
        for c in range(m + 1):
            w2 = w.copy(); w2[c] += h; J[:, c] = (eqs(w2, m, k, matched) - r) / h
        K = np.linalg.svd(J)[2][len(r):].T
        dz = K @ rng.standard_normal(K.shape[1]); dz *= eps * (math.pi / m) / np.linalg.norm(dz)
        w2, ok = newton_w(w + dz)
        if ok and ming(w2)[0] > 1 + 0.5 * (ming(w)[0] - 1) and ming(w2)[1] > 0: w = w2
    al, kap = w[:m], w[m]; D = 1 / math.sqrt(1 - kap)
    P, clo = hull_from_angles(al, D, m, k)
    gk = [g(al[(i - 1) % m] / 2, al[(i + k) % m] / 2) / kap for i in range(m)]
    print(f"m={m} angle-system resid={np.max(np.abs(eqs(w, m, k, matched))):.1e} Delta={D:.6f} "
          f"min alpha*m/pi={al.min()*m/math.pi:.3f} max={al.max()*m/math.pi:.3f}  min unmatched g/kappa="
          f"{min(gk[i] for i in range(k-1, m)):.4f}")
    # servers
    c = P.mean(0); S = []
    for i in range(m):
        A, B = P[i], P[(i + 1) % m]; mid = (A + B) / 2; d = np.linalg.norm(B - A)
        hg = math.sqrt(1 - d * d / 4); nr = np.array([-(B - A)[1], (B - A)[0]]) / d
        S.append(min([mid + hg * nr, mid - hg * nr], key=lambda x: np.linalg.norm(x - c)))
    X = np.vstack([P, np.array(S)])
    A0 = analyse(X, D)
    print(f"  full config: n={A0['n']} mu2={A0['mu2']} mu1={A0['mu1']} exc={A0['exc']} t={A0['t']} "
          f"slack={1-A0['maxother']:.3e} cc={A0['cc']:.3e} valid={valid(A0)}")
    E2, E1 = A0['E2'], A0['E1']
    if iters:
        X, D, f = climb(X, D, E2, E1, rng, iters=iters, sigma=0.003)
        A0 = analyse(X, D)
        print(f"  after climb: exc={A0['exc']} t={A0['t']} slack={1-A0['maxother']:.3e} cc={A0['cc']:.3e} valid={valid(A0)}")
    json.dump(dict(X=[[repr(a) for a in p] for p in X], D=repr(D), E2=A0['E2'], E1=A0['E1']),
              open(f"reuleaux_m{m}.json", "w"))

if __name__ == '__main__':
    main()
