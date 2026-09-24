"""Hull-only feasibility in the angle model for a chord block of size b (b = k-1 or k):
maximise min_{unmatched Delta-edges} g/kappa - 1 subject to sum alpha = pi, closure, g = kappa on matched,
alpha >= 0.05*pi/m.  Many random starts.  usage: python3 r2_search_anglefeas.py m b starts"""
import sys, math
import numpy as np
from scipy.optimize import minimize
from r2_search_reuleaux import g, eqs
m, b, starts = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); k = m // 2
v = [(t * (k + 1)) % m for t in range(m)]
# chord e_i=(i,i+k-1) <-> Delta-edge (i-1, i+k); block i = 0..b-1
matched = [((i - 1) % m, (i + k) % m) for i in range(b)]
unm = [((i - 1) % m, (i + k) % m) for i in range(b, m)]
rng = np.random.default_rng(0); best = -9
for s in range(starts):
    al = rng.uniform(0.3, 2.0, m); al *= math.pi / al.sum()
    kap = np.mean([g(al[u]/2, al[x]/2) for u, x in matched])
    y0 = np.concatenate([al, [kap], [0.0]])
    ineq = lambda y: np.array([g(y[u]/2, y[x]/2) / y[m] - 1 - y[-1] for u, x in unm] + list(y[:m] - 0.05*math.pi/m) + [y[m] - 1e-4])
    r = minimize(lambda y: -y[-1], y0, method='SLSQP', bounds=[(None, None)]*(m+1) + [(-2, 1)],
                 constraints=[{'type': 'eq', 'fun': lambda y: eqs(y[:m+1], m, k, matched)}, {'type': 'ineq', 'fun': ineq}],
                 options={'maxiter': 800, 'ftol': 1e-13})
    if np.max(np.abs(eqs(r.x[:m+1], m, k, matched))) < 1e-9 and np.min(ineq(r.x)) > -1e-9: best = max(best, r.x[-1])
print(f"m={m} block={b}: best min(g/kappa)-1 over unmatched = {best:.4f}  ({'feasible' if best > 0 else 'INFEASIBLE (numerically)'})")
# report which unmatched chords are tight at the last feasible optimum
y = r.x; vals = [(g(y[u]/2, y[x]/2) / y[m] - 1, i) for (u, x), i in zip(unm, range(b, m))]
print("   tight unmatched chord indices i (e_i=(i,i+k-1)):", [i for vv, i in vals if vv < 1e-6], " sum alpha - pi:", f"{y[:m].sum()-math.pi:.1e}")
