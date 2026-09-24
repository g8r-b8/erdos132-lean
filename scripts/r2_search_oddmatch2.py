"""odd m-gon + all servers + chord matching S (default 0..k-2); realise, then maximise margin.
usage: python3 r2_search_oddmatch2.py m starts seed [iters]"""
import sys, json
import numpy as np
from r2_search_common import *
from r2_search_deform import build, alt4
from r2_search_margin import climb, objective
m, starts, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); k = m // 2
iters = int(sys.argv[4]) if len(sys.argv) > 4 else 400
S = list(range(k - 1)); rng = np.random.default_rng(seed)
X0, D0, E2full, E1full = build('odd', m)
E2 = sorted([e for e in E2full if max(e) >= m] + [tuple(sorted((i, (i + k - 1) % m))) for i in S]); E1 = E1full
assert not alt4(E2, E1)
best = None
for tr in range(starts):
    X = X0 + rng.normal(0, [1e-2, 3e-2][tr % 2], X0.shape)
    r = realise(X, D0, E2, E1, cap=0.03, maxiter=500)
    if r is None or r[2] < 1e-4: print(tr, "realise fail", r and r[2]); continue
    X, D, s = r
    X, D, f = climb(X, D, E2, E1, rng, iters=iters)
    A = analyse(X, D)
    print(tr, f"f={f:.3e} exc={A['exc']} n={A['n']} mu2={A['mu2']} mu1={A['mu1']} t={A['t']} cc={A['cc']:.3e} slack={1-A['maxother']:.3e} D={D:.6f} valid={valid(A)}", flush=True)
    if valid(A) and (best is None or f > best[0]): best = (f, X, D, A)
if best:
    f, X, D, A = best
    json.dump(dict(m=m, S=S, X=[[repr(a) for a in p] for p in X], D=repr(D), E2=A['E2'], E1=A['E1'], f=f,
                   exc=A['exc'], t=A['t'], pattern=pattern(X, A)), open(f"oddmatch_m{m}_best.json", "w"), default=str)
    print("saved; pattern:", pattern(X, A))
