"""Check the exact identity for Reuleaux-type odd polygons (all offset-k chords = Delta):
  alpha_j = angle at p_j between its Delta-neighbours p_{j+k}, p_{j+k+1};
  c_i = |p_i p_{i+k-1}|  satisfies  c_i^2 = Delta^2 (1 - 8 sin a sin b cos(a+b)),
  a = alpha_{i-1}/2, b = alpha_{i+k}/2  ((i-1, i+k) is a Delta-edge).
So c_i <= 1  <=>  g(a,b) := 8 sin a sin b cos(a+b) >= 1 - Delta^-2, symmetric along each Delta-edge."""
import sys, json, math
import numpy as np
for fn in sys.argv[1:]:
    d = json.load(open(fn)); X = np.array([[float(c) for c in p] for p in d['X']]); D = float(d['D'])
    m = sum(1 for e in d['E1']); k = m // 2; P = X[:m]
    def ang(j):
        u = P[(j+k) % m] - P[j]; v = P[(j+k+1) % m] - P[j]
        return math.acos(np.dot(u, v) / np.linalg.norm(u) / np.linalg.norm(v))
    al = [ang(j) for j in range(m)]; err = 0; gs = []
    for i in range(m):
        a, b = al[(i-1) % m]/2, al[(i+k) % m]/2
        pred = D*D*(1 - 8*math.sin(a)*math.sin(b)*math.cos(a+b)); c2 = np.sum((P[i]-P[(i+k-1) % m])**2)
        err = max(err, abs(pred - c2)); gs.append(8*math.sin(a)*math.sin(b)*math.cos(a+b))
    kap = 1 - D**-2
    print(fn, f"m={m} sum alpha - pi = {sum(al)-math.pi:.2e}  max|identity err|={err:.2e}  kappa={kap:.6f}")
    print("   g/kappa per chord i:", " ".join(f"{g/kap:.4f}" for g in gs))
    print("   alpha*m/pi along Delta-cycle order:", " ".join(f"{al[(t*(k+1)) % m]*m/math.pi:.2f}" for t in range(m)))
