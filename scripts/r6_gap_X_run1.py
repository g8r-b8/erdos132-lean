import sys, json, math, cmath
from r6_gap_X_band import Band
from r6_gap_X_seeds import tri_path, solveR
N, M, w = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
allowA = len(sys.argv) > 4 and 'A' in sys.argv[4]
R = solveR(N, M)
P, B, qR, per = tri_path(R, N)
b = Band(R, M, w, allowA=allowA)
C0 = []
for z in P + B + [qR]:
    zc = b.canon(z)
    if all(abs(zc - y) > 1e-7 for y in b.copies()): b.add(z)
b.greedy()
st = b.stats()
st['R'] = R; st['N'] = N; st['M'] = M; st['w'] = w
print(json.dumps(st, default=str))
