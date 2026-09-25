"""Face walks of the unit-distance plane graph of a band configuration: checks
Def = 3 + 3c + sum_f(|f|-3), and Def >= |outer| + |hole| (+3c-...) with |outer| >= |A|, |hole| >= 2pi(R - t)."""
import math, cmath, sys
from r6_gap_X_disk import Packing, Region, seed_disk_pattern
R, N, w = float(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
P = Packing(Region('disk', R), wband=w); seed_disk_pattern(P, R, N); P.run()
pts = P.pts; n = len(pts)
adj = [[] for _ in range(n)]
for i in range(n):
    for j in P.near(pts[i], 1+1e-6):
        if j != i and abs(abs(pts[i]-pts[j])-1) < 1e-9: adj[i].append(j)
for i in range(n): adj[i].sort(key=lambda j: cmath.phase(pts[j]-pts[i]))
E = sum(len(a) for a in adj)//2
# components
comp = [-1]*n; c = 0
for s in range(n):
    if comp[s] >= 0: continue
    st = [s]; comp[s] = c
    while st:
        u = st.pop()
        for v in adj[u]:
            if comp[v] < 0: comp[v] = c; st.append(v)
    c += 1
# faces: next half-edge after (u->v) is (v->w) where w is the neighbour of v preceding u in ccw order
used = set(); faces = []
for u in range(n):
    for v in adj[u]:
        if (u, v) in used: continue
        walk = []; a, b = u, v
        while (a, b) not in used:
            used.add((a, b)); walk.append(a)
            k = adj[b].index(a); w2 = adj[b][(k-1) % len(adj[b])]
            a, b = b, w2
        area = sum((pts[walk[i]].conjugate()*pts[walk[(i+1) % len(walk)]]).imag for i in range(len(walk)))/2
        faces.append((len(walk), area, walk))
iso = sum(1 for i in range(n) if not adj[i])
Def = 3*n - E
S = sum(L-3 for L, _, _ in faces) + iso*(0-3)  # isolated vertices: their own (empty) walks... none expected
A = sum(1 for z in pts if abs(abs(z)-R) < 1e-9)
neg = sorted([f for f in faces if f[1] < 0], key=lambda f: f[1])   # cw walks = outer boundaries
print('n', n, 'E', E, 'c', c, 'isolated', iso, 'Def', Def, 'Euler RHS', 3 + 3*c + S - 3*(len([1 for f in faces if f[1] < 0]) - 1) if False else None)
# with several components the outer face is one face made of several cw walks; merge them
outer_walks = [f for f in faces if f[1] < 0]
bounded = [f for f in faces if f[1] >= 0]
tot = 3 + 3*c + (sum(f[0] for f in outer_walks) - 3) + sum(f[0]-3 for f in bounded)
print('Euler identity holds (single outer face incl. all cw walks):', tot == Def, tot, Def)
big = sorted(bounded, key=lambda f: -f[0])[:3]
print('|A| =', A, ' outer walk length =', sum(f[0] for f in outer_walks), ' largest bounded faces |f|:', [f[0] for f in big])
dmax = max(R-abs(z) for z in pts)
print('2pi(R - dmax - 1/2) =', 2*math.pi*(R-dmax-0.5), ' Def-2|A| =', Def-2*A, ' floor -(2pi t+3) =', -(2*math.pi*(dmax+0.5)+3))
