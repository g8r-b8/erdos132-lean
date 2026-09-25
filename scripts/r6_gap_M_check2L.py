"""Sanity (floats): pair-gap A-row + greedy completion; evaluate the Two-Layer ledger.
s_x = 2 - u_x - (r_x - 1)_+ over the c-row (= outer cycle of G[B]); g; Def - 2|A|; turning of the c-row."""
import math, cmath, sys
sys.argv = [sys.argv[0]] + sys.argv[1:]
from r6_gap_M_fill import run
R = float(sys.argv[1]) if len(sys.argv) > 1 else 30
pts, deg, nA = run('pairgap', R)
n = len(pts); TOL = 1e-9
adj = [[] for _ in range(n)]
for i in range(n):
    for j in range(i+1, n):
        if abs(abs(pts[i]-pts[j])-1) < TOL: adj[i].append(j); adj[j].append(i)
A = set(range(nA))
# c-row = the prescribed apexes (indices nA .. nA+len-1), in order
crow = list(range(nA, nA + nA))  # one apex per chord (pattern closes with all chords < 2?)
crow = [c for c in crow if c < n and any(a in A for a in adj[c])]
dT = [sum(1 for j in adj[a] if j in A) for a in range(nA)]
g = sum(2-d for d in dT)
S = 0; hist = {}
for k, c in enumerate(crow):
    u = sum(1 for j in adj[c] if j in A)
    nb = {crow[k-1], crow[(k+1) % len(crow)]}
    r = sum(1 for j in adj[c] if j not in A and j not in nb)
    s = 2 - u - max(r-1, 0); S += s; hist[(u, r)] = hist.get((u, r), 0) + 1
tn = [(-cmath.phase((pts[crow[(k+1)%len(crow)]]-pts[crow[k]])/(pts[crow[k]]-pts[crow[k-1]]))) for k in range(len(crow))]
print('|crow|', len(crow), ' sum s_x', S, ' g/2', g/2, ' sum s + g/2', S+g/2, ' (u,r) hist', hist)
print('c-row turning min/max', min(tn), max(tn), ' #reflex', sum(1 for t in tn if t < -1e-12))
