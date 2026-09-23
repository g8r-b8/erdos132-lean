"""Ve87 Case 1 re-done with direct circle intersections (sympy.solve dropped solutions in va1b_cases.py).
q = 0, v_k = unit vectors at 0, 120, 240 deg, Delta = sqrt3. An extra Delta2-neighbour P of v_i (P != q) has
|P - v_i| = 1, |P| <= 1, and |P - v_j| in [0,1] U {sqrt3} for j != i.
(1) Show the open branch (both other distances <= 1) is empty.
(2) Enumerate the equality-branch candidates, check 3-fold symmetry, and check whether some pairwise-compatible
    candidate set gives all three v_i a second neighbour. If none does, deg_G(v_i) = 1 for some i, so q cannot have
    3 neighbours in the 2-core."""
import math, itertools
from va1b_cases import circ
V = [(math.cos(2*math.pi*k/3), math.sin(2*math.pi*k/3)) for k in range(3)]
S3 = math.sqrt(3); E = 1e-9
def allowed(d): return d <= 1+E or abs(d-S3) < E
openb = 0
for i in range(3):
    for k in range(200001):
        phi = 2*math.pi*k/200000; P = (V[i][0]+math.cos(phi), V[i][1]+math.sin(phi)); r = math.hypot(*P)
        if r > 1+E or r < 1e-6: continue
        if all(math.dist(P, V[j]) <= 1+E for j in range(3) if j != i): openb += 1
print("open branch hits:", openb)
C = []
for i in range(3):
    for j in range(3):
        if i == j: continue
        for P in circ(V[i], 1.0, V[j], S3):
            r = math.hypot(*P)
            if r > 1+E or r < 1e-6: continue
            if all(allowed(math.dist(P, V[k])) for k in range(3) if k != i) and not any(math.dist(P, Q) < 1e-7 for _, Q in C):
                C.append((i, P))
for i, P in C: print("owner v%d" % i, "P=(%.6f, %.6f)" % P, "|P|=%.6f" % math.hypot(*P),
                     "dists to v:", ["%.6f" % math.dist(P, v) for v in V])
own = lambda P: {i for i in range(3) if abs(math.dist(P, V[i])-1) < E}
hit = []
for r in range(1, len(C)+1):
    for S in itertools.combinations(C, r):
        if all(allowed(math.dist(P, Q)) for (_, P), (_, Q) in itertools.combinations(S, 2)):
            if set().union(*(own(P) for _, P in S)) == {0, 1, 2}: hit.append(S)
print("candidates:", len(C), "| compatible sets covering all v_i:", len(hit))
print("pairwise distances between candidates:")
for (a, P), (b, Q) in itertools.combinations(C, 2):
    d = math.dist(P, Q); print("  v%d-cand vs v%d-cand: %.6f %s" % (a, b, d, "ok" if allowed(d) else "FORBIDDEN"))
