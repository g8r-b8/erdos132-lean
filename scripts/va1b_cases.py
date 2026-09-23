"""Verify the two local lemmas behind 'deg_{G'}(q) <= 2 for q in L2' (Ve87 Cases 1, 2).
Normalise q = 0, Delta2 = 1. Every point of X lies in the closed unit disk (q has no Delta-partner).
All distances in X are <= 1 or == Delta.

Case 2: v1 = (-1,0), v2, v3 = (cos a, +-sin a), 0 < a <= 30deg, Delta = |v1 v2| = 2cos(a/2).
  Claim: no r != q with |r - v1| = 1, |r| <= 1, |r - v_i| in [0,1] U {Delta} (i = 2,3). So deg_G(v1) = 1.
Case 1: v_i on unit circle at 0, 120, 240 deg, Delta = sqrt3. Candidate extra neighbours of v_i lie on
  circle(v_i,1) cap disk and must be at distance exactly sqrt3 from another v_j. Enumerate them exactly, then
  check which subsets are pairwise compatible, and whether each v_i can get degree >= 2 simultaneously."""
import math, itertools
import sympy as sp

# ---------- Case 2: dense sweep + exact treatment of the equality branches ----------
def case2(a, steps=4000):
    D = 2*math.cos(a/2)
    v1 = (-1.0, 0.0); v2 = (math.cos(a), math.sin(a)); v3 = (math.cos(a), -math.sin(a))
    bad = []
    # branch A: both |r-v2|,|r-v3| <= 1 (open condition -> sweep)
    for k in range(steps+1):
        phi = -math.pi/3 + (2*math.pi/3)*k/steps
        r = (v1[0]+math.cos(phi), v1[1]+math.sin(phi))
        if math.hypot(*r) > 1+1e-12 or math.hypot(*r) < 1e-9: continue
        if math.dist(r, v2) <= 1+1e-12 and math.dist(r, v3) <= 1+1e-12: bad.append(('both<=1', r))
    # branch B: |r - v_i| = Delta exactly for i=2 (or 3, symmetric): intersect circles
    for vi, vj in ((v2, v3), (v3, v2)):
        for r in circ(v1, 1.0, vi, D):
            if math.hypot(*r) > 1+1e-12 or math.hypot(*r) < 1e-9: continue
            dj = math.dist(r, vj)
            if dj <= 1+1e-12 or abs(dj-D) < 1e-9: bad.append(('eqD', r, dj))
    return bad

def circ(p, r1, q, r2):
    d = math.dist(p, q)
    if d > r1+r2 or d < abs(r1-r2) or d == 0: return []
    a = (r1*r1-r2*r2+d*d)/(2*d); h = math.sqrt(max(r1*r1-a*a, 0))
    ex, ey = (q[0]-p[0])/d, (q[1]-p[1])/d; mx, my = p[0]+a*ex, p[1]+a*ey
    return [(mx-h*ey, my+h*ex), (mx+h*ey, my-h*ex)]

if __name__ == '__main__':
  worst = 0
  for k in range(1, 3001):
      a = math.radians(30)*k/3000
      b = case2(a)
      if b: print("CASE 2 VIOLATION a=%.4f deg" % math.degrees(a), b[:2]); worst += 1
  print("Case 2: violations over 3000 angles:", worst)

  # ---------- Case 1: exact ----------
  s3 = sp.sqrt(3)
  V = [sp.Matrix([sp.cos(2*sp.pi*k/3), sp.sin(2*sp.pi*k/3)]) for k in range(3)]
  x, y = sp.symbols('x y', real=True)
  cands = []   # (owner i, point) : |P - V_i| = 1, |P| <= 1, P != 0, |P - V_j| = sqrt3 for some j != i
  for i in range(3):
      for j in range(3):
          if i == j: continue
          sols = sp.solve([(x-V[i][0])**2+(y-V[i][1])**2-1, (x-V[j][0])**2+(y-V[j][1])**2-3], [x, y], dict=True)
          for s in sols:
              P = sp.Matrix([sp.nsimplify(sp.simplify(s[x])), sp.nsimplify(sp.simplify(s[y]))])
              n2 = sp.simplify(P.dot(P))
              if n2 == 0 or n2 > 1: continue
              cands.append((i, P))
  # also: extra neighbour with all |P - V_j| <= 1 for j != i (open condition) -- check impossibility
  ok_open = []
  for i in range(3):
      for k in range(20001):
          phi = 2*math.pi*k/20000
          vi = [float(c) for c in V[i]]; P = (vi[0]+math.cos(phi), vi[1]+math.sin(phi))
          r = math.hypot(*P)
          if r > 1+1e-12 or r < 1e-7: continue
          if all(math.dist(P, [float(c) for c in V[j]]) <= 1+1e-12 for j in range(3) if j != i): ok_open.append((i, P))
  print("Case 1: extra neighbours with other distances <= 1:", len(ok_open))
  uniq = []
  for i, P in cands:
      # every other v_j distance must be <= 1 or == sqrt3
      good = True
      for j in range(3):
          if j == i: continue
          d2 = sp.simplify((P-V[j]).dot(P-V[j]))
          if not (d2 == 3 or sp.N(d2) <= 1+1e-12): good = False
      if good and not any(sp.simplify((P-Q).dot(P-Q)) == 0 for _, Q in uniq): uniq.append((i, P))
  print("Case 1 candidate extra neighbours:", [(i, [sp.N(c, 5) for c in P]) for i, P in uniq])
  def compat(P, Q):
      d2 = sp.simplify((P-Q).dot(P-Q))
      return d2 == 3 or sp.N(d2) <= 1+1e-12
  found = False
  for r in range(1, len(uniq)+1):
      for S in itertools.combinations(uniq, r):
          if not all(compat(P, Q) for (_, P), (_, Q) in itertools.combinations(S, 2)): continue
          owners = set()
          for _, P in S:
              for i in range(3):
                  if sp.simplify((P-V[i]).dot(P-V[i])) == 1: owners.add(i)
          if owners == {0, 1, 2}: print("Case 1: all three v_i get degree >= 2 with", S); found = True
  print("Case 1: compatible sets giving every v_i a 2nd neighbour:", "FOUND" if found else "none")
