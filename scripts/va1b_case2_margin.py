"""Ve87 Case 2 with margins. q=0, Delta2=1, v1=(-1,0), v2,v3=(cos a, +-sin a), a in (0,30deg], Delta=2cos(a/2).
For r on circle(v1,1) cap unit disk, r != 0: report
  open branch margin  m_open(a) = min_r max(|r-v2|,|r-v3|) - 1   (>0 means no r with both <= 1)
  equality branch: for r with |r-v2| = Delta exactly, gap of |r-v3| from the allowed set [0,1] U {Delta}."""
import math
from va1b_cases import circ
mo, me = 9, 9
for k in range(1, 3001):
    a = math.radians(30)*k/3000; D = 2*math.cos(a/2)
    v1=(-1.,0.); v2=(math.cos(a),math.sin(a)); v3=(math.cos(a),-math.sin(a))
    best = 9
    for j in range(20001):
        phi = -math.pi/3 + (2*math.pi/3)*j/20000
        r = (v1[0]+math.cos(phi), v1[1]+math.sin(phi)); n = math.hypot(*r)
        if n > 1+1e-12 or n < 1e-6: continue
        best = min(best, max(math.dist(r,v2), math.dist(r,v3)) - 1)
    mo = min(mo, best)
    for r in circ(v1, 1.0, v2, D):
        n = math.hypot(*r)
        if n > 1+1e-12 or n < 1e-6: continue
        d3 = math.dist(r, v3); gap = min(d3-1 if d3 > 1 else -1, abs(d3-D)) if d3 > 1 else -1
        me = min(me, gap)
print("Case 2 open-branch min margin over a in (0,30]: %.6f" % mo)
print("Case 2 equality-branch min gap (|r-v3| from {<=1, Delta}): %s" % ("no r in disk at all" if me == 9 else "%.6f" % me))
