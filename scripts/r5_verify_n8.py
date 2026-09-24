"""R5: independent EXACT check of the n=8 set with mu(Delta2)=mu(Delta3)=9 > 8 (found by R5/A,
recipe scratchpad/R5/A/n8.json).  Coordinates (identified by PSLQ, then taken as exact definitions):
  P_k = (cos 2pi k/5, sin 2pi k/5), k=0..4, and with s3=sqrt3, s5=sqrt5, w=sqrt(10+2s5), w2=sqrt(10-2s5):
  p5 = ((3 - s5 + s3 w2)/8, (5 s3 + s3 s5 + w2)/8)
  p6 = ((3 + s5 - s3 w)/8,  (5 s3 - s3 s5 - w)/8)
  p7 = ((-1 - s5 + s3 w2)/4, 0)
The script proves exactly (sympy minimal polynomials of differences):
 (i) the recipe's circle conditions hold (|p5P0|=|p5P2|=|P0P2|, |p6P0|=|P0P1|, |p6P1|=|P1p5|,
     |p7P0|=|P2p6|, |p7P1|=|P1p5|), so this is the recipe's set;
 (ii) the squared-distance multiset is (Delta:2, Delta2:9, Delta3:9, 5, 2, 1): each within-group equality
     is exact; distinct groups are separated by > 0.1 at 50 digits (distinct algebraic numbers).
Run: .venv/bin/python problems/132/scripts/r5_verify_n8.py"""
import sympy as sp, itertools
x=sp.Symbol('x'); s3,s5=sp.sqrt(3),sp.sqrt(5)
w=sp.sqrt(10+2*s5); w2=sp.sqrt(10-2*s5)
c1,c2=(s5-1)/4,-(s5+1)/4; si1,si2=w/4,w2/4       # cos/sin of 72 and 144 degrees
P=[(1,0),(c1,si1),(c2,si2),(c2,-si2),(c1,-si1)]
P+=[((3-s5+s3*w2)/8,(5*s3+s3*s5+w2)/8),((3+s5-s3*w)/8,(5*s3-s3*s5-w)/8),((-1-s5+s3*w2)/4,0)]
def sq(a,b): return sp.expand((P[a][0]-P[b][0])**2+(P[a][1]-P[b][1])**2)
def eq(e,f): return sp.minimal_polynomial(sp.expand(e-f),x)==x
for (a,b),(c,d) in [((5,0),(0,2)),((5,2),(0,2)),((6,0),(0,1)),((6,1),(1,5)),((7,0),(2,6)),((7,1),(1,5))]:
    assert eq(sq(a,b),sq(c,d)),(a,b,c,d)
print("recipe conditions: exact OK")
D={(i,j):sq(i,j) for i,j in itertools.combinations(range(8),2)}
vals=sorted({round(float(sp.N(e,50)),10) for e in D.values()},reverse=True)
out=[]
for v in vals:
    g=[e for e in D.values() if round(float(sp.N(e,50)),10)==v]
    assert all(eq(e,g[0]) for e in g[1:])
    out.append((v,len(g)))
gaps=min(vals[i]-vals[i+1] for i in range(len(vals)-1))
print("spectrum (sq-dist, mult):",out,"min gap",gaps)
m=[k for _,k in out]; assert sum(m)==28 and m[1]==9 and m[2]==9
print("n=8: mu(Delta2)=9>8, mu(Delta3)=9>8  [exact]")
