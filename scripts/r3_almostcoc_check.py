"""Sanity check (floating point, NOT a proof) of the almost-cocircular theorem of angle_R3:
convex P = (subset of R_N) + w points off the circle  =>  #frequent classes F small, k >= m - 24 - 3w/2.
Adversarial: off-circle points chosen among pairwise circle intersections (chord radii) that lie in a cap,
greedily maximising the number of pairs added to chord classes."""
import math, random, itertools, sys
from collections import Counter

def convex_strict(pts):
    # pts must be in strictly convex position (any order): check via hull size
    P = sorted(set(pts))
    if len(P) != len(pts): return False
    def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    lo=[];up=[]
    for p in P:
        while len(lo)>=2 and cross(lo[-2],lo[-1],p) <= 1e-12: lo.pop()
        lo.append(p)
    for p in reversed(P):
        while len(up)>=2 and cross(up[-2],up[-1],p) <= 1e-12: up.pop()
        up.append(p)
    return len(lo)+len(up)-2 == len(P)

def profile(pts, tol=1e-9):
    ds = sorted(math.dist(a,b) for a,b in itertools.combinations(pts,2))
    cls=[]; 
    for d in ds:
        if cls and d-cls[-1][0] < tol: cls[-1][1]+=1
        else: cls.append([d,1])
    return cls

def run(N, holes, w, trials, rng):
    V=[(math.cos(2*math.pi*a/N), math.sin(2*math.pi*a/N)) for a in range(N)]
    chords=[2*math.sin(math.pi*j/N) for j in range(1,N//2+1)]
    worst=None
    for _ in range(trials):
        keep=sorted(rng.sample(range(N), N-holes))
        C=[V[a] for a in keep]
        W=[]
        for _t in range(w):
            best=None
            for _c in range(400):
                a,b=rng.sample(keep,2); r1=rng.choice(chords); r2=rng.choice(chords)
                p,q=V[a],V[b]; d=math.dist(p,q)
                if d==0 or d>r1+r2 or d<abs(r1-r2): continue
                x=(d*d+r1*r1-r2*r2)/(2*d); h2=r1*r1-x*x
                if h2<0: continue
                h=math.sqrt(h2); ex=((q[0]-p[0])/d,(q[1]-p[1])/d)
                for s in (1,-1):
                    u=(p[0]+x*ex[0]-s*h*ex[1], p[1]+x*ex[1]+s*h*ex[0])
                    if abs(math.hypot(*u)-1)<1e-7 or math.hypot(*u)<1e-7: continue
                    if not convex_strict(C+W+[u]): continue
                    hits=sum(1 for c in C if min(abs(math.dist(u,c)-t) for t in chords)<1e-9)
                    if best is None or hits>best[0]: best=(hits,u)
            if best: W.append(best[1])
        pts=C+W; n=len(pts); m=n//2
        cls=profile(pts); D=len(cls); k=sum(1 for d,c in cls if c<=n); F=D-k
        rec=(k-(m-24-1.5*len(W)), N, holes, len(W), n, D, k, F)
        if worst is None or rec<worst: worst=rec
    return worst

if __name__=="__main__":
    rng=random.Random(1)
    print("slack=k-(m-24-1.5w), N, holes, w, n, D, k, F")
    for N in (12,18,24,30,36,42,60):
        for holes in (0,1,3):
            for w in (1,2,3):
                print(run(N,holes,w,6,rng)); sys.stdout.flush()
