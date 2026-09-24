"""R5/B: numerical scan of the "core configuration" (the only case left open in the proof of the
Charge Lemma).  Hook 1 (p,w,x;b) plus a unit neighbour u of x on the far side of line xw forces
(Trapezoid Lemma) x=(-s,0), p=(s,0), u=(-t,-d), b=(t,-d), w=(0,-k), Delta^2 = 1+4st.
We look for hook 2 (p',u,x;b') with p' on w's side of line xu (same orientation at x), b' on the far
side of line p'u from x, p', p, x extreme, correct angular order at p and p', and a third
neighbour c' of p' on x's side of line p'u (needed: u must be a middle neighbour of p').
Grid over (s,t) incl. the strata 2t=1, 2s=Delta, 2t=Delta; p' angles on a grid plus all
'special' angles where |p'q| in {1, Delta}; c' likewise.  Float guidance only.
usage: python3 r5_b_core.py N   (grid resolution)
"""
import math, sys
from collections import Counter
def cr(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def cc(p,q,r1,r2):
    d=math.dist(p,q)
    if d<1e-12 or d>r1+r2+1e-12 or d<abs(r1-r2)-1e-12: return []
    a=(r1*r1-r2*r2+d*d)/(2*d); h=math.sqrt(max(r1*r1-a*a,0)); ux,uy=(q[0]-p[0])/d,(q[1]-p[1])/d
    return [(p[0]+a*ux-h*uy,p[1]+a*uy+h*ux),(p[0]+a*ux+h*uy,p[1]+a*uy-h*ux)]
TOL=1e-7
def good(d,Dl): return d<=1+TOL or abs(d-Dl)<TOL
def base(s,t):
    if not (0<s<1 and 0<t and abs(t-s)<1): return None
    d=math.sqrt(1-(t-s)**2); k=math.sqrt(1-s*s)
    Dl=math.sqrt(1+4*s*t)
    x=(-s,0.0); p=(s,0.0); w2=(-t,-d); b=(t,-d); w=(0.0,-k)
    if not (cr(x,w,w2)*cr(x,w,p)<0 and cr(p,w,x)*cr(p,w,b)<0): return None
    P=[x,p,b,w,w2]
    for i in range(5):
        for j in range(i+1,5):
            if not good(math.dist(P[i],P[j]),Dl): return None
    return Dl,P
def merge(pts):
    out=[]
    for q in pts:
        if all(math.dist(q,r)>1e-7 for r in out): out.append(q)
    return out
def extreme(q,pts):
    angs=sorted(math.atan2(r[1]-q[1],r[0]-q[0]) for r in pts if math.dist(q,r)>1e-7)
    if len(angs)<2: return True
    gaps=[(angs[(i+1)%len(angs)]-angs[i])%(2*math.pi) for i in range(len(angs))]
    return max(gaps)>math.pi+1e-9
def order_ok(p,b,w,x,pts):
    """b,w are the first two unit-nbrs of p counted from b's side, and x,b opposite wrt line pw,
       and p has some unit nbr on x's side (not required: may be outside the configuration)"""
    nb=[q for q in pts if abs(math.dist(q,p)-1)<TOL]
    # angular order inside p's half-plane
    ang=lambda q: math.atan2(q[1]-p[1],q[0]-p[0])
    s=sorted(nb,key=ang)
    gaps=[(ang(s[(i+1)%len(s)])-ang(s[i]))%(2*math.pi) for i in range(len(s))]
    i0=max(range(len(s)),key=lambda i:gaps[i]); o=s[i0+1:]+s[:i0+1]
    if o[-1]==b or (len(o)>1 and o[-1] is not None and math.dist(o[-1],b)<1e-7): o=o[::-1]
    return math.dist(o[0],b)<1e-7 and math.dist(o[1],w)<1e-7
def check(Dl,P,al,C):
    x,p,b,w,w2=P
    p2=(w2[0]+math.cos(al),w2[1]+math.sin(al))
    if cr(x,w2,p2)*cr(x,w2,w)<=1e-12: return False
    if not all(good(math.dist(q,p2),Dl) for q in P): return False
    for b2 in cc(p2,x,1.0,Dl):
        if cr(p2,w2,b2)*cr(p2,w2,x)>=-1e-12: continue
        if not all(good(math.dist(q,b2),Dl) for q in P+[p2]): continue
        pts=merge(P+[p2,b2])
        if len(pts)<len(P)+2: C['coinc']+=1
        if not (extreme(p,pts) and extreme(p2,pts) and extreme(x,pts)): C['nonext']+=1; continue
        if not order_ok(p,b,w,x,pts): C['order1']+=1; continue
        if not order_ok(p2,b2,w2,x,pts): C['order2']+=1; continue
        return (p2,b2)
    return False
from collections import Counter
def cands(p,w,x,pts,Dl,M=1440):
    out=[]
    for a in range(M):
        c=(p[0]+math.cos(2*math.pi*a/M),p[1]+math.sin(2*math.pi*a/M))
        if cr(p,w,c)*cr(p,w,x)<=1e-9 or math.dist(c,w)<1e-6: continue
        if all(good(math.dist(c,q),Dl) for q in pts if math.dist(c,q)>1e-7): out.append(c)
    # special points: circle intersections with Delta / unit circles of existing points
    for q in pts:
        for r in (1.0,Dl):
            for c in cc(p,q,1.0,r):
                if cr(p,w,c)*cr(p,w,x)<=1e-9 or math.dist(c,w)<1e-6: continue
                if all(good(math.dist(c,q2),Dl) for q2 in pts if math.dist(c,q2)>1e-7): out.append(c)
    return out
if __name__=='__main__':
    N=int(sys.argv[1]); C=Counter(); hits=[]
    for i in range(1,N):
        s=i/N
        tvals=[2*j/N for j in range(1,N)]+[0.5,(4*s+math.sqrt(16*s*s+16))/8]+([(4*s*s-1)/(4*s)] if s>0.5 else [])
        for t in tvals:
            B=base(s,t)
            if B is None: continue
            Dl,P=B; x,p,b,w,w2=P
            als=[2*math.pi*a/360 for a in range(360)]
            for q in P:
                if q is w2: continue
                for r in (Dl,1.0):
                    for z in cc(w2,q,1.0,r): als.append(math.atan2(z[1]-w2[1],z[0]-w2[0]))
            for al in als:
                h=check(Dl,P,al,C)
                if not h: continue
                p2,b2=h; pts=merge(P+[p2,b2])
                C['pair']+=1
                c1=cands(p,w,x,pts,Dl)
                if not c1: C['no c']+=1; continue
                c2=cands(p2,w2,x,pts,Dl)
                if not c2: C['no c2']+=1; continue
                ok=False
                for u in c1:
                    for v in c2:
                        dd=math.dist(u,v)
                        if dd<1e-7 or good(dd,Dl):
                            X=merge(pts+[u,v])
                            if extreme(p,X) and extreme(p2,X) and extreme(x,X): ok=(u,v); break
                    if ok: break
                if ok: C['HIT']+=1; hits.append((s,t,al,pts,ok))
                else: C['c-c2 incompatible']+=1
    print(dict(C))
    for h in hits[:3]: print(h)
