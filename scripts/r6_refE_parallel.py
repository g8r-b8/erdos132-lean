"""R6-REF-E: high-precision (mpmath, 40 digits) check of GAP §3 Steps 1-2 on random / adversarial ball polygons.
K_rho = ∩_w D(w, rho). Boundary arc of circle i = normal-angle interval; ∂K has length rho * (measure of arc normals).
Checks: (1) K' arc normal-sets ⊂ K arc normal-sets of the same circle (offset structure, Step 1);
(2) per K' = (r-t)/r (per K - Σ_c len Z_c) with len Z_c = r*|K-arc normals ∩ N_{K'}(c)|;
(3) len Z_c <= 2 t tan(psi_c/2) (Step 2); (4) sin(psi/2) = |w1 w2|/(2(r-t)); (5) Σ Z_c <= 21 t when diam W <= 1.94 r."""
import random, mpmath as mp
mp.mp.dps = 40
TWO_PI = 2*mp.pi
def arcs(W, rho):
    out = []
    for i, wi in enumerate(W):
        lo, hi, ok = None, None, True
        ref = None
        for j, wj in enumerate(W):
            if j == i: continue
            dx, dy = wj[0]-wi[0], wj[1]-wi[1]; d = mp.sqrt(dx*dx+dy*dy)
            if d == 0: continue
            if d >= 2*rho: return None
            phi = mp.atan2(dy, dx); a = mp.acos(d/(2*rho))
            if ref is None: ref = phi
            c = ref + ((phi-ref+mp.pi) % TWO_PI) - mp.pi
            l, h = c-a, c+a
            lo = l if lo is None else max(lo, l); hi = h if hi is None else min(hi, h)
            if lo >= hi: ok = False; break
        if ok and lo is not None: out.append((i, lo % TWO_PI, hi-lo))
    out.sort(key=lambda x: x[1]); return out
def measure_in(arcsK, a0, length):
    """measure of union of K arc-normal intervals inside [a0, a0+length] (mod 2pi)"""
    tot = mp.mpf(0)
    for (_, lo, L) in arcsK:
        for sh in (-TWO_PI, 0, TWO_PI):
            s, e = lo+sh, lo+sh+L
            ov = min(e, a0+length) - max(s, a0)
            if ov > 0: tot += ov
    return tot
def check(W, r, t, label, maxnorm=True):
    AK, AKp = arcs(W, r), arcs(W, r-t)
    if not AK or not AKp or len(AKp) < 2: return None
    # (1) containment of normal sets per circle
    dK = {i: (lo, L) for i, lo, L in AK}
    for i, lo, L in AKp:
        assert i in dK, "K' arc on circle absent from K"
        lo0, L0 = dK[i]; off = (lo-lo0) % TWO_PI
        assert off >= -mp.mpf(10)**-30 and off+L <= L0+mp.mpf(10)**-30, "containment fails"
    perK = r*sum(L for _, _, L in AK); perKp = (r-t)*sum(L for _, _, L in AKp)
    Ztot, worst = mp.mpf(0), mp.mpf(0)
    m = len(AKp)
    for k in range(m):
        i, lo, L = AKp[k]; j, lo2, _ = AKp[(k+1) % m]
        a0 = lo+L; psi = (lo2-a0) % TWO_PI
        Z = r*measure_in(AK, a0, psi); Ztot += Z
        bound = 2*t*mp.tan(psi/2)
        assert Z <= bound + mp.mpf(10)**-25, ("collapse bound fails", Z, bound)
        wi, wj = W[i], W[j]; d = mp.sqrt((wi[0]-wj[0])**2+(wi[1]-wj[1])**2)
        assert abs(mp.sin(psi/2) - d/(2*(r-t))) < mp.mpf(10)**-25, "psi identity fails"
        if bound > 0: worst = max(worst, Z/bound)
    ident = perKp - (r-t)/r*(perK - Ztot)
    assert abs(ident) < mp.mpf(10)**-25, ("parallel-body identity fails", ident)
    return Ztot/t, worst
random.seed(1)
r = mp.mpf(10000); worstZt, worstratio, cnt = 0, 0, 0
for trial in range(300):
    k = random.randint(2, 12); mode = trial % 3
    if mode == 0:   # random centres in a disk of radius 0.6 r
        W = []
        while len(W) < k:
            x, y = random.uniform(-.6, .6), random.uniform(-.6, .6)
            if x*x+y*y < .36: W.append((mp.mpf(x)*r, mp.mpf(y)*r))
    elif mode == 1: # lens-type: two far centres at distance up to 1.94 r plus a few
        d = mp.mpf(random.uniform(1.5, 1.94))*r
        W = [(-d/2, mp.mpf(0)), (d/2, mp.mpf(0))] + [(mp.mpf(random.uniform(-.3, .3))*r, mp.mpf(random.uniform(-.2, .2))*r) for _ in range(k-2)]
    else:           # Reuleaux-like: centres near a circle of radius ~0.56 r (diam ~1.12r .. ) and some on 0.97r
        R0 = random.uniform(.5, .97)
        W = [(mp.mpf(R0*mp.cos(2*mp.pi*s/k+random.uniform(0, .05)))*r, mp.mpf(R0*mp.sin(2*mp.pi*s/k+random.uniform(0, .05)))*r) for s in range(k)]
    diam = max(mp.sqrt((a[0]-b[0])**2+(a[1]-b[1])**2) for a in W for b in W)
    if diam > mp.mpf('1.94')*r: continue
    for tt in (1, 20, 50):
        res = check(W, r, mp.mpf(tt), f"t{trial}")
        if res is None: continue
        cnt += 1; worstZt = max(worstZt, res[0]); worstratio = max(worstratio, res[1])
print(f"checked {cnt} (config,t) pairs: all identities hold at 1e-25;"
      f" max Σ Z_c / t = {mp.nstr(worstZt, 6)} (claim <= 21); max Z_c/(2t tan(psi/2)) = {mp.nstr(worstratio, 6)}")
# tan constant: tan(x) <= k x on x <= 77.2 deg
x = mp.asin(mp.mpf('0.975')); print("psi/2 max =", mp.nstr(mp.degrees(x), 6), "deg; tan(x)/x =", mp.nstr(mp.tan(x)/x, 6),
      "; 2*max tan(psi/2)/psi*2pi =", mp.nstr(2*mp.tan(x)/(2*x)*2*mp.pi, 6))
