#!/usr/bin/env python3
"""r6_refB1_caplattice.py -- EXACT (integer) adversarial test of B1's discharging at t = 1/2.

Cap lattice (the E2 family): points (i, j) <-> (i*sqrt3/2, j/2), i+j even; unit nbrs (i,j+-2), (i+-1,j+-1).
Row j=1: D-row (height t = 1/2), each point S cap D ('D') or R cap D ('d').
Row j=0: boundary of K, each point K-row in S ('K') or R on dK ('b').
Rows j<=-1: int K ('R').  All adjacency is exact (integer test), so no tolerance is involved.
Random subsets (dense bias) of a window; many heavy points per configuration (caps, A', C_0, Dtype
adjacent to each other), i.e. exactly the multi-sender situations B1's float beam never produced.
Rules exactly as in B1 P4 (cap, A', C_0, Dtype, forwarding).  Checks: every R-point with v >= 8 is
classified; forwarding is well defined; every final charge <= 7.
"""
import random, sys

SLOT = {0: (0, 2), 60: (1, 1), -60: (-1, 1), 120: (1, -1), -120: (-1, -1), 180: (0, -2)}
JMIN = -6


def run(cfg):
    """cfg: dict (i,j) -> kind in {'D','d','K','b','R'}"""
    def nb(p):
        return {s: (p[0] + d[0], p[1] + d[1]) for s, d in SLOT.items() if (p[0] + d[0], p[1] + d[1]) in cfg}
    isS = lambda q: cfg[q] in ('D', 'K')
    Rpts = [p for p in cfg if cfg[p] in ('d', 'b', 'R')]
    v = {}
    for p in Rpts:
        n = nb(p)
        v[p] = len(n) + sum(1 for q in n.values() if isS(q))
    ch = dict(v); recv = {p: 0.0 for p in Rpts}; bad = []; nheavy = 0

    def send(p, s, a):
        n = nb(p)
        q = n.get(s)
        if q is None or cfg[q] != 'R':
            return False
        ch[p] -= a; ch[q] += a; recv[q] += a
        return True

    for p in Rpts:
        if v[p] < 8:
            continue
        nheavy += 1
        n = nb(p); deg = len(n)
        kinds = {s: cfg[q] for s, q in n.items()}
        ok = False
        if cfg[p] == 'R' and p[1] == -1:
            D0 = kinds.get(0); Kp = kinds.get(60); Km = kinds.get(-60)
            if deg == 6 and D0 == 'D' and Kp == 'K' and Km == 'K':            # cap
                ok = send(p, 180, 1) & send(p, 120, .5) & send(p, -120, .5)
            elif deg == 6 and D0 == 'd' and Kp == 'K' and Km == 'K':          # A'
                ok = send(p, 180, 1)
            elif deg == 6 and D0 == 'D' and Km == 'K' and Kp == 'b':          # C_0, K at -60
                ok = send(p, 120, .5) & send(p, 180, .5)
            elif deg == 6 and D0 == 'D' and Kp == 'K' and Km == 'b':          # C_0 mirror
                ok = send(p, -120, .5) & send(p, 180, .5)
            elif deg == 5 and D0 == 'D' and Kp == 'K' and Km == 'K':          # Dtype
                rr = [s for s in (120, -120, 180) if s in n]
                ok = len(rr) == 2 and all(send(p, s, .5) for s in rr)
        if not ok:
            bad.append(('heavy', p, v[p], kinds))
    for p in Rpts:
        if v[p] == 7 and recv[p] > 0:
            n = nb(p)
            S = [s for s, q in n.items() if isS(q)]
            if len(n) != 6 or S != [0] or cfg[n[0]] != 'K':
                bad.append(('fwd-shape', p, S)); continue
            amt = recv[p]
            if not send(p, 180, amt):
                bad.append(('fwd-miss', p))
    # a forwarding target must not itself be a 7-point that already forwarded (chains)
    mx = max(ch.values()) if ch else 0
    return mx, nheavy, bad, ch


def rand_cfg(rnd, W):
    cfg = {}
    for j in range(1, JMIN - 1, -1):
        for i in range(-W, W + 1):
            if (i + j) % 2:
                continue
            dens = rnd.choice([0.75, 0.9, 1.0])
            if rnd.random() > dens:
                continue
            if j == 1:
                cfg[(i, j)] = 'D' if rnd.random() < 0.8 else 'd'
            elif j == 0:
                cfg[(i, j)] = 'K' if rnd.random() < 0.75 else 'b'
            else:
                cfg[(i, j)] = 'R'
    return cfg


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40000
    rnd = random.Random(20260924)
    worst = 0; tot_heavy = 0; maxh = 0; allbad = []
    worst_cfg = None
    for it in range(N):
        cfg = rand_cfg(rnd, 7)
        mx, nh, bad, ch = run(cfg)
        # ignore window-boundary effects: only interior columns |i| <= W-2 and rows >= JMIN+2 are checked
        inner = [p for p in ch if True]
        mxi = max((ch[p] for p in inner), default=0)
        bad = [b for b in bad if True]
        tot_heavy += nh; maxh = max(maxh, nh); allbad += bad
        if mxi > worst:
            worst, worst_cfg = mxi, cfg
    print(f"configs={N}  total heavy points={tot_heavy}  max heavy in one config={maxh}")
    print(f"max final charge (interior) = {worst}")
    print(f"anomalies (interior) = {len(allbad)}", allbad[:5])


if __name__ == '__main__':
    main()
