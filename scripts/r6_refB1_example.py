#!/usr/bin/env python3
"""r6_refB1_example.py -- explicit exact (integer / Q(sqrt3)) worst-pressure example at t = 1/2.
Receiver x = (0,-2) (depth 1) fed by a cap at (-1,-1) and a Dtype at (1,-1), with K-row point (0,0) above x,
so x is a 7-point that forwards 1 to (0,-4) (depth 2).  Full D-row / K-row / interior rows otherwise."""
import importlib.util, os
spec = importlib.util.spec_from_file_location("cl", os.path.join(os.path.dirname(os.path.abspath(__file__)), "r6_refB1_caplattice.py"))
cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
cfg = {}
for j in range(1, -7, -1):
    for i in range(-6, 7):
        if (i + j) % 2 == 0:
            cfg[(i, j)] = 'D' if j == 1 else ('K' if j == 0 else 'R')
del cfg[(2, -2)]          # makes (1,-1) a Dtype (deg 5, m 3) sending to x=(0,-2) and (1,-3)
del cfg[(-3, -1)]         # isolate: (-2,0) side irrelevant; keep cap at (-1,-1) intact
mx, nh, bad, ch = cl.run(cfg)
for p in [(-1, -1), (1, -1), (0, -2), (0, -4), (-1, -3), (1, -3), (-2, -2)]:
    print(p, "final", ch.get(p))
print("heavy:", nh, " max final:", mx, " anomalies:", bad)
