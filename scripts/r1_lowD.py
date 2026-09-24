"""Angle R1: certify the low-D instances (n, D, 0) = "Q-colouring using exactly D colours" (ordinal Altman),
built with b3_sat.build(n, D, 0, use_T=False, use_Q=True, order_Q=True), solved by kissat, checked by drat-trim.

Usage: r1_lowD.py OUTDIR n D [timeout=SEC]
"""
import sys, os, time, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from b3_sat import build
from r1_run import DRAT

outdir = sys.argv[1]; n, D = map(int, sys.argv[2:4])
kw = dict(a.split('=', 1) for a in sys.argv[4:]); to = kw.get('timeout', '3600')
tag = f"r1_low_{n}_{D}_0"
cnfp = os.path.join(outdir, tag + ".cnf"); prf = os.path.join(outdir, tag + ".drat")
cnf, pool, _, _ = build(n, D, 0, use_T=False, use_Q=True, order_Q=True)
cnf.to_file(cnfp)
t = time.time()
r = subprocess.run(["kissat", "-q", f"--time={to}", cnfp, prf], capture_output=True, text=True)
st = time.time() - t
status = 'UNSAT' if 's UNSATISFIABLE' in r.stdout else 'SAT' if 's SATISFIABLE' in r.stdout else 'UNKNOWN'
psize = os.path.getsize(prf) if os.path.exists(prf) else 0
verdict, dt = '-', 0.0
if status == 'UNSAT':
    t = time.time()
    d = subprocess.run([DRAT, cnfp, prf, "-t", "40000"], capture_output=True, text=True)
    dt = time.time() - t
    verdict = 'VERIFIED' if '\ns VERIFIED' in '\n' + d.stdout else 'NOT_VERIFIED'
for p in (prf, cnfp):
    if os.path.exists(p): os.remove(p)
print(f"RESULT {tag} n={n} D={D} F=0 {status} solve={st:.1f}s proof={psize} drat={verdict} drat_t={dt:.1f}s", flush=True)
