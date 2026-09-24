"""Angle R1 runner: build case CNF (r1_sat_split.build), solve with proof, check with drat-trim, delete proof.

Usage:
  r1_run.py OUTDIR n D r1 r2 [solver=kissat|cadical] [timeout=SEC] [check=1|0] [cube=...] [tag=...] [sb=Dmax]
Prints one line:  RESULT tag n D r1 r2 status solve_s proof_bytes drat_verdict drat_s
"""
import sys, os, time, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r1_sat_split import build, parse_cube

DRAT = "scratch/drat-trim/drat-trim"


def run(outdir, n, D, r1, r2, solver='kissat', timeout=3600, check=True, cube=(), tag=None, dtimeout=40000, sb=None):
    tag = tag or f"r1_{n}_{D}_{r1}{r2}"
    cnfp = os.path.join(outdir, tag + ".cnf"); prf = os.path.join(outdir, tag + ".drat")
    cnf, pool, pairs, X = build(n, D, (r1, r2), cube, sb)
    cnf.to_file(cnfp)
    t = time.time()
    if solver == 'kissat':
        cmd = ["kissat", "-q", f"--time={timeout}", cnfp] + ([prf] if check else [])
    else:
        cmd = ["cadical", "-q", "-t", str(timeout), cnfp] + ([prf] if check else [])
    r = subprocess.run(cmd, capture_output=True, text=True)
    st = time.time() - t
    status = 'UNSAT' if 's UNSATISFIABLE' in r.stdout else 'SAT' if 's SATISFIABLE' in r.stdout else 'UNKNOWN'
    psize = os.path.getsize(prf) if (check and os.path.exists(prf)) else 0
    verdict, dt = '-', 0.0
    if status == 'UNSAT' and check:
        t = time.time()
        d = subprocess.run([DRAT, cnfp, prf, "-t", str(dtimeout)], capture_output=True, text=True)
        dt = time.time() - t
        verdict = 'VERIFIED' if '\ns VERIFIED' in '\n' + d.stdout else 'NOT_VERIFIED'
        if verdict != 'VERIFIED':
            with open(os.path.join(outdir, tag + ".dratlog"), "w") as f: f.write(d.stdout[-5000:] + d.stderr[-2000:])
    if status == 'SAT':
        with open(os.path.join(outdir, tag + ".model"), "w") as f: f.write(r.stdout)
    for p in (prf, cnfp):
        if os.path.exists(p): os.remove(p)
    line = f"RESULT {tag} n={n} D={D} rare={r1},{r2} sb={sb} cube={len(cube)} {status} solve={st:.1f}s proof={psize} drat={verdict} drat_t={dt:.1f}s"
    print(line, flush=True)
    return status, verdict


if __name__ == '__main__':
    outdir = sys.argv[1]; n, D, r1, r2 = map(int, sys.argv[2:6])
    kw = dict(a.split('=', 1) for a in sys.argv[6:])
    run(outdir, n, D, r1, r2, solver=kw.get('solver', 'kissat'), timeout=int(kw.get('timeout', 3600)),
        check=kw.get('check', '1') == '1', cube=parse_cube(kw['cube'], n) if 'cube' in kw else (),
        tag=kw.get('tag'), sb=kw.get('sb'))
