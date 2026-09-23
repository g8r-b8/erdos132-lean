"""Re-certify B3 refutations with drat-trim (independent of our own RUP checker).
Usage: python b3_drat_trim.py OUTDIR n D F [TQ|Q]
Writes OUTDIR/<tag>.cnf and OUTDIR/<tag>.drup (Glucose 4 DRUP proof). OUTDIR/<tag>.lrat is written later by drat-trim -L."""
import sys, os, time
from pysat.solvers import Solver
from b3_sat import build

out = sys.argv[1]; n, D, F = map(int, sys.argv[2:5]); only = sys.argv[5] if len(sys.argv) > 5 else 'TQ'
tag = f"b3_{n}_{D}_{F}_{only}"
cnf, pool, _, _ = build(n, D, F, use_T='T' in only, use_Q='Q' in only, order_Q=True)
cnf.to_file(os.path.join(out, tag + ".cnf"))
t = time.time()
with Solver(name='glucose4', bootstrap_with=cnf.clauses, with_proof=True) as s:
    r = s.solve(); proof = s.get_proof()
assert not r, "instance is SAT"
with open(os.path.join(out, tag + ".drup"), "w") as f:
    f.write("\n".join(proof) + "\n")
print(tag, "UNSAT", len(proof), "proof lines", f"{time.time()-t:.1f}s")
