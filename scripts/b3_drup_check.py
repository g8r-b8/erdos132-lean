"""Angle B3: produce and independently check a DRUP refutation for the SAT instances of b3_sat.py.

Pipeline:
  1. build the CNF with b3_sat.build(...) (the encoding is the only thing that must be trusted);
  2. solve with Glucose 4 (via PySAT) with proof logging -> DRUP proof (lemmas + deletions);
  3. check the proof with the small forward RUP checker below (pure Python, independent of the solver):
     every lemma must be a reverse-unit-propagation consequence of the original clauses plus earlier lemmas,
     and the final clause database must be refuted by unit propagation.
     Deletions are IGNORED (keeping more clauses is sound: every kept clause is implied by the original CNF).

Usage: b3_drup_check.py n D F [TQ|Q]    (uses the compact order encoding of (Q))
       b3_drup_check.py selftest
"""
import sys, time
from b3_sat import build
from pysat.solvers import Solver


class RUP:
    def __init__(self, nvars):
        self.val = [0] * (nvars + 1)          # +1 true, -1 false, 0 unassigned (for variables)
        self.clauses = []
        self.watch = {}                       # literal -> list of clause ids watching it
        self.trail = []
        self.qhead = 0
        self.inconsistent = False

    def value(self, lit):
        v = self.val[abs(lit)]
        return v if lit > 0 else -v

    def assign(self, lit):
        self.val[abs(lit)] = 1 if lit > 0 else -1
        self.trail.append(lit)

    def propagate(self):
        """Unit propagation from qhead.  Returns True on conflict."""
        val = self.val; clauses = self.clauses; watch = self.watch
        while self.qhead < len(self.trail):
            lit = self.trail[self.qhead]; self.qhead += 1
            false_lit = -lit
            ws = watch.get(false_lit)
            if not ws:
                continue
            i = 0
            while i < len(ws):
                cid = ws[i]; c = clauses[cid]
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                other = c[0]
                ov = val[abs(other)]; ov = ov if other > 0 else -ov
                if ov == 1:
                    i += 1; continue
                found = False
                for k in range(2, len(c)):
                    l = c[k]; lv = val[abs(l)]; lv = lv if l > 0 else -lv
                    if lv != -1:
                        c[1], c[k] = c[k], c[1]
                        watch.setdefault(c[1], []).append(cid)
                        ws[i] = ws[-1]; ws.pop()
                        found = True; break
                if found:
                    continue
                if ov == -1:
                    return True
                self.assign(other)
                i += 1
        return False

    def add(self, clause):
        """Add a clause to the database (top level).  Returns True if the database became inconsistent."""
        c = list(dict.fromkeys(clause))
        if any(-l in c for l in c):
            return False  # tautology
        if not c:
            self.inconsistent = True; return True
        # order: non-false literals first
        c.sort(key=lambda l: -self.value(l))
        if self.value(c[0]) == 1:
            pass
        elif len(c) == 1 or self.value(c[1]) == -1:
            if self.value(c[0]) == -1:
                self.inconsistent = True; return True
            self.assign(c[0])
            if self.propagate():
                self.inconsistent = True; return True
        if len(c) >= 2:
            cid = len(self.clauses); self.clauses.append(c)
            self.watch.setdefault(c[0], []).append(cid)
            self.watch.setdefault(c[1], []).append(cid)
        return False

    def is_rup(self, clause):
        if self.inconsistent:
            return True
        save_trail, save_q = len(self.trail), self.qhead
        conflict = False
        for l in clause:
            v = self.value(l)
            if v == 1:
                conflict = True; break
            if v == 0:
                self.assign(-l)
        if not conflict:
            conflict = self.propagate()
        for l in self.trail[save_trail:]:
            self.val[abs(l)] = 0
        del self.trail[save_trail:]
        self.qhead = save_q
        return conflict


def check(cnf_clauses, proof_lines, nvars):
    chk = RUP(nvars)
    for c in cnf_clauses:
        if chk.add(c):
            return True, 0
    nl = 0
    for line in proof_lines:
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('d'):
            continue  # ignore deletions (sound)
        lits = [int(x) for x in line.split()]
        assert lits[-1] == 0
        lits = lits[:-1]
        if not chk.is_rup(lits):
            raise AssertionError(f"lemma {nl} is not RUP: {lits}")
        nl += 1
        if chk.add(lits):
            return True, nl
    return chk.inconsistent, nl


def selftest():
    """The checker must reject: an empty proof of a satisfiable instance, a proof with one lemma negated,
    and a truncated proof."""
    cnf, pool, _, _ = build(7, 4, 1, use_T=False, order_Q=True)          # satisfiable
    try:
        check(cnf.clauses, ["0"], pool.top); raise SystemExit("selftest FAILED: accepted bogus proof")
    except AssertionError:
        pass
    cnf, pool, _, _ = build(7, 4, 2, use_T=False, order_Q=True)          # unsatisfiable
    with Solver(name='glucose4', bootstrap_with=cnf.clauses, with_proof=True) as s:
        s.solve(); pr = s.get_proof()
    lem = [i for i, l in enumerate(pr) if not l.startswith('d') and len(l.split()) > 3]
    bad = list(pr); i = lem[len(lem) // 2]
    bad[i] = ' '.join(str(-int(x)) if x != '0' else x for x in bad[i].split())
    try:
        check(cnf.clauses, bad, pool.top); raise SystemExit("selftest FAILED: accepted mutated proof")
    except AssertionError:
        pass
    assert check(cnf.clauses, pr[:len(pr) // 2], pool.top)[0] is False
    assert check(cnf.clauses, pr, pool.top)[0] is True
    print("selftest passed (bogus, mutated and truncated proofs rejected; genuine proof accepted)")


if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest(); sys.exit(0)
    n, D, F = map(int, sys.argv[1:4]); only = sys.argv[4] if len(sys.argv) > 4 else 'TQ'
    cnf, pool, pairs, X = build(n, D, F, use_T='T' in only, use_Q='Q' in only, order_Q=True)
    t = time.time()
    with Solver(name='glucose4', bootstrap_with=cnf.clauses, with_proof=True) as s:
        r = s.solve(); proof = s.get_proof()
    print(f"n={n} D={D} F={F} [{only} order]: {pool.top} vars, {len(cnf.clauses)} clauses; glucose4:",
          "SAT" if r else "UNSAT", f"proof {len(proof)} lines, {time.time() - t:.1f}s", flush=True)
    if r:
        sys.exit(0)
    t = time.time()
    ok, nl = check(cnf.clauses, proof, pool.top)
    print(f"  independent RUP check: {'REFUTATION VERIFIED' if ok else 'FAILED (no final conflict)'}; "
          f"{nl} lemmas checked, {time.time() - t:.1f}s")
