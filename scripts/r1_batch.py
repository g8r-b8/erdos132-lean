"""Angle R1: run a list of rare-pair cases with at most W concurrent workers (each: solve, then drat-trim).
Stops launching new cases if free disk on /System/Volumes/Data drops below 3 GB.

Usage: r1_batch.py OUTDIR n D W [sb=Dmax] [timeout=SEC] [skip=a b,c d,...] [only=a b,...]
Appends RESULT lines to OUTDIR/batch_n{n}.log.
"""
import sys, os, shutil, itertools
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))


def free_gb():
    return shutil.disk_usage("/System/Volumes/Data").free / 2**30


def main():
    outdir = sys.argv[1]; n, D, W = map(int, sys.argv[2:5])
    kw = dict(a.split('=', 1) for a in sys.argv[5:])
    cases = list(itertools.combinations(range(1, D + 1), 2))
    if 'only' in kw: cases = [tuple(map(int, s.split())) for s in kw['only'].split(',')]
    if 'skip' in kw:
        sk = {tuple(map(int, s.split())) for s in kw['skip'].split(',')}
        cases = [c for c in cases if c not in sk]
    # hardest first (cases containing the diameter colour D were the slow ones at n = 13)
    cases.sort(key=lambda c: (D not in c, c))
    log = os.path.join(outdir, f"batch_n{n}.log")
    sb = kw.get('sb'); to = kw.get('timeout', '3600')

    def one(c):
        if free_gb() < 3.0:
            line = f"SKIPPED {c} low disk {free_gb():.1f} GB"
        else:
            args = ["uv", "run", "-q", "--with", "python-sat", "python", os.path.join(HERE, "r1_run.py"), outdir,
                    str(n), str(D), str(c[0]), str(c[1]), f"timeout={to}"]
            tag = f"r1_{n}_{D}_{c[0]}{c[1]}" + ("_sb" if sb else "")
            args += [f"tag={tag}"] + ([f"sb={sb}"] if sb else [])
            r = subprocess.run(args, capture_output=True, text=True)
            line = (r.stdout.strip() or f"ERROR {c} {r.stderr[-500:]}")
        with open(log, "a") as f: f.write(line + "\n")
        return line

    with ThreadPoolExecutor(max_workers=W) as ex:
        for line in ex.map(one, cases):
            print(line, flush=True)


if __name__ == '__main__':
    main()
