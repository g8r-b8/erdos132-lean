#!/usr/bin/env bash
# Angle B3: reproduce every computation quoted in angle_B3.md.  Run from problems/132/scripts.
# Needs uv (pulls python-sat).  Rough total time: n<=11 parts ~15 min; n=13 ~5 min; (15,8,6) long.
set -e
PY="uv run --with python-sat python"
echo "## validation"; python3 b3_validate.py 7 11; $PY b3_drup_check.py selftest
echo "## n=7 exhaustive (no SAT)"; for D in 2 3 4; do python3 b3_enum.py 7 $D > /dev/null; done
python3 b3_enum.py 7 4 2 noT > /dev/null
echo "## n=7, all solvers x encodings"
for a in "7 2 0" "7 3 1" "7 4 2"; do for s in cadical153 glucose4 minisat22 lingeling; do
  for o in "TQ" "TQ order" "Q" "Q order"; do $PY b3_sat.py $a $s $o | tail -1; done; done; done
echo "## certified refutations (Glucose DRUP + own RUP checker)"
for a in "7 2 0 TQ" "7 3 1 TQ" "7 4 2 TQ" "7 4 2 Q" "9 5 3 TQ" "11 2 0 TQ" "11 3 0 TQ" "11 4 0 TQ" "11 5 3 TQ" "11 6 4 Q" "11 6 4 TQ"; do
  $PY b3_drup_check.py $a; done
echo "## other odd n (CaDiCaL)"
for a in "9 2 0" "9 3 0" "9 4 2" "9 5 3" "13 2 0" "13 3 0" "13 4 0" "13 5 0" "13 6 4" "13 7 5" "15 2 0" "15 3 0" "15 4 0" "15 5 0" "15 6 0" "15 7 5" "15 8 6"; do
  $PY b3_sat.py $a cadical153 Q order | tail -1; $PY b3_sat.py $a cadical153 TQ order | tail -1; done
echo "## even n (reconfirm B2 Thm A for n=8,10,12)"
for a in "8 2 0" "8 3 0" "8 4 2" "10 2 0" "10 3 0" "10 4 0" "10 5 3" "12 2 0" "12 3 0" "12 4 0" "12 5 0" "12 6 4"; do
  $PY b3_sat.py $a | tail -1; done
echo "## tightness / sanity SAT instances (models re-checked)"
for a in "5 2 0" "5 3 1" "6 3 1" "7 3 0" "7 4 1" "9 5 2" "11 6 3"; do $PY b3_sat.py $a | tail -2; done
