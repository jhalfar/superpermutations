#!/bin/bash
# test.sh - runs the small tests of every part of this repository, one after another.
#
# Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.
#
# usage: bash test.sh PANTONE_REPO [WORK=./test-all] [THREADS=1]
#   PANTONE_REPO  a clone of https://github.com/jaypantone/superperm-upper-43-80.  The script takes these files from
#                 it: his n = 11 word (words/11/superpermutation-11-43930680.txt.xz), tools/construction-input.txt
#                 and, with PROOFS=1, his n = 9 word (words/9/superpermutation-9-408732.txt)
#   WORK          a directory for everything that is written (about 1 GB while it runs)
#
# The parts:
#   1. tools/test.sh       builds the C programs and runs them at n = 11 on Pantone's word, then rebuilds the n = 10
#                          and n = 11 words from their selections (reproduce/) and runs the passes on them
#   2. reproduce/          tools/check_min.py, the checker that shares no code with the C programs, on the two words
#                          that part 1 rebuilt
#   3. selection/test.sh   builds the four selections again from Pantone's file and runs their checkers
#   4. arrange/test.sh     the arrangement scripts on the n = 10 and n = 11 pieces, without a solver
#   5. proofs/n9           with PROOFS=1: the two checkers of the n = 9 result
# Needs: bash, gcc with OpenMP, xz, sha256sum, Python 3 with numpy and scipy.  No solver.  About 15 minutes on one
# thread and 1 GB of RAM.  Nothing at n = 12 or n = 13 runs here: reproduce/REPRODUCE.md has those commands and
# their hashes.
# The script ends with "ALL PARTS PASSED" or with the list of parts that failed; each part prints its own lines.
HERE=$(cd "$(dirname "$0")" && pwd)
[ $# -ge 1 ] || { sed -n '2,23p' "$0"; exit 1; }
PR=$(cd "$1" && pwd) || exit 1; WORK=${2:-./test-all}; THR=${3:-1}
mkdir -p "$WORK" || exit 1; WORK=$(cd "$WORK" && pwd)
PY=${PYTHON:-$(command -v python3 || command -v python)}
[ -n "$PY" ] || { echo "Python 3 is needed"; exit 1; }
export PYTHONDONTWRITEBYTECODE=1 # leave no __pycache__ next to the scripts
[ -f "$PR/words/11/superpermutation-11-43930680.txt.xz" ] && [ -f "$PR/tools/construction-input.txt" ] || { echo "$PR does not look like a clone of jaypantone/superperm-upper-43-80"; exit 1; }
failed=""
part() { echo; echo "######## $1"; }
fail() { failed="$failed
  $1"; echo "PART FAILED: $1"; }

part "1. tools/test.sh"
xz -dkc "$PR/words/11/superpermutation-11-43930680.txt.xz" > "$WORK/pantone-11.txt" || fail "cannot unpack Pantone's n = 11 word"
KEEP=1 PYTHON="$PY" bash "$HERE/tools/test.sh" "$WORK/pantone-11.txt" "$HERE" "$WORK/tools" "$THR" || fail "tools/test.sh"

part "2. reproduce: check_min.py on the rebuilt n = 10 and n = 11 words"
for n in 10 11; do
  w="$WORK/tools/t-n$n.txt"
  if [ ! -f "$w" ]; then fail "reproduce: part 1 left no n = $n word"; continue; fi
  if "$PY" "$HERE/reproduce/tools/check_min.py" $n "$w" | tee "$WORK/check_min_$n.log" | tail -1 | grep -q "VALID: every permutation occurs"; then echo "ok    n = $n: check_min.py: every permutation occurs"; else fail "reproduce: check_min.py on the n = $n word"; fi
done
rm -f "$WORK"/tools/t*.txt "$WORK"/tools/a-n*.txt "$WORK"/tools/n1?-base.txt "$WORK"/tools/w6*.txt

part "3. selection/test.sh"
if [ -f "$HERE/selection/test.sh" ]; then
  PY="$PY" bash "$HERE/selection/test.sh" "$PR/tools/construction-input.txt" "$WORK/selection" "$HERE/reproduce/selections" || fail "selection/test.sh"
else echo "no selection/test.sh here: skipped"; fi

part "4. arrange/test.sh"
if [ -f "$HERE/arrange/test.sh" ]; then
  PY="$PY" bash "$HERE/arrange/test.sh" "$HERE/reproduce" "$WORK/arrange" || fail "arrange/test.sh"
else echo "no arrange/test.sh here: skipped"; fi

if [ "${PROOFS:-0}" = 1 ]; then
  part "5. proofs/n9"
  W9="$PR/words/9/superpermutation-9-408732.txt"
  if [ ! -f "$W9" ] && [ -f "$W9.xz" ]; then xz -dkc "$W9.xz" > "$WORK/pantone-9.txt"; W9="$WORK/pantone-9.txt"; fi
  if [ ! -f "$W9" ]; then fail "proofs/n9: Pantone's n = 9 word is not in $PR/words/9"
  else
    "$PY" "$HERE/proofs/n9/check9s.py" "$W9" > "$WORK/check9s.log" 2>&1
    "$PY" "$HERE/proofs/n9/check9m.py" "$W9" > "$WORK/check9m.log" 2>&1
    for c in check9s check9m; do
      if grep -q "THEOREM (checked)" "$WORK/$c.log"; then echo "ok    $c.py: $(grep -o 'THEOREM (checked).*letters' "$WORK/$c.log" | tail -1)"; else fail "proofs/n9: $c.py"; fi
    done
  fi
fi

echo
if [ -z "$failed" ]; then echo "ALL PARTS PASSED"; else echo "FAILED:$failed"; exit 1; fi
