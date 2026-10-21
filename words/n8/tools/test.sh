#!/bin/bash
# test.sh - short tests of the n = 8 tools: the 46,174 word is checked, taken apart, written again from its order
# and rebuilt from its selection by the integer programme; the search steps run on small cases.
#
# Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.
#
# usage: bash words/n8/tools/test.sh [WORK=./test-n8]
#
# Needs: bash, xz, sha256sum, Python 3 with numpy and scipy.  No other solver: the integer programmes run on HiGHS
# through scipy.  SOLVER=gurobi (or scip, cbc) runs them on another solver.  About 2 minutes on one thread.
# Test 10 also needs a C compiler with OpenMP (CC, default gcc or cc) and is skipped without one.
# SLOW=1 adds the model "slices" twice: joins of every overlap (46,174) and only joins of overlap >= 3 (46,182);
# with HiGHS that takes about half an hour more.
# The script prints one line per test and ends with "ALL n TESTS PASSED" or with the list of failures.
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
WORK=${1:-./test-n8}
mkdir -p "$WORK" || exit 1
WORK=$(cd "$WORK" && pwd)
PY=${PYTHON:-$(command -v python3 || command -v python)}
[ -n "$PY" ] || { echo "Python 3 is needed"; exit 1; }
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1
SOLVER=${SOLVER:-highs}
N8="$PY -I $HERE/n8.py"
SEL=$REPO/words/n8/selection-46174.txt
ORDER=$REPO/words/n8/order-46174.txt
SHA_WORD=50d9bb150ffcf28482e4663f9d8a5ff449fae2de2ef09643eefd922fe1b224aa
npass=0; fails=""
ok()  { npass=$((npass + 1)); echo "ok    $*"; }
bad() { fails="$fails
  $*"; echo "FAIL  $*"; }
has() { grep -q -- "$2" "$1"; }
sha() { tr -d '\n' < "$1" | sha256sum | cut -c1-64; }

# 1. the published word
xz -dkc "$REPO/words/superpermutation-8-46174.txt.xz" > "$WORK/w46174.txt"
$N8 check "$WORK/w46174.txt" > "$WORK/1.log" 2>&1
if has "$WORK/1.log" "VALID: every permutation occurs and no letter" && has "$WORK/1.log" "$SHA_WORD"; then
  ok "1  n8.py check: the 46,174 word is valid, no letter can be deleted, SHA-256 as published"
else bad "1  n8.py check on the 46,174 word (see $WORK/1.log)"; fi

# 2. the checker of reproduce/, which shares no code with n8.py
if "$PY" -I "$REPO/reproduce/tools/check_min.py" 8 "$WORK/w46174.txt" > "$WORK/2.log" 2>&1 &&
   has "$WORK/2.log" "VALID: every permutation occurs"; then
  ok "2  check_min.py: every permutation occurs"
else bad "2  check_min.py on the 46,174 word"; fi

# 3. its selection and slice order
$N8 extract "$WORK/w46174.txt" -o "$WORK/sel.txt" --order-out "$WORK/order.txt" --compare "$SEL" > "$WORK/3.log" 2>&1
if has "$WORK/3.log" "the selection equals .*selection-46174.txt$" && has "$WORK/3.log" "J 25" &&
   diff <(grep -v '^#' "$WORK/order.txt") <(grep -v '^#' "$ORDER") > /dev/null; then
  ok "3  n8.py extract: the selection of the word is selection-46174.txt, its order is order-46174.txt, J = 25"
else bad "3  n8.py extract (see $WORK/3.log)"; fi

# 4. the word again from selection and order, no solver
$N8 rebuild "$SEL" --order "$ORDER" -o "$WORK/r4.txt" > "$WORK/4.log" 2>&1
if [ "$(sha "$WORK/r4.txt")" = "$SHA_WORD" ] && has "$WORK/4.log" "VALID"; then
  ok "4  n8.py rebuild --order: the published word, letter for letter"
else bad "4  n8.py rebuild --order (see $WORK/4.log)"; fi

# 5. the best word of the selection by the integer programme (model trails)
$N8 rebuild "$SEL" -o "$WORK/r5.txt" --solver "$SOLVER" > "$WORK/5.log" 2>&1
if has "$WORK/5.log" "J 25, lower bound on J 25: optimal in this model" && has "$WORK/5.log" "^length 46174 " &&
   has "$WORK/5.log" "VALID: every permutation occurs and no letter" &&
   "$PY" -I "$REPO/reproduce/tools/check_min.py" 8 "$WORK/r5.txt" | grep -q "VALID: every permutation occurs"; then
  ok "5  n8.py rebuild ($SOLVER): 46,174 letters, J = 25 = lower bound, valid (SHA-256 $(sha "$WORK/r5.txt" | cut -c1-12)...)"
else bad "5  n8.py rebuild with $SOLVER (see $WORK/5.log)"; fi

# 6. the seven words of ties/ have the same selection, up to renaming and reading backwards
n6=0
for f in "$REPO"/words/n8/ties/*.txt.xz; do
  xz -dkc "$f" > "$WORK/tie.txt"
  $N8 extract "$WORK/tie.txt" -o "$WORK/tie-sel.txt" --compare "$SEL" > "$WORK/6.log" 2>&1
  grep -q "the selection equals\|has the selection" "$WORK/6.log" && n6=$((n6 + 1))
done
if [ $n6 = 7 ]; then ok "6  n8.py extract: all 7 words of ties/ come from the selection, up to symmetry"
else bad "6  ties/: only $n6 of 7 words matched"; fi

# 7. closed walk types with at most 28 loops
$N8 walks --max-loops 28 -o "$WORK/types28.txt" > "$WORK/7.log" 2>&1
if has "$WORK/7.log" "28 loops and Q <= 17: 3 (complete" && has "$WORK/7.log" "266646664666466466646664666"; then
  ok "7  n8.py walks --max-loops 28: 3 types, among them the 27-walk"
else bad "7  n8.py walks (see $WORK/7.log)"; fi

# 8. the packing, and the price of the packing
$N8 pack --solver "$SOLVER" -o "$WORK/pack.txt" > "$WORK/8.log" 2>&1
$N8 price "$WORK/pack.txt" --solver "$SOLVER" --quiet > "$WORK/8b.log" 2>&1
if has "$WORK/8.log" "walks \[27, 27, 27, 27\]" && has "$WORK/8.log" "12 loops without a row" &&
   has "$WORK/8b.log" "^length 46174 "; then
  ok "8  n8.py pack ($SOLVER): four 27-walks and 12 loops without a row; priced at 46,174"
else bad "8  n8.py pack (see $WORK/8.log, $WORK/8b.log)"; fi

# 9. every packing by four 27-walks, up to renaming 0..5
$N8 pack --copies 266646664666466466646664666 4 -o "$WORK/copies.txt" > "$WORK/9.log" 2>&1
if has "$WORK/9.log" "360 packings of 4 copies, 2 classes"; then
  ok "9  n8.py pack --copies: 360 packings by four 27-walks, 2 classes up to renaming"
else bad "9  n8.py pack --copies (see $WORK/9.log)"; fi

# 10. tools/trailsearch.c, which may open a trail inside a slice, on the base word of the selection (C compiler)
CC=${CC:-$(command -v gcc || command -v cc)}
if [ -n "$CC" ] && "$CC" -O2 -mpopcnt -fopenmp -o "$WORK/trailsearch" "$REPO/tools/trailsearch.c" -lm 2> "$WORK/10cc.log"; then
  "$PY" -I "$REPO/reproduce/tools/geng.py" "$SEL" "$WORK/base8.txt" --table "$WORK/base8.tsv" > "$WORK/10a.log" 2>&1
  "$WORK/trailsearch" "$WORK/base8.txt" "$WORK/t10.txt" --iters 30000 --seed 1 --kmax 12 --T0 0.7 --threads 1 \
    > "$WORK/10.log" 2>&1
  $N8 check "$WORK/t10.txt" > "$WORK/10b.log" 2>&1
  if has "$WORK/10b.log" "^length 46173," && has "$WORK/10b.log" "VALID: every permutation occurs and no letter" &&
     has "$WORK/10.log" "events 16 (unchanged pieces 0, segments 0).*gap-1 openings 0, duplicate-skip openings 0"; then
    ok "10 trailsearch on the selection: 46,173 letters, every trail one run opened at a step of weight 2 or 3, valid"
  else bad "10 trailsearch on the selection (see $WORK/10.log, $WORK/10b.log)"; fi
else echo "skip  10 no C compiler with OpenMP: trailsearch not built"; fi

if [ "${SLOW:-0}" = 1 ]; then
  $N8 price "$SEL" --model slices --solver "$SOLVER" --quiet > "$WORK/11.log" 2>&1
  if has "$WORK/11.log" "J 25, lower bound on J 25" && has "$WORK/11.log" "^length 46174 "; then
    ok "11 n8.py price --model slices: 46,174, J = 25 = lower bound"
  else bad "11 n8.py price --model slices (see $WORK/11.log)"; fi
  $N8 price "$SEL" --model slices --min-overlap 3 --solver "$SOLVER" --quiet > "$WORK/12.log" 2>&1
  if has "$WORK/12.log" "J 33, lower bound on J 33" && has "$WORK/12.log" "^length 46182 "; then
    ok "12 n8.py price --model slices --min-overlap 3: 46,182, J = 33 = lower bound"
  else bad "12 n8.py price --model slices --min-overlap 3 (see $WORK/12.log)"; fi
fi

echo
if [ -z "$fails" ]; then echo "ALL $npass TESTS PASSED"; else echo "FAILED:$fails"; exit 1; fi
