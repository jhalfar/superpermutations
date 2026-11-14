#!/bin/bash
# prepub.sh - the check every word goes through before it is published or announced.
#
# usage: bash tools/prepub/prepub.sh N WORD [options]
#   WORD                 the word (.txt or .txt.xz); letters 0..N-1, line feeds and CR ignored
#   --selection SEL      selection file of the word (n = 8: words/n8/selection-*.txt format, read by geng.py).
#                        Strongly preferred: the base is then built from the selection with all closed trails.
#   --base BASE --plan PLAN   use this base word and plan instead (e.g. the reproduce/ base of a record)
#   --time SEC           seconds per trailsearch setting (default by n: <=9: 60, 10: 300, 11: 600, >=12: 1200)
#   --threads T          search threads per setting (default 4)
#   --out DIR            work directory (default $PREPUB_RUNS/N-LENGTH-TIME)
#   --par P              run P trailsearch settings at a time (default 1; each uses --threads threads and its own
#                        memory, so P = 3 at n = 13 needs about 3 times one run); with P > 1 check_min also runs in
#                        the background beside the searches and recut runs beside them. The searches and the verdict
#                        are the same as with P = 1, only the wall-clock time changes.
# Steps:  1. three checkers (check_min.py, delcheck, Pantone's literal_check --deletions for N <= 12)
#         2. base and plan: from --selection (geng.py + word2plan, must be exact), or --base/--plan, or the word itself
#            (then the number of closed pieces is compared with the trail count and a mismatch is reported: a word
#            read as its own base can hide a closed trail, which is how 46,173 stayed hidden on 20 October)
#         3. trailsearch from the plan with several settings (kmax 8 and 12, T0 0.4, 0.7, 1.2), and recut --co-skip
#         4. REPORT.txt: either "CLEAN: no tool shortened the word in ..." or "SHORTER: ..." with the new word checked
# Run with nice; it never deletes anything outside its work directory. GPU segment insertion (n >= 11) is not in
# this script: run tools/gpucuts/orx.sh on the word's plan as well before publishing n >= 11.
# Environment: TOOLS = directory of the binaries delcheck, literal_check, trailsearch, word2plan, recut (default: the
# directory of this script); PYTHON (default python3); PREPUB_RUNS (default prepub-runs in the current directory).
set -u
H=$(cd "$(dirname "$0")" && pwd)
B=${TOOLS:-$H}; R=$(cd "$H/../.." && pwd); PY=${PYTHON:-$(command -v python3 || command -v python)}
RL=$H/relabel.py; MAP=""; REV=""; RUNS=${PREPUB_RUNS:-prepub-runs}
N=${1:?N}; W=${2:?WORD}; shift 2
SEL=""; BASE=""; PLAN=""; SEC=""; THR=4; OUT=""; PAR=1
while [ $# -gt 0 ]; do case "$1" in
  --selection) SEL=$2; shift 2;; --base) BASE=$2; shift 2;; --plan) PLAN=$2; shift 2;;
  --time) SEC=$2; shift 2;; --threads) THR=$2; shift 2;; --out) OUT=$2; shift 2;; --par) PAR=$2; shift 2;;
  *) echo "unknown option $1"; exit 2;; esac; done
if [ -z "$SEC" ]; then if [ "$N" -le 9 ]; then SEC=60; elif [ "$N" -eq 10 ]; then SEC=300; elif [ "$N" -eq 11 ]; then SEC=600; else SEC=1200; fi; fi
TMP=$RUNS/tmp.$$; mkdir -p "$RUNS"
case "$W" in *.xz) xz -dc "$W" | tr -d '\r\n' > "$TMP";; *) tr -d '\r\n' < "$W" > "$TMP";; esac
L=$(stat -c %s "$TMP"); printf '\n' >> "$TMP"
OUT=${OUT:-$RUNS/$N-$L-$(date +%m%d%H%M)}
mkdir -p "$OUT" || exit 1
mv "$TMP" "$OUT/word.txt"
REP=$OUT/REPORT.txt
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a "$REP"; }
say "prepub n=$N length $L word $W sha256(no LF) $(tr -d '\n' < "$OUT/word.txt" | sha256sum | cut -c1-64)"
fail=0
# 1. checkers (with --par > 1 check_min runs in the background and is read before the verdict)
CMPID=""
if [ "$PAR" -gt 1 ]; then
  (nice -n 19 "$PY" -I "$R/reproduce/tools/check_min.py" "$N" "$OUT/word.txt" > "$OUT/check_min.log" 2>&1) & CMPID=$!
else
  r=$(nice -n 19 "$PY" -I "$R/reproduce/tools/check_min.py" "$N" "$OUT/word.txt" 2>&1 | tail -1); say "check_min: $r"
  echo "$r" | grep -q "^VALID" || fail=1
fi
r=$(nice -n 19 "$B/delcheck" "$OUT/word.txt" "$THR" 2>&1 | tail -1); echo "$r" > "$OUT/word.delcheck.json"
echo "$r" | grep -q '"missing_permutations":0' && echo "$r" | grep -q '"coverage_preserving_deletions_count":0' \
  && say "delcheck: 0 missing, 0 deletable" || { say "delcheck: FAILED $r"; fail=1; }
if [ "$N" -le 12 ]; then
  ALPH=$(echo 0123456789ABCDEF | cut -c1-$N)
  r=$(nice -n 19 "$B/literal_check" "$N" "$ALPH" "$OUT/word.txt" --deletions 2>&1 | tail -1)
  echo "$r" | grep -q '"missing_permutations":0' && echo "$r" | grep -q '"coverage_preserving_deletions":\[\]' \
    && say "literal_check: 0 missing, no deletion" || { say "literal_check: FAILED $r"; fail=1; }
else say "literal_check: skipped for n > 12 (run it under Linux with enough memory)"; fi
[ $fail -eq 0 ] || { say "STOP: the word does not pass the checkers"; exit 1; }
# 2. base and plan
if [ -n "$SEL" ]; then
  nice -n 19 "$PY" -I "$R/reproduce/tools/geng.py" "$SEL" "$OUT/base.txt" > "$OUT/geng.log" 2>&1 || { say "geng.py failed"; exit 1; }
  BASE=$OUT/base.txt; PLAN=$OUT/word.plan
  # word2plan prints "...: safe to search from" or "...: NOT safe to search from"; the second contains the first,
  # so the test must look for the NOT (the old test accepted unsafe plans, and trailsearch then lost permutations).
  safe() { grep -q "RESULT: exact" "$1" && grep -q "safe to search from" "$1" && ! grep -q "NOT safe to search from" "$1"; }
  nice -n 19 "$B/word2plan" "$BASE" "$OUT/word.txt" "$PLAN" > "$OUT/word2plan.log" 2>&1
  if safe "$OUT/word2plan.log"; then say "base from the selection; word2plan: exact, safe to search from"
  else
    say "word2plan: not exact or NOT safe to search from on the selection's base ($(grep -o '^plan: [0-9]* events' "$OUT/word2plan.log"))"
    # A word of a symmetric image of the selection (relabelled and/or reversed) is fragmented on the base.  Search on
    # its image in the base's labelling: lengths and coverage do not change under relabelling and reversal.
    if nice -n 19 "$PY" -I "$RL" "$BASE" "$OUT/word.txt" "$OUT/word_rl.txt" > "$OUT/relabel.log" 2>&1; then
      MAP=$(grep -o "^MAP [0-9A-F]*" "$OUT/relabel.log" | cut -c5-); REV=$(grep -o "REV [01]" "$OUT/relabel.log" | cut -c5-)
      nice -n 19 "$B/word2plan" "$BASE" "$OUT/word_rl.txt" "$PLAN" > "$OUT/word2plan.log" 2>&1
      safe "$OUT/word2plan.log" || { say "word2plan on the relabelled word: still NOT safe; see word2plan.log"; exit 1; }
      say "the word is the image of a word of the selection (reversal $REV, then letters 01234567 -> $MAP); searching on that image: word2plan exact, safe ($(grep -o '^plan: [0-9]* events' "$OUT/word2plan.log"))"
    else say "no relabelling of the word fits the selection's trails; see word2plan.log (try word2plan --rebase)"; exit 1; fi
  fi
elif [ -n "$BASE" ] && [ -n "$PLAN" ]; then say "base $BASE, plan $PLAN (given)"
else BASE=$OUT/word.txt; PLAN=""
  say "WARNING: no selection given; the word is its own base. A trail that the word writes in parts is then not seen as closed."
fi
PLANARG=""; [ -n "$PLAN" ] && PLANARG="--plan-in $PLAN"
nice -n 19 "$B/trailsearch" "$BASE" "$OUT/load.txt" $PLANARG --time 0 > "$OUT/load.log" 2>&1
TR=$(grep -o "^trails [0-9]*" "$OUT/load.log" | grep -o "[0-9]*"); CL=$(grep -o "closed pieces [0-9]*" "$OUT/load.log" | grep -o "[0-9]*")
ML=$(grep -o "model length of the [a-z ]*: [0-9]*" "$OUT/load.log" | grep -o "[0-9]*$")
say "model: trails $TR, closed pieces $CL, model length $ML"
[ "$TR" = "$CL" ] || say "WARNING: $((TR - CL)) trail(s) not closed in the base: the search cannot move them; give --selection"
[ "$ML" = "$L" ] || say "WARNING: model length $ML differs from the word length $L"
# 3. searches
FOCUS=""; [ "$N" -ge 12 ] && FOCUS="--focus 0.85"
PT=""; [ "$PAR" -gt 1 ] && PT=", $PAR at a time"
best=$L; bestf=""
run_ts() {  # k t: one trailsearch setting; its exit code goes to $o.exit
  local o=$OUT/ts_k$1_t$2.txt
  nice -n 19 "$B/trailsearch" "$BASE" "$o" $PLANARG --time "$SEC" --seed $(($1*100+${2/./})) --kmax $1 --T0 $2 \
    --threads "$THR" --sync 15 --ckpt 60 $FOCUS > "$o.log" 2>&1; echo $? > "$o.exit"
}
run_recut() { nice -n 19 "$B/recut" "$BASE" "$OUT/recut.txt" --plan-in "$PLAN" --co-skip --time 0 > "$OUT/recut.log" 2>&1; }
if [ "$PAR" -gt 1 ]; then          # P settings at a time, recut beside them; the report keeps the fixed order below
  [ -n "$PLAN" ] && { run_recut & }
  for k in 8 12; do for t in 0.4 0.7 1.2; do
    while [ "$(jobs -rp | grep -v "^${CMPID:-x}$" | wc -l)" -ge "$PAR" ]; do wait -n; done
    run_ts $k $t &
  done; done
  for p in $(jobs -rp); do [ "$p" = "$CMPID" ] || wait "$p"; done
else
  for k in 8 12; do for t in 0.4 0.7 1.2; do run_ts $k $t; done; done
  [ -n "$PLAN" ] && run_recut
fi
for k in 8 12; do for t in 0.4 0.7 1.2; do
  o=$OUT/ts_k${k}_t$t.txt; e=$(cat "$o.exit" 2>/dev/null || echo 99)
  b=$(grep -o "best [0-9]*$" "$o.log" | tail -1 | grep -o "[0-9]*"); first=$(grep -m1 -o "t=[0-9]*s: best [0-9]* -> [0-9]*" "$o.log")
  if [ "$e" -ne 0 ] || [ ! -f "$o" ]; then say "trailsearch kmax $k T0 $t: exit $e, no word written: $(grep -m1 -o 'REFUSED: .\{0,160\}' "$o.log")"; b=""; fail=1
  else say "trailsearch kmax $k T0 $t ($SEC s, $THR threads$PT): best ${b:-?} ${first:+(first gain $first)}"; fi
  if [ -n "$b" ] && [ "$b" -lt "$best" ]; then best=$b; bestf=$o; fi
done; done
if [ -n "$PLAN" ]; then
  b=$(grep -o "length [0-9]*" "$OUT/recut.log" | tail -1 | grep -o "[0-9]*"); say "recut --co-skip: length ${b:-?}"
  if [ -n "$b" ] && [ "$b" -lt "$best" ]; then best=$b; bestf=$OUT/recut.txt; fi
fi
if [ -n "$CMPID" ]; then             # check_min of step 1, run in the background
  wait "$CMPID"; r=$(tail -1 "$OUT/check_min.log"); say "check_min: $r"
  echo "$r" | grep -q "^VALID" || { say "STOP: check_min does not accept the word"; exit 1; }
fi
# 4. verdict
if [ "$best" -lt "$L" ]; then
  r=$(nice -n 19 "$B/delcheck" "$bestf" "$THR" 2>&1 | tail -1); echo "$r" > "$bestf.delcheck.json"
  echo "$r" | grep -q '"missing_permutations":0' && v=valid || v="NOT VALID"
  if [ -n "$MAP" ]; then nice -n 19 "$PY" -I "$RL" --back "$MAP" "$REV" "$bestf" "$bestf.orig_labels.txt"
    say "(the search ran on the relabelled image; $bestf.orig_labels.txt is the shorter word in the word's own labelling)"; fi
  say "SHORTER: $best (from $L) in $bestf, delcheck: $v. Do not publish $L; run prepub again on the new word."
  exit 3
fi
[ $fail -eq 0 ] || { say "NOT CLEAN: a search was refused (see above); fix the base/plan and run again"; exit 1; }
say "CLEAN: no tool shortened the word ($((6 * SEC)) s of trailsearch on $THR threads${PLAN:+, recut}). For n >= 11 also run the GPU passes."
