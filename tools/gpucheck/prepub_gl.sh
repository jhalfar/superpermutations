#!/bin/bash
# prepub_gl.sh - prepub_fast.sh with the card: the same steps, checkers and verdict, plus
#   * step 0, a first check on the card: gcheck (vfast's numbers) and gdelcheck (delcheck's verdict, n <= 13) in
#     seconds; a word that fails stops at once.  The CPU checkers (check_min, delcheck, literal_check) still run and
#     still give the verdict;
#   * the searches run in trailsearch_gl --gpuload: the bitmap passes of the model load on the card
#     (same plans and words as trailsearch_fast; at n = 13 the load takes about 2 min instead of 6).
#   If the card is busy (gpubusy.sh), both are skipped and the run is prepub_fast's.  --nogpu: never use it.
# Environment: TOOLS = directory of the binaries delcheck, literal_check, word2plan, recut, trailsearch_gl, gcheck,
# gdelcheck (default: the directory of this script); PYTHON (default python3); PREPUB_RUNS (default prepub-runs).
# The header of prepub_fast.sh follows.
# prepub_fast.sh - tools/prepub/prepub.sh with the same steps and the same verdict, in less wall-clock time.
#
# usage: bash tools/gpucheck/prepub_gl.sh N WORD [options]     (options as prepub.sh, plus --ts, --cmprocs, --nogpu)
#   --selection SEL | --base BASE --plan PLAN | (none: the word is its own base), --time SEC, --threads T, --out DIR
#   --par P      P trailsearch settings at a time (default 1).  All six settings run in ONE trailsearch_fast process
#                (--set, --setpar P) on one loaded model, so P = 6 at n = 13 needs about 11 GB + 6 x T x 0.45 GB,
#                not 6 x 13 GB as six processes did.
#   --ts EXE     the trailsearch binary (default trailsearch_gl in TOOLS; it must know --set)
#   --cmprocs K  K > 1: check_min_fast.py --procs K (the loop of check_min.py on K ranges at once) instead of
#                check_min.py (default 1); at n = 13 check_min.py takes 22-33 min, longer than the searches with --par 6
# What differs from prepub.sh (none of it changes a search or the verdict):
#   * no separate load step (prepub.sh ran trailsearch --time 0 on one thread, 16 min at n = 13, and wrote a 6.7 GB
#     load.txt): the trail count, closed pieces and model length are read from the log of the search process;
#   * the model is loaded once for all six settings instead of six times (about 4 min each at n = 13);
#   * the checkers (check_min, delcheck, literal_check) run in the background beside the searches; their verdict is
#     read before the search verdict, and a failure still ends with "STOP: the word does not pass the checkers";
#   * a setting that does not shorten the word writes only its plan (--write-better-only): its word is the input
#     plan's word, which the plan check of trailsearch has already covered.  A shorter word is written and checked as
#     before.  At n = 13 this saves 6 x 6.7 GB of writes and about 1.5 min per setting.
#   * the REPORT lines and their order are those of prepub.sh, except that "model:" comes after the searches.
set -u
H=$(cd "$(dirname "$0")" && pwd)
B=${TOOLS:-$H}; R=$(cd "$H/../.." && pwd); PY=${PYTHON:-$(command -v python3 || command -v python)}
TS=$B/trailsearch_gl; GPU=1
RL=$H/../prepub/relabel.py; MAP=""; REV=""; RUNS=${PREPUB_RUNS:-prepub-runs}
N=${1:?N}; W=${2:?WORD}; shift 2
SEL=""; BASE=""; PLAN=""; SEC=""; THR=4; OUT=""; PAR=1; CMP=1
while [ $# -gt 0 ]; do case "$1" in
  --selection) SEL=$2; shift 2;; --base) BASE=$2; shift 2;; --plan) PLAN=$2; shift 2;;
  --time) SEC=$2; shift 2;; --threads) THR=$2; shift 2;; --out) OUT=$2; shift 2;; --par) PAR=$2; shift 2;;
  --ts) TS=$2; shift 2;; --cmprocs) CMP=$2; shift 2;; --nogpu) GPU=0; shift;;
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
say "prepub n=$N length $L word $W sha256(no LF) $(tr -d '\n' < "$OUT/word.txt" | sha256sum | cut -c1-64) (prepub_gl)"
fail=0
# 0. card first check (prepub_gl): gcheck (coverage, vfast's numbers) and gdelcheck (delcheck's verdict) in seconds;
#    a failure stops here.  They do not replace the checkers below, which still give the verdict.
if [ "$GPU" = 1 ] && bash "$H/gpubusy.sh" > /dev/null 2>&1; then
  ALPH0=$(echo 0123456789ABCDEF | cut -c1-$N)
  r=$(nice -n 19 "$B/gcheck" "$N" "$OUT/word.txt" --alpha "$ALPH0" 2> "$OUT/gcheck.err" | tail -1); echo "$r" > "$OUT/gcheck.json"
  echo "$r" | grep -q '"missing":0,"foreign_bytes":0' \
    && say "gcheck (card, first check): 0 missing, repeats $(echo "$r" | grep -o '"repeats":[0-9]*' | cut -d: -f2), $(echo "$r" | grep -o '"seconds":[0-9.]*' | cut -d: -f2) s" \
    || { say "gcheck (card, first check): FAILED $r"; say "STOP: the word does not pass the card's first check"; exit 1; }
  if [ "$N" -le 13 ]; then
    r=$(nice -n 19 "$B/gdelcheck" "$OUT/word.txt" "$THR" 2> "$OUT/gdelcheck.err" | tail -1); echo "$r" > "$OUT/gdelcheck.json"
    echo "$r" | grep -q '"missing_permutations":0' && echo "$r" | grep -q '"coverage_preserving_deletions_count":0' \
      && say "gdelcheck (card, first check): 0 missing, 0 deletable, $(echo "$r" | grep -o '"seconds":[0-9.]*' | cut -d: -f2) s" \
      || { say "gdelcheck (card, first check): FAILED $r"; say "STOP: the word does not pass the card's first check"; exit 1; }
  fi
  GPUARG="--gpuload"
elif [ "$GPU" = 1 ]; then say "card busy: no card first check, trailsearch loads on the processor"; GPUARG=""
else GPUARG=""; fi
# 1. checkers, in the background; read before the verdict
if [ "$CMP" -gt 1 ]; then CMCMD=("$H/check_min_fast.py" "$N" "$OUT/word.txt" --procs "$CMP"); else CMCMD=("$R/reproduce/tools/check_min.py" "$N" "$OUT/word.txt"); fi
(nice -n 19 "$PY" -I "${CMCMD[@]}" > "$OUT/check_min.log" 2>&1) & CMPID=$!
(nice -n 19 "$B/delcheck" "$OUT/word.txt" "$THR" 2>&1 | tail -1 > "$OUT/word.delcheck.json") & DCPID=$!
LCPID=""
if [ "$N" -le 12 ]; then
  ALPH=$(echo 0123456789ABCDEF | cut -c1-$N)
  (nice -n 19 "$B/literal_check" "$N" "$ALPH" "$OUT/word.txt" --deletions 2>&1 | tail -1 > "$OUT/literal_check.log") & LCPID=$!
fi
# 2. base and plan (as prepub.sh)
if [ -n "$SEL" ]; then
  nice -n 19 "$PY" -I "$R/reproduce/tools/geng.py" "$SEL" "$OUT/base.txt" > "$OUT/geng.log" 2>&1 || { say "geng.py failed"; exit 1; }
  BASE=$OUT/base.txt; PLAN=$OUT/word.plan
  safe() { grep -q "RESULT: exact" "$1" && grep -q "safe to search from" "$1" && ! grep -q "NOT safe to search from" "$1"; }
  nice -n 19 "$B/word2plan" "$BASE" "$OUT/word.txt" "$PLAN" > "$OUT/word2plan.log" 2>&1
  if safe "$OUT/word2plan.log"; then say "base from the selection; word2plan: exact, safe to search from"
  else
    say "word2plan: not exact or NOT safe to search from on the selection's base ($(grep -o '^plan: [0-9]* events' "$OUT/word2plan.log"))"
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
# 3. searches: one process, six sets, PAR at a time; recut beside it
FOCUS=""; [ "$N" -ge 12 ] && FOCUS="--focus 0.85"
PT=""; [ "$PAR" -gt 1 ] && PT=", $PAR at a time"
WOUT=$(cygpath -m "$OUT" 2>/dev/null || echo "$OUT")
SETS=""
for k in 8 12; do for t in 0.4 0.7 1.2; do SETS="$SETS --set $WOUT/ts_k${k}_t$t.txt:$k:$t:$(($k*100+${t/./}))"; done; done
[ -n "$PLAN" ] && { nice -n 19 "$B/recut" "$BASE" "$OUT/recut.txt" --plan-in "$PLAN" --co-skip --time 0 > "$OUT/recut.log" 2>&1 & }
nice -n 19 "$TS" "$BASE" "$OUT/ts_main.txt" $PLANARG $GPUARG --time "$SEC" --threads "$THR" --sync 15 --ckpt 60 $FOCUS \
  --write-better-only --setpar "$PAR" $SETS > "$OUT/ts_main.log" 2>&1
TSE=$?
for p in $(jobs -rp); do case " $CMPID $DCPID $LCPID " in *" $p "*) ;; *) wait "$p";; esac; done   # recut
TR=$(grep -o "^trails [0-9]*" "$OUT/ts_main.log" | grep -o "[0-9]*"); CL=$(grep -o "closed pieces [0-9]*" "$OUT/ts_main.log" | grep -o "[0-9]*")
ML=$(grep -o "model length of the [a-z ]*: [0-9]*" "$OUT/ts_main.log" | grep -o "[0-9]*$")
say "model: trails $TR, closed pieces $CL, model length $ML"
[ "$TR" = "$CL" ] || say "WARNING: $((TR - CL)) trail(s) not closed in the base: the search cannot move them; give --selection"
[ "$ML" = "$L" ] || say "WARNING: model length $ML differs from the word length $L"
best=$L; bestf=""
for k in 8 12; do for t in 0.4 0.7 1.2; do
  o=$OUT/ts_k${k}_t$t.txt
  b=$(grep -o "best [0-9]*$" "$o.log" 2>/dev/null | tail -1 | grep -o "[0-9]*"); first=$(grep -m1 -o "t=[0-9]*s: best [0-9]* -> [0-9]*" "$o.log" 2>/dev/null)
  if ! grep -q "^wrote " "$o.log" 2>/dev/null || grep -q "REFUSED" "$o.log"; then
    say "trailsearch kmax $k T0 $t: exit $TSE, no word written: $(grep -h -m1 -o 'REFUSED: .\{0,160\}' "$o.log" "$OUT/ts_main.log" 2>/dev/null | head -1)"; b=""; fail=1
  else say "trailsearch kmax $k T0 $t ($SEC s, $THR threads$PT): best ${b:-?} ${first:+(first gain $first)}"; fi
  if [ -n "$b" ] && [ "$b" -lt "$best" ]; then best=$b; bestf=$o; fi
done; done
if [ -n "$PLAN" ]; then
  b=$(grep -o "length [0-9]*" "$OUT/recut.log" | tail -1 | grep -o "[0-9]*"); say "recut --co-skip: length ${b:-?}"
  if [ -n "$b" ] && [ "$b" -lt "$best" ]; then best=$b; bestf=$OUT/recut.txt; fi
fi
# checkers of step 1
wait "$DCPID"; r=$(cat "$OUT/word.delcheck.json")
echo "$r" | grep -q '"missing_permutations":0' && echo "$r" | grep -q '"coverage_preserving_deletions_count":0' \
  && say "delcheck: 0 missing, 0 deletable" || { say "delcheck: FAILED $r"; ckfail=1; }
if [ -n "$LCPID" ]; then
  wait "$LCPID"; r=$(cat "$OUT/literal_check.log")
  echo "$r" | grep -q '"missing_permutations":0' && echo "$r" | grep -q '"coverage_preserving_deletions":\[\]' \
    && say "literal_check: 0 missing, no deletion" || { say "literal_check: FAILED $r"; ckfail=1; }
else say "literal_check: skipped for n > 12 (run it under Linux with enough memory)"; fi
wait "$CMPID"; r=$(tail -1 "$OUT/check_min.log"); say "check_min: $r"
echo "$r" | grep -q "^VALID" || ckfail=1
[ "${ckfail:-0}" -eq 0 ] || { say "STOP: the word does not pass the checkers"; exit 1; }
# 4. verdict (as prepub.sh)
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
