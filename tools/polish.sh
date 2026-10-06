#!/bin/bash
# polish.sh - cycle the three deterministic passes on a plan until a whole cycle gains nothing.
#
#   dpa   relocate --dpa        windows of neighbouring trails moved elsewhere, the trails around re-cut
#   or3   segins --or3 C        segment insertion (with three cuts: a 3-opt move without reversal)
#   loop  loopscan --greedy     loop moves
#
# Every word is checked with delcheck before its plan is accepted, and only the best word stays on disk.
# DIR/best.txt holds "LENGTH PLAN WORD" of the best word, DIR/steps.log one line per step.
#
# usage: polish.sh DIR BASE PLAN0 [THREADS=4] [MAXCYCLES=6] [OR3="--or3 3 --or3-slack 0"] [STEPS="dpa or3 loop"]
#
# What I used: n = 11  polish.sh DIR BASE PLAN 2 6 "--or3 5 --or3-slack 4"
#              n = 12  polish.sh DIR BASE PLAN 4 6 "--or3 5 --or3-slack 1"
#              n = 13  OR3TIME=16000 polish.sh DIR BASE PLAN 8 2 "--or3 3 --or3-slack 0 --or3-maxcand 3000 --or3-sec 14400"
#                      (one n = 13 process at a time: each needs 11 to 13 GB)
# Environment: TOOLS = directory of the binaries (default: the directory of this script); DPATIME, OR3TIME, LSTIME =
# time limits of the steps in seconds (defaults 14400, 7200, 7200); DPAOPT = more options for relocate; LSOPT =
# options of the loop step (default "--neutral --nbatch 16"); LSROUNDS (default 40).
# The binaries are built as the comment at the top of each .c file says (test.sh builds them all).
T=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
[ $# -ge 3 ] || { sed -n '2,20p' "$0"; exit 1; }
DIR=$1; BASE=$2; PLAN=$3; THR=${4:-4}; MAXC=${5:-6}; OR3=${6:---or3 3 --or3-slack 0}; STEPS=${7:-dpa or3 loop}
mkdir -p "$DIR"; LOG=$DIR/steps.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a "$LOG"; }
len_of() { grep -o 'wrote .* length [0-9]*' "$1" | tail -1 | grep -o '[0-9]*$'; }
check() { "$T/delcheck" "$1" "$THR" > "$1.delcheck.json" 2>&1; grep -q '"missing_permutations":0' "$1.delcheck.json"; }
best_len=999999999999; best_word=""
accept() {   # tag word plan : keep it if it is valid and shorter
  local L; L=$(len_of "$DIR/$1.log")
  if [ -n "$L" ] && [ -f "$2" ] && [ "$L" -lt "$best_len" ] && check "$2"; then
    [ -n "$best_word" ] && rm -f "$best_word"
    cp "$3" "$DIR/$1.plan"; PLAN=$DIR/$1.plan; say "$1: $best_len -> $L valid"; best_len=$L; best_word=$2
    echo "$L $PLAN $2" > "$DIR/best.txt"; return 0
  fi
  say "$1: no gain (length '$L', best $best_len)"; [ "$2" != "$best_word" ] && rm -f "$2"; return 1
}
say "start: base $BASE plan $PLAN threads $THR steps '$STEPS' or3 '$OR3'"
for c in $(seq 1 "$MAXC"); do
  gained=0
  for s in $STEPS; do
    t=c${c}_$s
    case $s in
      dpa)  OMP_NUM_THREADS=$THR timeout "${DPATIME:-14400}" nice -n 19 "$T/relocate" "$BASE" "$DIR/$t.txt" --plan-in "$PLAN" --threads 1 --time 0 --dpa --dpa-thr "$THR" ${DPAOPT:-} --dpa-v > "$DIR/$t.log" 2>&1
            accept $t "$DIR/$t.txt" "$DIR/$t.txt.plan" && gained=1 ;;
      or3)  OMP_NUM_THREADS=$THR timeout "${OR3TIME:-7200}" nice -n 19 "$T/segins" "$BASE" "$DIR/$t.txt" --plan-in "$PLAN" --time 0 --threads "$THR" $OR3 > "$DIR/$t.log" 2>&1
            accept $t "$DIR/$t.txt" "$DIR/$t.txt.plan" && gained=1 ;;
      loop) OMP_NUM_THREADS=$THR timeout "${LSTIME:-7200}" nice -n 19 "$T/loopscan" "$BASE" --plan "$PLAN" --only PABD --nogap1 --threads "$THR" --quiet --greedy ${LSOPT:---neutral --nbatch 16} --maxrounds "${LSROUNDS:-40}" --planout "$DIR/$t.txt.plan" --out "$DIR/$t.txt" > "$DIR/$t.log" 2>&1
            accept $t "$DIR/$t.txt" "$DIR/$t.txt.plan" && gained=1 ;;
      *)    say "unknown step '$s'"; exit 1 ;;
    esac
  done
  [ $gained = 0 ] && { say "cycle $c: nothing gained, stop"; break; }
done
say "done: best $best_len ($(cat "$DIR/best.txt" 2>/dev/null))"
