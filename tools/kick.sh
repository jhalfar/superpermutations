#!/bin/bash
# kick.sh - a new starting point for the passes when they find nothing more.
#
# A short search at a constant high temperature (a "kick") from the best plan ends on a sequence a few letters longer
# than the best one.  The search program writes the end sequence of every thread (--drift), and each of them goes
# through polish.sh (relocation, loop moves, segment insertion).  A checked shorter word becomes the next start.
# At n = 12 this gave 522,745,376 -> 374 and 522,745,366 -> 356 -> 355.  At n = 11 it found nothing below 43,930,614.
#
# usage: kick.sh DIR BASE PLAN0 KICKS THREADS SEED0 [ITERS=60000] [T0LIST="1.2 0.6 0.9"] [KMAX=14] [PTHREADS=4] [STEPS="dpa loop or3"]
#
# What I used at n = 12: KOR3="--or3 5 --or3-slack 1" kick.sh DIR BASE PLAN 12 2 SEED
# Environment: TOOLS = directory of the binaries and of kern.ptx (default: the directory of this script);
# GPU = 1 (default: the search runs with --gpu --ptx TOOLS/kern.ptx) or 0 (the CPU path of the same program: the same
# search, much slower); KOPT = search options after the fixed ones (default "--cosync --drift 1000");
# KOR3 = options of the segment-insertion step (default "--or3 3 --or3-slack 0"); BEST0 = length to beat; OR3TIME.
T=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
[ $# -ge 6 ] || { sed -n '2,15p' "$0"; exit 1; }
DIR=$1; BASE=$2; PLAN=$3; KICKS=$4; THR=$5; SEED=$6; ITERS=${7:-60000}; T0S=(${8:-1.2 0.6 0.9}); KMAX=${9:-14}; PT=${10:-4}; STEPS=${11:-dpa loop or3}
GOPT="--gpu --ptx $T/kern.ptx"; [ "${GPU:-1}" = 1 ] || GOPT=""
mkdir -p "$DIR"; LOG=$DIR/steps.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a "$LOG"; }
len_of() { grep -o 'wrote .* length [0-9]*' "$1" | tail -1 | grep -o '[0-9]*$'; }
best=$(grep -o '^[0-9]*' "$DIR/best.txt" 2>/dev/null); [ -z "$best" ] && best=${BEST0:-999999999999}
bestw=""
say "start: base $BASE plan $PLAN kicks $KICKS threads $THR iters $ITERS T0 '${T0S[*]}' kmax $KMAX best $best"
for k in $(seq 1 "$KICKS"); do
  TK=${T0S[$(( (k - 1) % ${#T0S[@]} ))]}
  rm -f "$DIR"/k$k.txt.drift*.plan
  OMP_NUM_THREADS=$THR nice -n 19 "$T/trailsearch_gpu" "$BASE" "$DIR/k$k.txt" --plan-in "$PLAN" --threads "$THR" --time 100000 --iters "$ITERS" --seed $((SEED + k)) --kmax "$KMAX" --T0 "$TK" --focus 0.8 --sync 100000 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --co-skip ${KOPT:---cosync --drift 1000} $GOPT > "$DIR/k$k.log" 2> "$DIR/k$k.err"
  L=$(len_of "$DIR/k$k.log"); rm -f "$DIR/k$k.txt"
  n=0
  for dp in "$DIR"/k$k.txt.drift*.plan; do
    [ -f "$dp" ] || continue
    n=$((n + 1)); P=$DIR/k${k}_$n
    TOOLS=$T OR3TIME=${OR3TIME:-2700} bash "$T/polish.sh" "$P" "$BASE" "$dp" "$PT" 2 "${KOR3:---or3 3 --or3-slack 0}" "$STEPS" > "$P.out" 2>&1
    PL=; PP=; PW=; [ -f "$P/best.txt" ] && read -r PL PP PW < "$P/best.txt"
    if [ -n "$PL" ] && [ "$PL" -lt "$best" ]; then
      best=$PL; cp "$PP" "$DIR/best_$PL.plan"; PLAN=$DIR/best_$PL.plan
      [ -n "$bestw" ] && rm -f "$bestw"; bestw=$DIR/best_$PL.txt; mv "$PW" "$bestw"; cp "$PW.delcheck.json" "$bestw.delcheck.json" 2>/dev/null
      echo "$PL $PLAN $bestw" > "$DIR/best.txt"; say "kick $k (T0 $TK) thread plan $n: polished $PL  NEW BEST"
    else
      say "kick $k (T0 $TK, search end '$L') thread plan $n: polished '$PL' (best $best)"
    fi
    rm -rf "$P" "$P.out"
  done
  [ $n = 0 ] && say "kick $k: no thread ended within the drift limit ($(tail -1 "$DIR/k$k.err" | cut -c1-120))"
done
say "done: best $best"
