#!/bin/bash
# ils12.sh DIR PLAN LEN [ROUNDS=20] [SEC=3000]: n = 12 on a hybrid base (env BASE, required).  A round: tools/polish.sh
# (dpa, or3 5 slack 1, loopscan; 4 threads), then two segins_ils lanes side by side (kmax 2 and kmax 3, 2 threads
# each, SEC seconds, new seeds each round) from the best plan; the best valid word (delcheck) goes on.  Stops after
# a round without gain or on DIR/STOP.  Log DIR/ils.log ends with END.
# Environment: TOOLS = directory of the binaries of tools/ (default: the directory of this script); GUARD as in
# loop.sh (I used a 12 GB guard per job).
H=$(cd "$(dirname "$0")" && pwd); B=${TOOLS:-$H}; D=$1; PLAN=$2; best=$3; NR=${4:-20}; SEC=${5:-3000}
BASE=${BASE:?set BASE}; G=${GUARD-}
mkdir -p $D; L=$D/ils.log; say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $L; }
take() {   # tag length plan word
  if [ -n "$2" ] && [ "$2" -lt "$best" ] && [ -f "$4" ] && $B/delcheck "$4" 2 > "$4.delcheck.json" 2>&1 && grep -q '"missing_permutations":0' "$4.delcheck.json"; then
    best=$2; PLAN=$3; g=1; say "$1: $2 valid ($4)"; else say "$1: no gain ($2)"; fi; }
say "start plan $PLAN best $best"
for r in $(seq 1 $NR); do
  [ -f $D/STOP ] && break
  g=0
  TOOLS=$B nice -n 19 $G bash $H/../polish.sh $D/p$r $BASE $PLAN 4 6 "--or3 5 --or3-slack 1" > $D/p$r.out 2>&1
  if [ -f $D/p$r/best.txt ]; then read b p w < $D/p$r/best.txt; take "round $r polish" "$b" "$p" "$w"; fi
  for k in 2 3; do mkdir -p $D/i$r$k
    nice -n 19 $G $B/segins_ils $BASE $D/i$r$k/o.txt --plan-in $PLAN --time 0 --threads 2 --seed $((r * 100 + k * 7)) \
      --ils $SEC --ils-log 600 --ils-kmax $k --ils-slack 2 --ils-near -1 --ils-cuts 3 --or3-stop $D/STOP > $D/i$r$k/o.log 2>&1 &
  done; wait
  for k in 2 3; do b=$(grep -o "wrote .* length [0-9]*" $D/i$r$k/o.log | tail -1 | grep -o "[0-9]*$"); take "round $r ils kmax $k" "$b" "$D/i$r$k/o.txt.plan" "$D/i$r$k/o.txt"; done
  echo "$best $PLAN" > $D/best.txt
  [ $g = 0 ] && break
done
say "done best $best plan $PLAN"; say END
