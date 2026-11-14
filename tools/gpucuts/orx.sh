#!/bin/bash
# orx.sh - segment-insertion passes, one setting after another, each from the best plan so far.
# Every word is checked with delcheck; only the best word stays on disk.  Stop a pass cleanly with: touch DIR/STOP
# MAXCAND = batch size of the judging (default 3000; with judging on the card, tsw5g2 --or3-gpu, use 200000).
# BASE = base word (required).  TSW = the segment-insertion program (default: tsw5g2 in TOOLS); it may be a command
# with arguments, e.g. a memory guard in front of the program.  TOOLS = directory of the binaries (default: the
# directory of this script); delcheck is taken from there.
# usage: orx.sh DIR PLAN0 BEST0 "SETTING|SETTING|..." [SEC=5400] [THREADS=8]
#   e.g. BASE=base.txt MAXCAND=200000 orx.sh or13d w.plan 6747916917 "--or3 5 --or3-slack 0 --or3-gpu|--or3 5 --or3-slack 1 --or3-gpu"
B=${TOOLS:-$(cd "$(dirname "${BASH_SOURCE:-$0}")" && pwd)}
DIR=$1; PLAN=$2; best=$3; IFS="|" read -r -a SET <<< "$4"; SEC=${5:-5400}; THR=${6:-8}
BASE=${BASE:?set BASE}; TSW=${TSW:-$B/tsw5g2}; mkdir -p $DIR; LOG=$DIR/steps.log; bestw=""
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a $LOG; }
say "start: plan $PLAN best $best settings '$4' seconds $SEC threads $THR program $TSW"
i=0
for S in "${SET[@]}"; do
  i=$((i + 1)); t=$DIR/s$i; rm -f $DIR/STOP
  touch $t.log.start; rm -f $t.txt.plan
  OMP_NUM_THREADS=$THR nice -n 19 $TSW $BASE $t.txt --plan-in "$PLAN" --time 0 --threads $THR $S --or3-maxcand ${MAXCAND:-3000} --or3-sec $SEC --or3-stop $DIR/STOP > $t.log 2>&1
  L=$(grep -a -o 'wrote .* length [0-9]*' $t.log | tail -1 | grep -o '[0-9]*$')
  # The run can die after a round wrote its plan (e.g. out of memory in the next round): render that plan.
  if [ -z "$L" ] && [ -f $t.txt.plan ] && [ $t.txt.plan -nt $t.log.start ]; then
    say "setting $i: run ended without a word; rendering its last plan"; cp $t.txt.plan $t.rescue.plan
    OMP_NUM_THREADS=$THR nice -n 19 $TSW $BASE $t.txt --plan-in $t.rescue.plan --time 0 --threads $THR > $t.render.log 2>&1
    L=$(grep -a -o 'wrote .* length [0-9]*' $t.render.log | tail -1 | grep -o '[0-9]*$'); cp $t.rescue.plan $t.txt.plan
  fi
  if [ -n "$L" ] && [ -f $t.txt ] && [ "$L" -lt "$best" ] && nice -n 19 $B/delcheck $t.txt $THR > $t.txt.delcheck.json 2>&1 && grep -q '"missing_permutations":0' $t.txt.delcheck.json; then
    [ -n "$bestw" ] && rm -f "$bestw"
    best=$L; bestw=$t.txt; cp $t.txt.plan $t.keep.plan; PLAN=$t.keep.plan
    echo "$L $PLAN $bestw" > $DIR/best.txt; say "setting $i ($S): $L valid  NEW BEST"
  else
    say "setting $i ($S): no gain (length '$L', best $best)"; rm -f $t.txt
  fi
done
say "done: best $best"
