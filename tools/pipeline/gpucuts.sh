#!/bin/bash
# gpucuts.sh N DIR PLAN LEN: GPU segment insertion with more cuts than the loops use (four cuts slack 0, five cuts
# slack 0, five cuts slack 1, --or3-long 600), each pass from the best plan so far.  Env BASE (required).
# Log DIR/gpu.log, ends with END.
# Environment: TOOLS, GUARD as in loop.sh.  Five cuts at n = 13 peak at about 19 GB; I ran this with a 34 GB guard.
H=$(cd "$(dirname "$0")" && pwd); N=$1; D=$2; P=$3; best=$4
: "${BASE:?set BASE}"; export BASE
mkdir -p $D; L=$D/gpu.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $L; }
say "start n=$N $best plan $P base $BASE"
i=0
for opts in "--or3 4 --or3-slack 0 --or3-gpu" \
            "--or3 5 --or3-slack 0 --or3-long 600 --or3-gpu" \
            "--or3 5 --or3-slack 1 --or3-long 600 --or3-gpu"; do
  i=$((i + 1)); g=$D/p$i
  TSW=$H/tswg.sh MAXCAND=200000 bash $H/../gpucuts/orx.sh $g $P $best "$opts" 3600 6 > $g.out 2>&1
  gl=$(grep -o 'done: best [0-9]*' $g/steps.log 2>/dev/null | grep -o '[0-9]*$')
  if [ -n "$gl" ] && [ "$gl" -lt "$best" ] && [ -f $g/s1.keep.plan ]; then
    best=$gl; P=$g/s1.keep.plan; say "pass $i ($opts): $best word $g/s1.txt"
  else
    say "pass $i ($opts): no gain ($(tail -1 $g/steps.log 2>/dev/null); $(grep -h 'out of memory' $g/s1.log 2>/dev/null | head -1))"
  fi
done
say "END best $best plan $P"
