#!/bin/bash
# loop.sh DIR PLAN LEN [MAXIT=6]: an n = 13 loop to a fixed point on a hybrid base (env BASE, required), at most 6
#   threads, a wait for a free card before each GPU pass, and old words deleted (only the best word so far is kept).
#   GPU segment insertion (tools/gpucuts/orx.sh, tsw5g2 --or3 3 --or3-slack 0 --or3-gpu, 2400 s, 6 threads, through
#   tswg.sh) while it gains; then one round of trailsearch (kmax 8 T0 0.4, 1200 s, 4 threads) + longloop.sh (loopscan
#   up to 1000 rounds, 6 threads); stop when a GPU pass and the trailsearch/loopscan round both gain 0.
#   Log DIR/loop.log, ends with "END best LEN plan PLAN word WORD".
# Environment: TOOLS = directory of the binaries (tsw5g2, trailsearch, loopscan, delcheck, vfast; default: the
# directory of this script); GUARD = a command put in front of every job, e.g.
# GUARD="$PYTHON -I tools/pipeline/guard.py --gb 20 --" (default: none); TSTIME = seconds of trailsearch (1200).
H=$(cd "$(dirname "$0")" && pwd); B=${TOOLS:-$H}; D=$1; P=$2; best=$3; MAXIT=${4:-6}
: "${BASE:?set BASE}"; export BASE
G=${GUARD-}
mkdir -p $D; L=$D/loop.log; bestw=""
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $L; }
plen() { grep -a -o 'length [0-9]*' $1 | tail -1 | grep -o '[0-9]*'; }
keep() {  # keep() WORD: the new best word; delete the previous one
  [ -n "$bestw" ] && [ "$bestw" != "$1" ] && rm -f "$bestw"; bestw=$1; }
gpuwait() {  # wait up to 30 min while another job uses the card (util > 30 % or > 12 GB used)
  for k in $(seq 1 15); do
    q=$(nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader,nounits | tr -d ' ')
    u=${q%,*}; m=${q#*,}
    [ "$u" -le 30 ] && [ "$m" -le 12000 ] && return
    say "card busy ($u %, $m MiB), waiting"; sleep 120
  done; }
say "start $best plan $P base $BASE"
for it in $(seq 1 $MAXIT); do
  g=$D/g$it; gpuwait
  TSW=$H/tswg.sh MAXCAND=200000 bash $H/../gpucuts/orx.sh $g $P $best "--or3 3 --or3-slack 0 --or3-gpu" 2400 6 > $g.out 2>&1
  gl=$(grep -o 'done: best [0-9]*' $g/steps.log | grep -o '[0-9]*$')
  if [ -n "$gl" ] && [ "$gl" -lt "$best" ] && [ -f $g/s1.keep.plan ]; then
    best=$gl; P=$g/s1.keep.plan; keep $g/s1.txt; say "it $it GPU: $best ($g/s1.txt)"; continue
  fi
  say "it $it GPU: no gain ($(tail -1 $g/steps.log))"
  t=$D/t$it; mkdir -p $t; tw=$t/r1t.txt
  OMP_NUM_THREADS=4 nice -n 19 $G $B/trailsearch $BASE $tw --plan-in $P \
    --time ${TSTIME:-1200} --seed $((it * 11)) --kmax 8 --T0 0.4 --threads 4 --sync 15 --ckpt 300 --focus 0.85 > $tw.log 2>&1
  tl=$(plen $tw.log); [ -f $tw.plan ] || tl=""
  say "it $it trailsearch: ${tl:-no word}"
  cur=$P; [ -n "$tl" ] && cur=$tw.plan
  bash $H/longloop.sh $t/l $cur 1000 6
  ll=$(grep -o -- '-> [0-9]*' $t/l/ll.log | tail -1 | grep -o '[0-9]*')
  say "it $it longloop: ${ll:-none} ($(grep -o 'missing":[0-9]*' $t/l/ll.log | tail -1); $(grep -o 'deletions_count":[0-9]*' $t/l/w.txt.delcheck.json 2>/dev/null))"
  nb=""; np=""; nw=""
  if [ -n "$tl" ] && [ "$tl" -lt "$best" ]; then nb=$tl; np=$tw.plan; nw=$tw; fi
  if [ -n "$ll" ] && [ -f $t/l/w.txt.plan ] && [ "$ll" -lt "${nb:-$best}" ]; then nb=$ll; np=$t/l/w.txt.plan; nw=$t/l/w.txt; fi
  for x in $tw $t/l/w.txt; do [ "$x" != "$nw" ] && rm -f $x; done
  if [ -n "$nb" ]; then best=$nb; P=$np; keep $nw; say "it $it tl: $best ($nw)"
  else say "it $it tl: no gain; fixed point"; break; fi
done
say "END best $best plan $P word $bestw"
