#!/bin/bash
# longloop.sh DIR PLAN [ROUNDS=1000] [THREADS=6] [NBATCH=16]: the move of W-0100 (Jay Pantone's note: polish.sh's
# loopscan run for many more rounds than the default 40) on an n = 13 plan over a hybrid base (env BASE, required).
# nice 19.  Then delcheck and vfast of the word.  Log DIR/ll.log, ends with END.
# Environment: TOOLS = directory of loopscan, delcheck, vfast (default: the directory of this script); GUARD as in
# loop.sh (I used a 14 GB guard here).
H=$(cd "$(dirname "$0")" && pwd); X=${TOOLS:-$H}; D=$1; P=$2; NR=${3:-1000}; T=${4:-6}; NB=${5:-16}
B=${BASE:?set BASE}; G=${GUARD-}
mkdir -p $D; L=$D/ll.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $L; }
say "start plan $P rounds $NR threads $T nbatch $NB base $B"
OMP_NUM_THREADS=$T nice -n 19 $G $X/loopscan $B --plan $P --only PABD --nogap1 \
  --threads $T --quiet --greedy --neutral --nbatch $NB --maxrounds $NR --planout $D/w.txt.plan --out $D/w.txt > $D/loop.log 2>&1
say "loopscan exit $?: $(grep -o 'greedy: .*' $D/loop.log | tail -1)"
if [ -f $D/w.txt ]; then
  nice -n 19 $X/delcheck $D/w.txt $T > $D/w.txt.delcheck.json 2>&1
  say "delcheck: $(tr -d '\n' < $D/w.txt.delcheck.json | head -c 300)"
  say "vfast: $(nice -n 19 $X/vfast 13 0123456789ABC < $D/w.txt | grep -o '"length":[0-9]*,.*"missing":[0-9]*')"
fi
say END
