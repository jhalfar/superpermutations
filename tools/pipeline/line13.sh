#!/bin/bash
# line13.sh W0 L D: an n = 13 line from any word in N labels (the labels of the base word BASEN of base.sh).
# The word must already be in N labels (relabel it first otherwise).
# base.sh (hybrid base from the word, plan) -> tsnum.py (trailsearch numbering) -> loop.sh (GPU three cuts / trailsearch
# / longloop to a fixed point) -> prepub (--par 3) on the loop's best word, or on the start word if the loop gained
# nothing; repeat from prepub's word while it says SHORTER, at most 4 cycles.
# Log D/line.log, ends with "END best LEN word W".
# Environment: as base.sh and loop.sh (BASEN, TOOLS, PYTHON, GUARD).
H=$(cd "$(dirname "$0")" && pwd); W0=$1; L=$2; D=$3; B=$D/base
PY=${PYTHON:-$(command -v python3 || command -v python)}
mkdir -p $D; LOG=$D/line.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $LOG; }
say "start $L $W0"
MAP=0123456789ABC bash $H/base.sh $W0 $B
say "base: $(tail -3 $B/base.log | tr '\n' ' ')"
[ -f $B/w.plan ] || { say "no plan; stop"; say "END best $L word $W0"; exit 1; }
nice -n 19 "$PY" -I $H/tsnum.py $B/base.txt $B/base_p.tsv $B/w.plan $B/w.ts.plan > $B/tsnum.log 2>&1
say "tsnum exit $?: $(tail -1 $B/tsnum.log)"
export BASE=$B/base.txt
P=$B/w.ts.plan; W=$B/wN.txt
for c in 1 2 3 4; do
  bash $H/loop.sh $D/loop$c $P $L 6
  line=$(grep "END best" $D/loop$c/loop.log | tail -1)
  lw=$(echo "$line" | grep -o 'word [^ ]*' | cut -d' ' -f2)
  if [ -n "$lw" ] && [ -f "$lw" ]; then
    L=$(echo "$line" | grep -o 'best [0-9]*' | cut -d' ' -f2); P=$(echo "$line" | grep -o 'plan [^ ]*' | cut -d' ' -f2); W=$lw
  fi
  say "cycle $c loop: $L word $W plan $P"
  nice -n 19 bash $H/../prepub/prepub.sh 13 $W --base $BASE --plan $P --threads 4 --par 3 --out $D/prepub$c > $D/prepub$c.log 2>&1
  rep=$D/prepub$c/REPORT.txt
  v=$(grep -E "CLEAN|SHORTER" $rep | tail -1)
  say "cycle $c prepub: $v"
  case "$v" in
    *SHORTER:*)
      L=$(echo "$v" | grep -o 'SHORTER: [0-9]*' | cut -d' ' -f2)
      W=$(echo "$v" | grep -o 'in [^ ,]*' | head -1 | cut -d' ' -f2); P=$W.plan ;;
    *) break ;;
  esac
done
say "END best $L word $W"
