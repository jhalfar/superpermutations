#!/bin/bash
# base.sh WORD DIR: n = 13 word -> N labels (env MAP: target labels for tr '0123456789ABC' MAP; 0123456789ABC keeps
#    the letters as they are)
# -> hybrid base from the word itself (hyb13 on the base word of selection N, env BASEN) -> base_p.tsv (pieces) +
#    base.tsv (X 0 len-10 start) -> plan (w2p13o + unitsplit.py).  Every job nice 19, 6 threads.
# Log DIR/base.log, ends with END.
# Environment: TOOLS = directory of the binaries hyb13, pieces, w2p13o, vfast (default: the directory of this
# script); PYTHON (default python3); GUARD = a command put in front of every job, e.g.
# GUARD="$PYTHON -I tools/pipeline/guard.py --gb 20 --" (default: none).
H=$(cd "$(dirname "$0")" && pwd); B=${TOOLS:-$H}; W=$1; D=$2
BN=${BASEN:?set BASEN}; PY=${PYTHON:-$(command -v python3 || command -v python)}; G=${GUARD-}
mkdir -p $D; L=$D/base.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $L; }
vf() { nice -n 19 $B/vfast 13 0123456789ABC < $1 | grep -o '"length":[0-9]*\|"missing":[0-9]*\|"repeats":[0-9]*' | tr '\n' ' '; }
say "start $W"
[ -f $D/wN.txt ] || tr -d '\r\n' < $W | tr '0123456789ABC' ${MAP:?set MAP} > $D/wN.txt
say "relabelled: $(vf $D/wN.txt) first $(head -c 13 $D/wN.txt)"
if [ ! -f $D/base.txt ]; then
  OMP_NUM_THREADS=6 nice -n 19 $G $B/hyb13 $BN $D/wN.txt $D/base.txt --no-rotate > $D/hyb13.log 2>&1
  say "hyb13 exit $?: $(grep '^wrote' $D/hyb13.log)"
fi
OMP_NUM_THREADS=6 nice -n 19 $G $B/pieces $D/base.txt 13 $D/base_p.tsv > $D/base_p.log 2>&1
say "pieces exit $?: $(tail -1 $D/base_p.log)"
awk -F'\t' -v OFS='\t' '{print "X", 0, $3 - 10, $2}' $D/base_p.tsv > $D/base.tsv
say "base.tsv $(wc -l < $D/base.tsv) rows"
OMP_NUM_THREADS=6 nice -n 19 $G $B/w2p13o $D/base.txt $D/wN.txt $D/w.plan.w2p > $D/w2p.log 2>&1
say "w2p13o exit $?: $(grep -o 'events.*anomalies [0-9]*' $D/w2p.log | head -1)"
nice -n 19 $G "$PY" -I $H/unitsplit.py $D/base.txt $D/base.tsv $D/w.plan.w2p $D/w.plan >> $D/w2p.log 2>&1
say "unitsplit exit $?: $(tail -2 $D/w2p.log | tr '\n' ' ')"
say END
