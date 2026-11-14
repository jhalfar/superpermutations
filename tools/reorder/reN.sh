#!/bin/bash
# reN.sh N WORD LEN DIR [SECS=10800]: the cut-opening reorder (cutlns2.py, my rebuild of Jay Pantone's move of
# W-0107) on a word, in six lines side by side.  steps (weight >= 3) once, then six one-thread lines with different
# K / Rfine / chain settings for SECS seconds each, then gdelcheck on every written word.
# Log DIR/re.log, ends with "END best LEN word W".  Stop all lines cleanly with: touch DIR/STOP
# Environment: TOOLS = directory of the binaries steps and gdelcheck (default: the directory of this script);
# PYTHON = the Python with numpy, scipy and gurobipy (default python3); GUARD = a command put in front of every line,
# e.g. GUARD="$PYTHON -I tools/pipeline/guard.py --gb 8 --" (default: none).
H=$(cd "$(dirname "$0")" && pwd); B=${TOOLS:-$H}; N=$1; W=$2; L0=$3; D=$4; SECS=${5:-10800}
PY=${PYTHON:-$(command -v python3 || command -v python)}; G=${GUARD-}
mkdir -p $D; LOG=$D/re.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" >> $LOG; }
say "start $W $L0 secs $SECS"
[ -f $D/st.bin ] || nice -n 19 $B/steps $W $N 3 $D/st.bin > $D/steps.log 2>&1
say "steps: $(tail -1 $D/steps.log)"
CFG=("--K 4 --Rfine 1000 --seed 1" "--K 2 --Rfine 1000 --seed 2" "--K 4 --Rfine 300 --seed 3" \
     "--K 4 --Rfine 3000 --chain 1 --wbreak 6 --D 3 --seed 4" "--K 2 --Rfine 3000 --chain 1 --wbreak 6 --D 3 --seed 5" \
     "--K 6 --Rfine 1000 --heavy 0 --seed 6")
for i in 0 1 2 3 4 5; do
  O=$D/l$i; mkdir -p $O
  (OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 $G "$PY" -I $H/cutlns2.py \
    $W $N $D/st.bin $O --gfine 3 ${CFG[$i]} --threads 1 --time $SECS --stop $D/STOP > $O/out.log 2>&1; echo $? > $O/DONE) &
done
while [ $(ls $D/l*/DONE 2>/dev/null | wc -l) -lt 6 ]; do sleep 30; done
best=$L0; bw=$W
for i in 0 1 2 3 4 5; do
  f=$D/l$i/w.txt; [ -f $f ] || { say "line $i (${CFG[$i]}): no word"; continue; }
  l=$(tr -d '\r\n' < $f | wc -c)
  dc=$(nice -n 19 $B/gdelcheck $f 8 2>/dev/null | tail -1 | grep -o '"missing_permutations":[0-9]*\|"coverage_preserving_deletions_count":[0-9]*' | tr '\n' ' ')
  say "line $i (${CFG[$i]}): $l $dc"
  case "$dc" in *'missing_permutations":0 '*) [ "$l" -lt "$best" ] && { best=$l; bw=$f; } ;; esac
done
say "END best $best word $bw"
