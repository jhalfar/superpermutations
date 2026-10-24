#!/bin/bash
# Second count of T7 = J(S1 S1 R R; 62, 70; 3), all rings (PROOF_5901.md Table C: kept 1,432,335,917,907,
# tried 7,283,065,963,552), with the audit's j2_np5.exe (= programs/second/j2_np5.cpp: j2.cpp of defect 15 with five pieces, written from the
# texts), table table/capD.txt, rings 0..96.  Gate on piece 2 at its first row, 8 parts (j2 follows a piece 1
# that completes above a gate on piece 1 in part 0 only, so a gate on piece 1 left much of the work in part 0 in a first try; with
# the gate on piece 2 every part repeats the search of piece 1, about 1.5 h, and splits the rest); one file per part
# (parts/p<i>.txt); finished or claimed parts are skipped, so the same line resumes the run.
# usage: ./run_t7.sh [THREADS]     after a kill: rm parts/*.claim parts/*.tmp (only when no worker runs), then again
cd "$(dirname "$0")" || exit 2
EXE=../../../../audit_20261020/j2_np5.exe
TAB=../../jrev/capD.txt
N=8; GP=2; DEPTH=1; TH=${1:-2}
mkdir -p parts
CMD="$TAB 62 70 3 0 96 $GP $DEPTH $N S1 S1 R R"
if [ -f parts/command.txt ]; then
  [ "$(cat parts/command.txt)" = "$CMD" ] || { echo "parts/ was started with other parameters"; exit 2; }
else echo "$CMD" > parts/command.txt; fi
date '+start %F %T' >> run.log
for ((i=0;i<N;i++)); do [ -f parts/p$i.txt ] || echo $i; done | \
  nice -n 19 xargs -P $TH -I{} $EXE $TAB 62 70 3 0 96 $GP $DEPTH $N {} parts/p{}.txt S1 S1 R R
date '+end %F %T' >> run.log
