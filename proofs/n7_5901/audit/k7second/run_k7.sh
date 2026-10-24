#!/bin/bash
# Second count of K7 (PROOF_5901.md Table C) with the audit's program k2_s12 (written from the texts,
# programs/second/k2_s12.cpp), on the table of the card run (table/capD16u_7_k.txt).
# Statement: S 7, LO 35, G 54 (levels 36..54), CUT 12, potential 10,16,25. Gate at depth 8, 64 parts, 2 workers.
# Part files parts/p<i>.txt; a finished or claimed part is skipped, so the same line can be repeated.
cd "$(dirname "$0")" || exit 2
EXE=../../../../audit_20261020/k2_s12.exe
TAB=../../gpu2/k/caps/capD16u_7_k.txt
N=64; DEPTH=8; TH=${1:-2}
mkdir -p parts
echo "$TAB 7 35 54 12 10 16 25 $DEPTH $N" > parts/command.txt
date '+start %F %T' >> run.log
for ((i=0;i<N;i++)); do [ -f parts/p$i.txt ] || echo $i; done | \
  nice -n 19 xargs -P $TH -I{} $EXE $TAB 7 35 54 12 10 16 25 $DEPTH $N {} parts/p{}.txt
date '+end %F %T' >> run.log
