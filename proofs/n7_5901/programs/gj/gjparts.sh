#!/bin/bash
# gjparts.sh TAG NPARTS DEPTH NPARTS2 CAPS V W B piece...   (agent n7-gpuj)
# The statement J(pieces; V, W; B) on the card (gj.exe + gj7.ptx) in NPARTS x NPARTS2 parts, one after the other:
# part (i, j) = nodes at DEPTH rows of piece 1 with index i mod NPARTS (the gate of jt.c / jr.c: PART, NPARTS, DEPTH)
# and start vertices v of piece 2 with v mod NPARTS2 = j (PART2, NPARTS2); NPARTS2 = 1: no second gate.
# The environment is passed on: RLO RHI ORD REV RMODE RP PA PB PH JCAP, card: GN GK MAXSEC.
# One file per finished part: parts/TAG/p<i>_<j>.txt (written as .tmp, renamed when it has a RESULT line).
# The same line again does the missing parts only.  Sum and check: ./gjsumm.sh TAG NPARTS NPARTS2
cd "$(dirname "$0")"
TAG=$1; NP=$2; DEP=$3; NP2=$4; CAPS=$5; shift 5
dir=parts/$TAG; mkdir -p $dir
echo "gj.exe 7 $CAPS run $* NPARTS=$NP DEPTH=$DEP NPARTS2=$NP2 RLO=$RLO RHI=$RHI ORD=$ORD REV=$REV RMODE=$RMODE RP=$RP PA=$PA PB=$PB PH=$PH JCAP=$JCAP" > $dir/command.txt
for i in $(seq 0 $((NP - 1))); do for j in $(seq 0 $((NP2 - 1))); do
  f=$dir/p${i}_$j.txt; [ -s $f ] && continue
  PART=$i NPARTS=$NP DEPTH=$DEP PART2=$j NPARTS2=$NP2 ./gj.exe 7 $CAPS run $* > $f.tmp 2>> $dir/err.txt && grep -q "^RESULT" $f.tmp && mv $f.tmp $f
done; done
echo "$(date '+%F %T') $TAG: $(ls $dir | grep -c '^p[0-9_]*\.txt$') of $((NP * NP2)) parts" >> $dir/log.txt
