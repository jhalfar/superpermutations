#!/bin/bash
# gj3parts.sh TAG NPARTS DEPTH NPARTS2 CAPS V W B piece...   (n7-tune16; gj2parts.sh of n7-gpu2 for gj3.exe = gj2 + RVMIN; CAPS relative to this directory)
# J(pieces; V, W; B) on the card in NPARTS x NPARTS2 parts, one after the other: part (i, j) = nodes at DEPTH rows of
# piece 1 with index i mod NPARTS and start vertices v of piece 2 with v mod NPARTS2 = j.  DEPTH = 0: no first gate.
# Environment passed on: RLO RHI RVMIN ORD ORDS REV RMODE RP PA PB PH JCAP, card: GN GK MAXSEC (default here 1500 s).
# One file per finished part: parts/TAG/p<i>_<j>.txt; the same line again does the missing parts only (resumable).
# Only parts FIRST..LAST (environment, default all) are run, or the parts listed in PLIST ("3 67 131"): a part i of N that
# hit MAXSEC is redone as the parts i, i + N, .., i + (M - 1) N of N M under a new TAG (same nodes, by the modulo rule).
cd "$(dirname "$0")"
TAG=$1; NP=$2; DEP=$3; NP2=$4; CAPS=$5; shift 5
dir=parts/$TAG; mkdir -p $dir
echo "gj3.exe 7 $CAPS run $* NPARTS=$NP DEPTH=$DEP NPARTS2=$NP2 RLO=$RLO RHI=$RHI RVMIN=$RVMIN ORD=$ORD ORDS=$ORDS REV=$REV RMODE=$RMODE RP=$RP PA=$PA PB=$PB PH=$PH JCAP=$JCAP" > $dir/command.txt
for i in ${PLIST:-$(seq ${FIRST:-0} ${LAST:-$((NP - 1))})}; do for j in $(seq 0 $((NP2 - 1))); do
  f=$dir/p${i}_$j.txt; [ -s $f ] && continue
  if [ $DEP -gt 0 ]; then g="PART=$i NPARTS=$NP DEPTH=$DEP"; else g="X=1"; fi
  env $g PART2=$j NPARTS2=$NP2 ./gj3.exe 7 $CAPS run $* > $f.tmp 2>> $dir/err.txt && grep -q "^RESULT" $f.tmp && mv $f.tmp $f
done; done
echo "$(date '+%F %T') $TAG: $(ls $dir | grep -c '^p[0-9_]*\.txt$') of $((NP * NP2)) parts" >> $dir/log.txt
