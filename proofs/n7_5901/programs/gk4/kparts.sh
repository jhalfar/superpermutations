#!/bin/bash
# kparts.sh TAG S LO NPARTS DEPTH A B H CAPS [GTOP]   (n7-gpu2; gparts.sh of n7-gpu with a tag and the kernel file of gpu2/k/run)
# The kernel-alone statement F_S on the levels LO < x <= GTOP - 6 S (GTOP default 96) on the card, CUT=12, potential
# A,B,H, in NPARTS parts (prefixes of DEPTH rows by index modulo NPARTS, as kfast2.exe).  One file per finished part:
# parts/TAG/p<i>.txt; the same line again does the missing parts only.  FIRST, LAST (environment): only these parts.
cd "$(dirname "$0")"
TAG=$1; S=$2; LO=$3; N=$4; DEP=$5; PA=$6; PB=$7; PH=$8; CAPS=$9; GTOP=${10:-96}
dir=parts/$TAG; mkdir -p $dir
echo "S=$S LO=$LO NPARTS=$N DEPTH=$DEP CAPS=$CAPS GTOP=$GTOP CUT=12 POT=$PA,$PB,$PH exe=run/gk4.exe" > $dir/params.txt
for i in $(seq ${FIRST:-0} ${LAST:-$((N - 1))}); do
  f=$dir/p$i.txt; [ -s $f ] && continue
  (cd run && PART=$i NPARTS=$N DEPTH=$DEP LO=$LO CUT=12 POTA=$PA POTB=$PB POTH=$PH ./gk4.exe run $S $GTOP ../$CAPS) > $f.tmp 2>> $dir/err.txt && grep -q "violations" $f.tmp && mv $f.tmp $f
done
echo "$(date '+%F %T') $TAG: $(ls $dir | grep -c '^p[0-9]*\.txt$') of $N parts" >> $dir/log.txt
