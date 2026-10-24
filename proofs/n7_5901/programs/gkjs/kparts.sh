#!/bin/bash
# kparts.sh TAG S LO NPARTS DEPTH A B H CAPS [GTOP]   (agent n7-gkjs; kparts.sh of gpu2/k for run/gkjs.exe + run/gkjs.ptx)
# The kernel-alone statement F_S on the levels LO < x <= GTOP - 6 S (GTOP default 96) on the card, CUT=12, potential A,B,H,
# Rule JS by the environment (JS=1 on, JS=0 off = the production program; must be given), in NPARTS parts (prefixes of DEPTH
# rows by index modulo NPARTS; the numbering depends on JS and on the potential).  One file per finished part:
# parts/TAG/p<i>.txt; the same line again does the missing parts only.  A tag belongs to one set of parameters: the line is
# refused if parts/TAG/params.txt differs.  Environment: JS (0 | 1), MAXSEC (default 200000: a part that hits it is lost),
# FIRST, LAST or PLIST="i j .." (only these parts).
cd "$(dirname "$0")"
TAG=$1; S=$2; LO=$3; N=$4; DEP=$5; PA=$6; PB=$7; PH=$8; CAPS=$9; GTOP=${10:-96}
[ "$JS" == 0 ] || [ "$JS" == 1 ] || { echo "set JS=0 or JS=1"; exit 2; }
[ -n "$CAPS" ] && [ -s "$CAPS" ] || { echo "usage: JS=1 ./kparts.sh TAG S LO NPARTS DEPTH A B H CAPS [GTOP]"; exit 2; }
export MAXSEC=${MAXSEC:-200000}
dir=parts/$TAG; mkdir -p $dir
par="S=$S LO=$LO NPARTS=$N DEPTH=$DEP CAPS=$CAPS GTOP=$GTOP CUT=12 POT=$PA,$PB,$PH JS=$JS exe=run/gkjs.exe"
if [ -s $dir/params.txt ]; then [ "$(cat $dir/params.txt)" == "$par" ] || { echo "tag $TAG was started with other parameters: $(cat $dir/params.txt)"; exit 2; }
else echo "$par" > $dir/params.txt; fi
for i in ${PLIST:-$(seq ${FIRST:-0} ${LAST:-$((N - 1))})}; do
  f=$dir/p$i.txt; [ -s $f ] && continue
  (cd run && JS=$JS PART=$i NPARTS=$N DEPTH=$DEP LO=$LO CUT=12 POTA=$PA POTB=$PB POTH=$PH ./gkjs.exe run $S $GTOP ../$CAPS) > $f.tmp 2>> $dir/err.txt && grep -q "violations" $f.tmp && mv $f.tmp $f
done
echo "$(date '+%F %T') $TAG: $(ls $dir | grep -c '^p[0-9]*\.txt$') of $N parts" >> $dir/log.txt
