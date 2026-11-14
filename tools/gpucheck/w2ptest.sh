#!/bin/bash
# w2ptest.sh TAG BASE WORD - w2p13o (tools/pipeline/w2p13.c, processor) and w2p13g (card) on the same base and word,
# 3 threads each (OMP_NUM_THREADS=3), nice 19: the plans must have the same SHA-256 and the logs the same lines
# apart from the times.  Line in WORK/val/w2ptest.tsv; compare with val/w2ptest.tsv next to this script (my run).
# Environment: WORK = work directory (required); TOOLS = directory of w2p13o, w2p13g and w2pg.ptx (default: the
# directory of this script); GUARD = a command put in front of both runs (default none; I used a 16 GB guard).
H=$(cd "$(dirname "${BASH_SOURCE:-$0}")" && pwd); B=${TOOLS:-$H}
TAG=$1; BASE=$2; WORD=$3
O=${WORK:?set WORK}/w2p; mkdir -p $O $WORK/val || exit 1
export OMP_NUM_THREADS=3
waitgpu() { while ! bash $H/gpubusy.sh > /dev/null; do sleep 60; done; }
s=$(date +%s.%N)
nice -n 19 ${GUARD-} $B/w2p13o "$BASE" "$WORD" $O/${TAG}_o.plan > $O/${TAG}_o.log 2>&1; ro=$?
m=$(date +%s.%N)
waitgpu
m2=$(date +%s.%N)
nice -n 19 ${GUARD-} $B/w2p13g "$BASE" "$WORD" $O/${TAG}_g.plan > $O/${TAG}_g.log 2>&1; rg=$?
e=$(date +%s.%N)
ho=$(sha256sum < $O/${TAG}_o.plan | cut -c1-16); hg=$(sha256sum < $O/${TAG}_g.plan | cut -c1-16)
lo=$(grep -v "^\[guard\]" $O/${TAG}_o.log | sed 's/ ([0-9]*s)//' | sha256sum | cut -c1-12)
lg=$(grep -v "^\[guard\]" $O/${TAG}_g.log | sed 's/ ([0-9]*s)//' | sha256sum | cut -c1-12)
ok=1; [ "$ho" = "$hg" ] && [ "$lo" = "$lg" ] && [ $ro = $rg ] || ok=0
line="$TAG	$([ $ok = 1 ] && echo SAME || echo DIFFER)	plan $ho/$hg log $lo/$lg exit $ro/$rg	w2p13o $(awk "BEGIN{printf \"%.0f\", $m - $s}") s	w2p13g $(awk "BEGIN{printf \"%.0f\", $e - $m2}") s	$(grep -o 'peak committed memory of the job [0-9.]* GB' $O/${TAG}_g.log)"
echo "$line" >> $WORK/val/w2ptest.tsv; echo "$line"
