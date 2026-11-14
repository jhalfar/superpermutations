#!/bin/bash
# validate.sh [gcheck|gcheck13|gdel|gdel13|all] - gcheck and gdelcheck against the CPU tools
#   gcheck:   vfast (recipes/n14/vfast.c) and gcheck on record words n = 9..12 (plain, .txt.xz, stdin, 1 MB chunks,
#             buffered reads) and on corrupted words (corrupt: sub, del, swap, first, last; a foreign byte, a line
#             end inside, CRLF lines, lowercase letters, a word cut to N-1 letters): the 11 fields of vfast's line must
#             be equal and the exit codes too.
#   gcheck13: the same at n = 13 (record words and three corruptions).
#   gdel:     delcheck (tools/delcheck.c) and gdelcheck on the same words n = 9..12 and on words with a
#             deletable letter: every field except the times and the thread count must be equal, and the exit code.
#   gdel13:   the same at n = 13.
# One line per run in WORK/val/results.tsv, the JSON lines in WORK/val/; END line in WORK/val/validate.log.  Compare
# them with the val/ folder next to this script, which holds the results of my run.  nice 19; the card must be free
# (gpubusy.sh) before every card run.
# Environment: WORK = work directory (required; up to 14 GB for gcheck13 / gdel13); TOOLS = directory of the
# binaries gcheck, gdelcheck, vfast, delcheck, corrupt (default: the directory of this script) and of the .ptx files;
# GUARD = a command put in front of every check, e.g. GUARD="$PYTHON -I tools/pipeline/guard.py --gb 16 --" (default
# none).  Words that are not in this repository, each optional (the runs on them are left out without it):
# PANTONE_WORDS = the words/ folder of Jay Pantone's repository (9/, 10/, 11/); W9 = Theo H.'s n = 9 word of 408,731
# letters in letters 0-8; EXTRA12, EXTRA13 = a word of 522,736,434 and one of 6,747,800,516 letters (the val/ results
# "cutlns" were made on such words; the 6,747,800,516 word has one deletable letter).
H=$(cd "$(dirname "${BASH_SOURCE:-$0}")" && pwd); B=${TOOLS:-$H}
WHAT=${1:-all}
G() { nice -n 19 ${GUARD-} "$@"; }
PUB=$(cd "$H/../.." && pwd); PF=${PANTONE_WORDS:-}
T=${WORK:?set WORK}; mkdir -p "$T/val" || exit 1; cd "$T" || exit 1
LOG=val/validate.log; RES=val/results.tsv
VF=$B/vfast; CORR=$B/corrupt; DC=$B/delcheck
fail=0; runs=0
waitgpu() { while ! bash $H/gpubusy.sh > /dev/null; do echo "card busy, waiting 60 s" >> $LOG; sleep 60; done; }
have() { [ -n "$1" ] && [ -e "$1" ]; }
al() { echo 0123456789ABCDEF | cut -c1-$1; }
strip_g() { sed 's/,"alphabet".*/}/' "$1"; }                  # gcheck's line cut to vfast's fields
strip_d() { sed 's/,"scan_seconds".*//; s/,"pass1_seconds".*//' "$1"; }   # delcheck / gdelcheck without times
rec() {   # rec TAG OK DETAIL
  runs=$((runs + 1)); [ "$2" = 1 ] || fail=$((fail + 1))
  local line="$1	$([ "$2" = 1 ] && echo PASS || echo FAIL)	$3"
  echo "$line" >> $RES; echo "$line" >> $LOG; echo "$line"
}
# cmpv TAG N INPUT_FOR_VFAST(file) GCHECK_ARGS... : vfast on the file, gcheck with the args; compare
cmpv() {
  local tag=$1 n=$2 f=$3; shift 3
  local base=val/$(echo "$tag" | tr ' /' '__')
  local tv0=$(date +%s.%N)
  case "$f" in *.xz) nice -n 19 xz -T1 -dc "$f" | G $VF $n $(al $n) > $base.vf.json 2>> $LOG;; *) G $VF $n $(al $n) < "$f" > $base.vf.json 2>> $LOG;; esac; local rv=$?
  local tv=$(awk "BEGIN{printf \"%.1f\", $(date +%s.%N) - $tv0}")
  waitgpu; G $B/gcheck $n "$@" > $base.gc.json 2>> $LOG; local rg=$?
  local ok=1; [ "$(strip_g $base.gc.json)" = "$(cat $base.vf.json)" ] || ok=0; [ $rv = $rg ] || ok=0
  rec "gcheck $tag" $ok "exit vfast=$rv gcheck=$rg $(grep -o '"missing":[0-9]*' $base.gc.json) $(grep -o '"repeats":[0-9]*' $base.gc.json) $(grep -o '"foreign_bytes":[0-9]*' $base.gc.json) $(grep -o '"seconds":[0-9.]*' $base.gc.json) vfast_wall ${tv} s"
}
# cmpd TAG FILE [GDEL ARGS] : delcheck and gdelcheck on the file
cmpd() {
  local tag=$1 f=$2; shift 2
  local base=val/$(echo "$tag" | tr ' /' '__')
  G $DC "$f" 3 > $base.dc.json 2>> $LOG; local rv=$?
  waitgpu; G $B/gdelcheck "$f" 3 "$@" > $base.gd.json 2>> $LOG; local rg=$?
  local ok=1; [ "$(strip_d $base.gd.json)" = "$(strip_d $base.dc.json)" ] || ok=0; [ $rv = $rg ] || ok=0
  [ -s $base.dc.json ] || ok=0
  rec "gdelcheck $tag" $ok "exit delcheck=$rv gdelcheck=$rg $(grep -o '"missing_permutations":[0-9]*' $base.gd.json) $(grep -o '"coverage_preserving_deletions_count":[0-9]*' $base.gd.json) dc $(grep -o '"scan_seconds":[0-9.]*,"deletion_seconds":[0-9.]*' $base.dc.json) gd $(grep -o '"pass1_seconds":[0-9.]*,"pass2_seconds":[0-9.]*' $base.gd.json)"
}
unxz_to() { [ -s "$2" ] || nice -n 19 xz -T1 -dc "$1" | tr -d '\r\n' > "$2"; }
echo "validate $WHAT start $(date '+%F %T') gcheck.c $(sha256sum $H/gcheck.c | cut -c1-16) gpuprep.cu $(sha256sum $H/gpuprep.cu | cut -c1-16) gdelcheck.c $( [ -f $H/gdelcheck.c ] && sha256sum $H/gdelcheck.c | cut -c1-16)" >> $LOG

# the words n = 9 .. 12 as plain files without line ends
W9=${W9:-}; BEST12=${EXTRA12:-}; BEST13=${EXTRA13:-}
prep() {
  unxz_to "$PUB/words/superpermutation-10-4034855.txt.xz" $T/w10.txt
  unxz_to "$PUB/words/superpermutation-11-43930534.txt.xz" $T/w11.txt
  unxz_to "$PUB/words/superpermutation-12-522736969.txt.xz" $T/w12.txt
}
if [ $WHAT = gcheck ] || [ $WHAT = all ]; then
  prep
  have "$W9" && cmpv "n9 408731" 9 $W9 $W9
  have "$PF" && cmpv "n9 pantone 408732 (final LF)" 9 $PF/9/superpermutation-9-408732.txt $PF/9/superpermutation-9-408732.txt
  have "$PF" && cmpv "n9 pantone 408736" 9 $PF/9/superpermutation-9-408736.txt - < $PF/9/superpermutation-9-408736.txt
  have "$PF" && for f in $PF/10/*.txt; do cmpv "n10 $(basename $f)" 10 $f $f; done
  cmpv "n10 4034855 plain" 10 $T/w10.txt $T/w10.txt
  cmpv "n10 4034855 1MB chunks buffered" 10 $T/w10.txt $T/w10.txt --chunk 1 --io buffered
  cmpv "n11 43930534 plain" 11 $T/w11.txt $T/w11.txt
  cmpv "n11 43930534 xz" 11 "$PUB/words/superpermutation-11-43930534.txt.xz" "$PUB/words/superpermutation-11-43930534.txt.xz"
  cmpv "n11 43930534 1MB chunks 3 readers" 11 $T/w11.txt $T/w11.txt --chunk 1 --readers 3
  have "$PF" && for f in $PF/11/*.xz; do cmpv "n11 $(basename $f)" 11 $f $f; done
  cmpv "n12 522736969 plain" 12 $T/w12.txt $T/w12.txt
  cmpv "n12 522736969 xz" 12 "$PUB/words/superpermutation-12-522736969.txt.xz" "$PUB/words/superpermutation-12-522736969.txt.xz"
  cmpv "n12 522736969 stdin 3MB chunks" 12 $T/w12.txt - --chunk 3 < $T/w12.txt
  have "$BEST12" && cmpv "n12 cutlns 522736434" 12 $BEST12 $BEST12
  # corrupted words
  for spec in "10 w10 4034855" "11 w11 43930534" "12 w12 522736969"; do
    set -- $spec; n=$1; w=$2; L=$3
    for c in "sub $((L / 2))" "del $((L / 3))" "swap $((2 * L / 3))" "first" "last --len $L"; do
      tag=$(echo $c | cut -d' ' -f1-2 | tr ' ' '_')
      nice -n 19 $CORR $c < $T/$w.txt > $T/bad.txt 2>> $LOG
      cmpv "corrupt n$n $tag" $n $T/bad.txt $T/bad.txt --chunk 1
    done
  done
  w=$T/w10.txt
  { head -c 2000000 $w; printf 'x'; tail -c +2000001 $w; } > $T/bad.txt; cmpv "n10 foreign byte inside" 10 $T/bad.txt $T/bad.txt
  { head -c 1048576 $w; printf '\n'; tail -c +1048577 $w; } > $T/bad.txt; cmpv "n10 LF inside at a 1MB chunk end" 10 $T/bad.txt $T/bad.txt --chunk 1
  fold -w 1000 $w | sed 's/$/\r/' > $T/bad.txt; cmpv "n10 CRLF lines of 1000" 10 $T/bad.txt $T/bad.txt --chunk 1
  printf '\n\n' >> $T/bad.txt; cmpv "n10 CRLF lines + 2 LF at the end" 10 $T/bad.txt $T/bad.txt
  head -c 9 $w > $T/bad.txt; cmpv "n10 9 letters" 10 $T/bad.txt $T/bad.txt
  head -c 10 $w > $T/bad.txt; cmpv "n10 10 letters" 10 $T/bad.txt $T/bad.txt
  : > $T/bad.txt; cmpv "n10 empty" 10 $T/bad.txt $T/bad.txt
  tr '0-9' 'a-j' < $w > $T/bad.txt
  G $VF 10 abcdefghij < $T/bad.txt > val/lower.vf.json 2>> $LOG; rv=$?; waitgpu; G $B/gcheck 10 $T/bad.txt > val/lower.gc.json 2>> $LOG; rg=$?
  rec "gcheck n10 lowercase letters (auto alphabet)" $([ "$(strip_g val/lower.gc.json)" = "$(cat val/lower.vf.json)" ] && [ $rv = $rg ] && echo 1 || echo 0) "exit $rv $rg $(grep -o '"alphabet":"[^"]*"' val/lower.gc.json)"
  rm -f $T/bad.txt
fi
if [ $WHAT = gcheck13 ] || [ $WHAT = all ]; then
  unxz_to "$PUB/words/superpermutation-13-6747802319.txt.xz" $T/w13.txt
  cmpv "n13 6747802319 plain" 13 $T/w13.txt $T/w13.txt
  cmpv "n13 6747802319 xz" 13 "$PUB/words/superpermutation-13-6747802319.txt.xz" "$PUB/words/superpermutation-13-6747802319.txt.xz"
  have "$BEST13" && cmpv "n13 cutlns 6747800516" 13 $BEST13 $BEST13
  have "$BEST13" && cmpv "n13 cutlns 6747800516 buffered" 13 $BEST13 $BEST13 --io buffered
  L=6747802319
  for c in "sub $((L / 2))" "del $((L / 3))" "last --len $L"; do
    tag=$(echo $c | cut -d' ' -f1-2 | tr ' ' '_')
    nice -n 19 $CORR $c < $T/w13.txt > $T/bad13.txt 2>> $LOG
    cmpv "corrupt n13 $tag" 13 $T/bad13.txt $T/bad13.txt
  done
  rm -f $T/bad13.txt
fi
if [ $WHAT = gdel ] || [ $WHAT = all ]; then
  prep
  have "$W9" && cmpd "n9 408731" $W9
  have "$PF" && cmpd "n9 pantone 408732 (final LF)" $PF/9/superpermutation-9-408732.txt
  have "$PF" && for f in $PF/10/*.txt; do cmpd "n10 $(basename $f)" $f; done
  cmpd "n10 4034855 1MB chunks" $T/w10.txt --chunk 1
  cmpd "n11 43930534" $T/w11.txt
  cmpd "n12 522736969" $T/w12.txt
  have "$BEST12" && cmpd "n12 cutlns 522736434" $BEST12
  # words with deletable letters: a letter doubled (the copy is deletable), a permutation window repeated, corrupted
  w=$T/w10.txt
  { head -c 2000000 $w; tail -c +2000000 $w; } > $T/bad10.txt; cmpd "n10 letter 1999999 doubled" $T/bad10.txt
  { head -c 2000010 $w; tail -c +2000001 $w; } > $T/bad10.txt; cmpd "n10 10 letters repeated" $T/bad10.txt --chunk 1
  { head -c 1048570 $w; head -c 30 $w; tail -c +1048571 $w; } > $T/bad10.txt; cmpd "n10 first 30 letters inserted at a chunk end" $T/bad10.txt --chunk 1
  { cat $w; tail -c 10 $w; } > $T/bad10.txt; cmpd "n10 last 10 letters repeated" $T/bad10.txt
  { head -c 10 $w; cat $w; } > $T/bad10.txt; cmpd "n10 first 10 letters repeated" $T/bad10.txt
  { cat $w; cat $w; } > $T/bad10.txt; cmpd "n10 word twice" $T/bad10.txt --chunk 1
  for c in "sub 2017427" "del 1344951" "swap 2689903" "first" "last --len 4034855"; do
    tag=$(echo $c | cut -d' ' -f1-2 | tr ' ' '_'); nice -n 19 $CORR $c < $w > $T/bad10.txt 2>> $LOG; cmpd "corrupt n10 $tag" $T/bad10.txt
  done
  w=$T/w12.txt
  { head -c 300000000 $w; tail -c +299999990 $w; } > $T/bad12.txt; cmpd "n12 11 letters repeated" $T/bad12.txt
  nice -n 19 $CORR del 100000000 < $w > $T/bad12.txt 2>> $LOG; cmpd "corrupt n12 del" $T/bad12.txt
  rm -f $T/bad10.txt $T/bad12.txt
fi
if [ $WHAT = gdel13 ] || [ $WHAT = all ]; then
  unxz_to "$PUB/words/superpermutation-13-6747802319.txt.xz" $T/w13.txt
  cmpd "n13 6747802319" $T/w13.txt
  have "$BEST13" && cmpd "n13 cutlns 6747800516" $BEST13
  { head -c 4000000000 $T/w13.txt; tail -c +3999999990 $T/w13.txt; } > $T/bad13.txt; cmpd "n13 11 letters repeated" $T/bad13.txt
  rm -f $T/bad13.txt
fi
echo "$(date '+%F %T') END validate $WHAT: $runs runs, $fail failed" | tee -a $LOG
