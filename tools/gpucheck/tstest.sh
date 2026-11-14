#!/bin/bash
# tstest.sh [small|n13] - trailsearch_gl --gpuload against trailsearch_fast: same arguments, the plan and the word they
# write must have the same SHA-256, and the printed lines must agree apart from times; wall times of both.  3 threads
# (OMP_NUM_THREADS=3, --threads 1 or 3), nice 19; the card must be free (gpubusy.sh) before each card run.  Lines in
# WORK/val/tstest.tsv; compare with val/tstest.tsv next to this script (my run).
# Environment: WORK = work directory (required); TOOLS = directory of trailsearch_gl and tsgl.ptx (default: the
# directory of this script); TS_FAST = the program without the card (default: trailsearch_gl, which without --gpuload
# is trailsearch_fast; my run used a separate build of trailsearch_fast); GUARD = a command put in front of every run
# (default none; I used a 16 GB guard); PYTHON (default python3, for geng.py).
# small: n = 10 from the selection and plan in reproduce/ (geng.py writes the base word), and the published words of
#        n = 10, 11, 12 as their own base; EXTRA12 = a word of 522,736,434 letters (optional, the n12c run).
# n13:   BASE13 + PLAN13 = a hybrid base word and a plan on it (optional), EXTRA13 = a word read as its own base
#        (optional).
H=$(cd "$(dirname "${BASH_SOURCE:-$0}")" && pwd); B=${TOOLS:-$H}; R=$(cd "$H/../.." && pwd)
WHAT=${1:-small}
PY=${PYTHON:-$(command -v python3 || command -v python)}
T=${WORK:?set WORK}; O=$T/ts; mkdir -p $O $T/val || exit 1
A=${TS_FAST:-$B/trailsearch_gl}; BB=$B/trailsearch_gl
RES=$T/val/tstest.tsv; LOG=$T/val/tstest.log
export OMP_NUM_THREADS=3
waitgpu() { while ! bash $H/gpubusy.sh > /dev/null; do echo "card busy, waiting 60 s" >> $LOG; sleep 60; done; }
have() { [ -n "$1" ] && [ -e "$1" ]; }
unxz_to() { [ -s "$2" ] || nice -n 19 xz -T1 -dc "$1" | tr -d '\r\n' > "$2"; }
fail=0; runs=0
# tst TAG BASE PLAN(-) ARGS... : A, then B --gpuload
tst() {
  local tag=$1 base=$2 plan=$3; shift 3
  local pa=""; [ "$plan" != "-" ] && pa="--plan-in $plan"
  local s=$(date +%s.%N)
  nice -n 19 ${GUARD-} $A "$base" $O/${tag}_a.txt $pa "$@" > $O/${tag}_a.log 2>&1; local ra=$?
  local m=$(date +%s.%N)
  waitgpu
  local m2=$(date +%s.%N)
  nice -n 19 ${GUARD-} $BB "$base" $O/${tag}_b.txt $pa --gpuload "$@" > $O/${tag}_b.log 2>&1; local rb=$?
  local e=$(date +%s.%N)
  local ha=$(sha256sum < $O/${tag}_a.txt.plan 2>/dev/null | cut -c1-16) hb=$(sha256sum < $O/${tag}_b.txt.plan 2>/dev/null | cut -c1-16)
  local wa=$(sha256sum < $O/${tag}_a.txt 2>/dev/null | cut -c1-16) wb=$(sha256sum < $O/${tag}_b.txt 2>/dev/null | cut -c1-16)
  # the printed lines must agree too, apart from times
  local la=$(grep -v "^\[guard\]\|^\[prof\]\|^TSGL_DEBUG" $O/${tag}_a.log | sed 's/([0-9.]*s)//g; s/ [0-9.]*s$//; s/_[ab]\.txt/_X.txt/g' | sha256sum | cut -c1-12)
  local lb=$(grep -v "^\[guard\]\|^\[prof\]\|^TSGL_DEBUG" $O/${tag}_b.log | sed 's/([0-9.]*s)//g; s/ [0-9.]*s$//; s/_[ab]\.txt/_X.txt/g' | sha256sum | cut -c1-12)
  grep "^TSGL_DEBUG" $O/${tag}_b.log >> $LOG
  local ok=1; [ -n "$ha" ] && [ "$ha" = "$hb" ] && [ "$wa" = "$wb" ] && [ $ra = $rb ] && [ "$la" = "$lb" ] || ok=0
  runs=$((runs + 1)); [ $ok = 1 ] || fail=$((fail + 1))
  local line="$tag	$([ $ok = 1 ] && echo SAME || echo DIFFER)	plan $ha/$hb word $wa/$wb log $la/$lb exit $ra/$rb	fast $(awk "BEGIN{printf \"%.1f\", $m - $s}") s	gl $(awk "BEGIN{printf \"%.1f\", $e - $m2}") s	$(grep -o 'peak committed memory of the job [0-9.]* GB' $O/${tag}_b.log)"
  echo "$line" >> $RES; echo "$line"
}
echo "tstest $WHAT start $(date '+%F %T') trailsearch_gl.c $(sha256sum $H/trailsearch_gl.c | cut -c1-16) tsgl.cu $(sha256sum $H/tsgl.cu | cut -c1-16)" >> $LOG
if [ $WHAT = small ]; then
  [ -s $T/base10.txt ] || nice -n 19 "$PY" "$R/reproduce/tools/geng.py" "$R/reproduce/selections/n10-selection.txt" $T/base10.txt > $T/geng10.log 2>&1
  P10=$R/reproduce/plan/n10-4034855.plan
  unxz_to "$R/words/superpermutation-10-4034855.txt.xz" $T/w10.txt
  unxz_to "$R/words/superpermutation-11-43930534.txt.xz" $T/w11.txt
  unxz_to "$R/words/superpermutation-12-522736969.txt.xz" $T/w12.txt
  tst n10p_t0 $T/base10.txt $P10 --time 0 --prof
  tst n10b_t0 $T/base10.txt - --time 0
  tst n10p_it $T/base10.txt $P10 --threads 1 --iters 3000 --time 1e9 --seed 7 --kmax 8 --T0 0.4
  tst n10w_t0 $T/w10.txt - --time 0
  tst n11w_t0 $T/w11.txt - --time 0
  tst n11w_it $T/w11.txt $O/n11w_t0_a.txt.plan --threads 1 --iters 1500 --time 1e9 --seed 3 --kmax 10 --T0 0.6
  tst n12w_t0 $T/w12.txt - --time 0 --prof
  tst n12w_it $T/w12.txt $O/n12w_t0_a.txt.plan --threads 1 --iters 500 --time 1e9 --seed 11 --kmax 8 --T0 0.4
  have "${EXTRA12:-}" && tst n12c_t0 $EXTRA12 - --time 0
fi
if [ $WHAT = n13 ]; then
  have "${BASE13:-}" && have "${PLAN13:-}" && tst n13p_t0 $BASE13 $PLAN13 --time 0 --prof --threads 3
  have "${EXTRA13:-}" && tst n13w_t0 $EXTRA13 - --time 0 --prof --threads 3
fi
echo "$(date '+%F %T') END tstest $WHAT: $runs runs, $fail differ" | tee -a $LOG
