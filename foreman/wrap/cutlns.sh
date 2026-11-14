#!/bin/bash
# cutlns.sh OUT PLAN BASE N SEC THR [cutlns2.py options...]: the cut-opening reorder (tools/reorder) as an arm.
#   1. render PLAN on BASE to a word (trailsearch --time 0); 2. tools/reorder/steps (steps of weight >= 3);
#   3. tools/reorder/cutlns2.py for SEC seconds (DIR/STOP stops it); 4. back to a plan on BASE: n = 13 w2p13o +
#   unitsplit.py (tools/pipeline, BASE.tsv beside BASE), else word2plan (exact and safe).  If no plan can be made the
#   word is still written and "terminal" is printed (foreman keeps and reports the word, the plan is not reused).
# Prints "wrote OUT length L".  Needs Python with numpy, scipy and gurobipy (a Gurobi licence for models this size).
. "$(dirname "$0")/paths.sh"; OUT=$1; PLAN=$2; B=$3; N=$4; SEC=$5; THR=$6; shift 6
D=$(dirname "$OUT"); BT=${B%.txt}.tsv
OMP_NUM_THREADS=4 "$(exe trailsearch)" "$B" "$D/in.txt" --plan-in "$PLAN" --time 0 --threads 4 --mincut 1 > "$D/render.log" 2>&1
L0=$(grep -o "wrote .* length [0-9]*" "$D/render.log" | tail -1 | grep -o "[0-9]*$")
[ -n "$L0" ] && [ -f "$D/in.txt" ] || { echo "render failed"; tail -n 3 "$D/render.log"; exit 1; }
echo "cutlns: n $N start $L0, $SEC s, $THR threads, options $*"
"$(exe "$RO" steps)" "$D/in.txt" "$N" 3 "$D/steps.bin" > "$D/steps.log" 2>&1 || { echo "steps failed"; exit 1; }
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
"$PYX" -I "$RO/cutlns2.py" "$D/in.txt" "$N" "$D/steps.bin" "$D/c" --time "$SEC" --threads "$THR" --write 1 \
  --stop "$D/STOP" "$@" > "$D/cutlns.log" 2>&1
grep -E "^round|gain|wrote|END" "$D/c/run.log" 2>/dev/null | tail -n 5
rm -f "$D/steps.bin"
if [ ! -f "$D/c/w.txt" ]; then rm -f "$D/in.txt"; echo "no word written (no gain or stopped before the end)"; echo "wrote $OUT length $L0"; cp "$PLAN" "$OUT.plan"; : > "$OUT"; exit 0; fi
L=$(stat -c %s "$D/c/w.txt"); [ "$(tail -c 1 "$D/c/w.txt" | od -An -c | tr -d ' ')" = '\n' ] && L=$((L - 1))
rm -f "$D/in.txt"
if [ "$L" -ge "$L0" ]; then rm -f "$D/c/w.txt"; echo "cutlns: no gain ($L >= $L0)"; echo "wrote $OUT length $L0"; cp "$PLAN" "$OUT.plan"; : > "$OUT"; exit 0; fi
mv "$D/c/w.txt" "$OUT"
if [ "$N" = "13" ]; then
  OMP_NUM_THREADS=6 "$(exe "$PL" w2p13o)" "$B" "$OUT" "$OUT.w2p" > "$OUT.w2p.log" 2>&1
  "$PYX" -I "$PL/unitsplit.py" "$B" "$BT" "$OUT.w2p" "$OUT.plan" >> "$OUT.w2p.log" 2>&1
  rm -f "$OUT.w2p"
else
  "$(exe word2plan)" "$B" "$OUT" "$OUT.plan" > "$OUT.w2p.log" 2>&1
  if ! grep -q "RESULT: exact" "$OUT.w2p.log" || grep -q "NOT safe to search from" "$OUT.w2p.log"; then rm -f "$OUT.plan"; fi
fi
[ -f "$OUT.plan" ] || echo "terminal"
echo "wrote $OUT length $L"
