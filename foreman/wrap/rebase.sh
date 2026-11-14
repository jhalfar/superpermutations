#!/bin/bash
# rebase.sh OUT PLAN BASE ALTBASE [ALTBASE...]: move a plan onto another base.  A word read as its own base can hide
# closed trails that the search cannot move.  Render PLAN on BASE, then convert the word with word2plan onto each
# ALTBASE in turn (a selection's base or a hybrid base); if the word does not fit as it is, its symmetric image
# (relabelled and/or reversed: tools/prepub/relabel.py) is tried.  The first exact and safe plan wins; the word
# written as OUT is then the image (same length, same coverage).
# Writes OUT and OUT.plan, prints "newbase ALTBASE" and "wrote OUT length L".
. "$(dirname "$0")/paths.sh"; OUT=$1; PLAN=$2; B=$3; shift 3; D=$(dirname "$OUT")
OMP_NUM_THREADS=4 "$(exe trailsearch)" "$B" "$OUT" --plan-in "$PLAN" --time 0 --threads 4 --mincut 1 > "$D/render.log" 2>&1
L=$(grep -o "wrote .* length [0-9]*" "$D/render.log" | tail -1 | grep -o "[0-9]*$")
[ -n "$L" ] && [ -f "$OUT" ] || { echo "render failed"; tail -3 "$D/render.log"; exit 1; }
grep -E "^trails" "$D/render.log"
ok() { grep -q "RESULT: exact" "$1" && ! grep -q "NOT safe to search from" "$1"; }
for A in "$@"; do
  [ "$A" = "$B" ] && continue
  "$(exe word2plan)" "$A" "$OUT" "$OUT.plan" > "$D/w2p.log" 2>&1
  if ok "$D/w2p.log"; then
    echo "word2plan on $A: exact, safe ($(grep -o '^plan: [0-9]* events' "$D/w2p.log"))"
    echo "newbase $A"; echo "wrote $OUT length $L"; exit 0
  fi
  if "$PYX" -I "$PP/relabel.py" "$A" "$OUT" "$D/img.txt" > "$D/relabel.log" 2>&1; then
    "$(exe word2plan)" "$A" "$D/img.txt" "$OUT.plan" > "$D/w2p.log" 2>&1
    if ok "$D/w2p.log"; then
      echo "word2plan on $A: the image ($(grep -o 'MAP [0-9A-F]*\|REV [01]' "$D/relabel.log" | tr '\n' ' ')) is exact, safe"
      mv "$D/img.txt" "$OUT"
      echo "newbase $A"; echo "wrote $OUT length $L"; exit 0
    fi
  fi
  rm -f "$D/img.txt"
  echo "word2plan on $A: not exact or not safe (also its image)"
done
rm -f "$OUT.plan"
echo "no alternative base fits"
exit 1
