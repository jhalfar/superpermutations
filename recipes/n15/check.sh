#!/bin/bash
# check.sh [check|count] [THREADS]
#   builds gen16 and gen16c from the sources next to this file, checks the SHA-256 of the selection and of the
#   unpacked plan, and then
#   check (default): generates the word from the plan block by block and checks it with the group check
#                    (gen16c, THREADS check workers, default 2; 1 generator thread and 1 SHA thread besides);
#   count:           only spells the word and prints its length and SHA-256 (gen16, one thread).
#   The word is never stored. Both modes compare the length and SHA-256 with the expected values.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
MODE=${1:-check}; T=${2:-2}
PLAN=n15_1401325411491_on_selC.uplan.xz
EXP_LEN=1401325411491
EXP_SHA=d91b875a151480dbac864005bf7bdcd1d9aaeab2d5f5a0bffabfdb1e18cbe21c
SEL_SHA=4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a
PLAN_SHA=8a9ed8988f18f42885dd72a026c93ddd9a36aa863b9b51c081ee60afa0b371d0
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
SELXZ="$D/../../arrange/data/n12t-selection.txt.xz"   # the selection of the repository
[ -f "$SELXZ" ] || SELXZ="$D/n12t-selection.txt.xz"
xz -dc "$SELXZ" > "$W/sel.txt"
echo "$SEL_SHA  $W/sel.txt" | sha256sum -c - >&2
xz -dc "$D/$PLAN" > "$W/plan.uplan"
echo "$PLAN_SHA  $W/plan.uplan" | sha256sum -c - >&2
if [ "$MODE" = count ]; then
  gcc -O3 -march=native -o "$W/gen16" "$D/gen16.c"
  "$W/gen16" plan 3 "$W/sel.txt" "$W/plan.uplan" --count 2> "$W/out.json" || { cat "$W/out.json"; exit 1; }
else
  gcc -O3 -march=native -pthread -o "$W/gen16c" "$D/gen16c.c"
  "$W/gen16c" plan 3 "$W/sel.txt" "$W/plan.uplan" --check "$T" > "$W/out.json" || { cat "$W/out.json"; echo "gen16c failed"; exit 1; }
fi
cat "$W/out.json"
grep -q "\"length\":$EXP_LEN," "$W/out.json" && grep -q "\"sha256\":\"$EXP_SHA\"" "$W/out.json" || { echo "MISMATCH"; exit 1; }
if [ "$MODE" = count ]; then echo "OK: n = 15 word of $EXP_LEN letters, SHA-256 as expected (no permutation check in this mode)"
else grep -q '"missing_permutations":0' "$W/out.json" && grep -q '"valid":true' "$W/out.json" \
  && echo "OK: n = 15 word of $EXP_LEN letters, every permutation present" || { echo "MISMATCH"; exit 1; }; fi
