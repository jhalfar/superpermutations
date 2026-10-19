#!/bin/bash
# decode.sh PLAN.uplan.xz [OUT|-|check]
#   builds gen14 (and vfast for "check") from the sources next to this file, checks the selection's SHA-256,
#   and writes the word to OUT (or stdout with "-"), or streams it into vfast with "check".
#   gen14 prints the length and SHA-256 of what it wrote and compares them with the plan's "# expect" line.
set -e
D=$(cd "$(dirname "$0")" && pwd)
PLAN=$1; OUT=${2:-check}
SEL_SHA=4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a
T=$(mktemp -d)
SELXZ="$D/../../arrange/data/n12t-selection.txt.xz"   # the selection of the repository
[ -f "$SELXZ" ] || SELXZ="$D/n12t-selection.txt.xz"
xz -dc "$SELXZ" > "$T/sel.txt"
echo "$SEL_SHA  $T/sel.txt" | sha256sum -c - >&2
xz -dc "$PLAN" > "$T/plan.uplan"
gcc -O3 -o "$T/gen14" "$D/gen14.c"
if [ "$OUT" = check ]; then
  gcc -O3 -o "$T/vfast" "$D/vfast.c" -lpthread
  "$T/gen14" plan "$T/sel.txt" "$T/plan.uplan" | "$T/vfast" 14 0123456789ABCD 1
elif [ "$OUT" = - ]; then
  "$T/gen14" plan "$T/sel.txt" "$T/plan.uplan"
else
  "$T/gen14" plan "$T/sel.txt" "$T/plan.uplan" > "$OUT"
fi
rm -rf "$T"
