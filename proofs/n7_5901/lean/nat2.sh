#!/bin/bash
# ./nat2.sh NAME [J]   as nat.sh without a DLL, with Mathlib and the Lean libraries on the path (as
# the run script of the level-1 sources); for modules that import level-1 files such as K16Final, J16Bridge.  Log logs/NAME.log.
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE" || exit 1
LL="${LEVEL1:?set LEVEL1 to a directory with the sources and the build of the level-1 modules}"
TC="${LEAN_TOOLCHAIN:?set LEAN_TOOLCHAIN to the Lean 4.31.0 toolchain}"
w() { cygpath -w "$1"; }
NAME="$1"; J="${2:-1}"; LOG="logs/$NAME.log"
PK="$LL/../../lean/pantone/.lake/packages"; LP=""
for p in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do LP="$LP$(w "$PK/$p/.lake/build/lib/lean");"; done
LP="$(w "$TC/lib/lean");$LP$(w "$LL/../../lean/pantone/.lake/build/lib/lean");$(w "$LL/../../lean/work/build/lib");$(w "$LL/build/lib");$(w "$HERE/build/lib")"
mkdir -p logs build/lib/Audit5901
echo "nat2: $NAME started $(date '+%F %T'), $J threads" > "$LOG"
t0=$(date +%s)
LEAN_PATH="$LP" LEAN_NUM_THREADS=$J \
  "$TC/bin/lean.exe" -j "$J" --root="$(w "$HERE")" \
  -o "$(w "$HERE/build/lib/Audit5901/$NAME.olean")" -i "$(w "$HERE/build/lib/Audit5901/$NAME.ilean")" \
  "$(w "$HERE/Audit5901/$NAME.lean")" < /dev/null >> "$LOG" 2>&1
rc=$?
[ $rc -ne 0 ] && rm -f "build/lib/Audit5901/$NAME.olean" "build/lib/Audit5901/$NAME.ilean"
echo "nat2: exit=$rc wall=$(( $(date +%s) - t0 ))s, ended $(date '+%F %T')" >> "$LOG"
exit $rc
