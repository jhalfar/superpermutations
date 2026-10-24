#!/bin/bash
# ./nat.sh NAME DLL [J]   compiles Audit5901/NAME.lean (native_decide with DLL loaded) to build/lib/Audit5901/NAME.olean;
# log logs/NAME.log.  Idle priority, 16 GB guard.  On failure the .olean is removed.
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE" || exit 1
LL="${LEVEL1:?set LEVEL1 to a directory with the sources and the build of the level-1 modules}"
TC="${LEAN_TOOLCHAIN:?set LEAN_TOOLCHAIN to the Lean 4.31.0 toolchain}"
w() { cygpath -w "$1"; }
NAME="$1"; DLL="$2"; J="${3:-1}"; LOG="logs/$NAME.log"
mkdir -p logs build/lib/Audit5901
DL=(); [ -n "$DLL" ] && [ "$DLL" != - ] && DL=(--load-dynlib="$(w "$DLL")")
echo "nat: $NAME started $(date '+%F %T'), $J threads, dll $DLL $( [ ${#DL[@]} -gt 0 ] && sha256sum "$DLL" | cut -c1-16)" > "$LOG"
t0=$(date +%s)
LEAN_PATH="$(w "$TC/lib/lean");$(w "$LL/build/lib");$(w "$HERE/build/lib")" LEAN_NUM_THREADS=$J \
  "$TC/bin/lean.exe" -j "$J" "${DL[@]}" --root="$(w "$HERE")" \
  -o "$(w "$HERE/build/lib/Audit5901/$NAME.olean")" -i "$(w "$HERE/build/lib/Audit5901/$NAME.ilean")" \
  "$(w "$HERE/Audit5901/$NAME.lean")" < /dev/null >> "$LOG" 2>&1
rc=$?
[ $rc -ne 0 ] && rm -f "build/lib/Audit5901/$NAME.olean" "build/lib/Audit5901/$NAME.ilean"
echo "nat: exit=$rc wall=$(( $(date +%s) - t0 ))s, ended $(date '+%F %T')" >> "$LOG"
exit $rc
