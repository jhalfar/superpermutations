#!/bin/bash
# ./ev.sh SRC DLL [J]   evaluates the #eval lines of SRC with DLL loaded (J threads, idle priority, 16 GB guard).
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE" || exit 1
LL="${LEVEL1:?set LEVEL1 to a directory with the sources and the build of the level-1 modules}"
TC="${LEAN_TOOLCHAIN:?set LEAN_TOOLCHAIN to the Lean 4.31.0 toolchain}"
w() { cygpath -w "$1"; }
SRC="$1"; DLL="$2"; J="${3:-1}"; B="$(basename "$SRC" .lean)"; LOG="logs/$B.log"
mkdir -p logs
echo "ev: $SRC started $(date '+%F %T'), $J threads, dll $DLL $(sha256sum "$DLL" | cut -c1-16)" > "$LOG"
t0=$(date +%s)
LEAN_PATH="$(w "$TC/lib/lean");$(w "$LL/build/lib");$(w "$HERE/build/lib")" LEAN_NUM_THREADS=$J \
  "$TC/bin/lean.exe" -j "$J" --load-dynlib="$(w "$DLL")" --root="$(w "$HERE")" "$(w "$HERE/$SRC")" < /dev/null >> "$LOG" 2>&1
rc=$?
echo "ev: exit=$rc wall=$(( $(date +%s) - t0 ))s, ended $(date '+%F %T')" >> "$LOG"
exit $rc
