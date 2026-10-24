#!/bin/bash
# Builds the DLL for the compiled evaluations of the 5,901 engines (agent pub5901). Writes only below this
# directory: build/J16Search.c (C of LowerBounds/J16Search.lean of the level-1 sources, no .olean written there),
# build/lib/Audit5901/J16Count.olean, build/J16Count.c, build/A16C.dll.
HERE="$(cd "$(dirname "$0")" && pwd)"; cd "$HERE" || exit 1
LL="${LEVEL1:?set LEVEL1 to a directory with the sources and the build of the level-1 modules}"
TC="${LEAN_TOOLCHAIN:?set LEAN_TOOLCHAIN to the Lean 4.31.0 toolchain}"
w() { cygpath -w "$1"; }
set -e
mkdir -p build/lib/Audit5901
export LEAN_PATH="$(w "$TC/lib/lean");$(w "$LL/build/lib");$(w "$HERE/build/lib")"
export LEAN_NUM_THREADS=1
nice -n 19 "$TC/bin/lean.exe" --root="$(w "$LL")" -c "$(w "$HERE/build/J16Search.c")" "$(w "$LL/LowerBounds/J16Search.lean")"
nice -n 19 "$TC/bin/lean.exe" --root="$(w "$HERE")" -o "$(w "$HERE/build/lib/Audit5901/J16Count.olean")" \
  -i "$(w "$HERE/build/lib/Audit5901/J16Count.ilean")" -c "$(w "$HERE/build/J16Count.c")" "$(w "$HERE/Audit5901/J16Count.lean")"
nice -n 19 "$TC/bin/leanc.exe" -shared -O3 -o "$(w "$HERE/build/A16C.dll")" "$(w "$HERE/build/J16Count.c")" \
  "$(w "$HERE/build/J16Search.c")" "$(w "$LL/build/native/J15Search.c")" "$(w "$LL/build/native/KSearch.c")" \
  "$(w "$LL/build/native/PSearch.c")" "$(w "$LL/build/native/PCount.c")"
sha256sum "$LL/LowerBounds/J16Search.lean" Audit5901/J16Count.lean build/J16Search.c build/J16Count.c build/A16C.dll | tee build/SHA256.txt
echo "build done $(date '+%F %T')"
