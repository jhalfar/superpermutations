#!/bin/bash
# The certificate 14 843 63334 16000 of Theorem C: a superpermutation on 14 symbols has at least 93,891,141,126
# letters, checked by the Lean kernel.  The Lean files are generated here, not stored: about 12 GB of source.
#
#     ./build.sh [generate | build | final | all]          default: all
#
# Run ../../build.sh first (the default level is enough): this script works in the same build directory and
# needs the compiled modules of LowerBounds/ that it leaves there.
#
#   generate  ../../tools/s_plan2.py runs the search of the certificate (1,342,488 states) and writes it as Lean
#             files cut into lemmas of at most 400 states (5,347 files: 4,479 data files D...., the file Defs,
#             866 parts P..., one head file); fix_imports.py then makes every part import only the data files
#             it uses instead of Defs.  The files must agree with generated.sha256.
#   build     Lean compiles the data files, the parts and the head file, JOBS processes at a time.  These
#             modules need no Mathlib.  The kernel evaluates every lemma of every part.
#   final     make_final.py writes Final_C14_843_63334_16000.lean, which must be identical to the file here;
#             Lean compiles it (it imports Mathlib through ../../LowerBounds) and the script checks that both
#             statements depend on propext, Classical.choice and Quot.sound only.
#
# Settings: those of ../../../tools/common.sh (LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES, JOBS, LEAN_THREADS,
# MINFREE_GB), and
#   BUILD_DIR   the build directory of ../../build.sh: ../../../build/words
#
# Cost when I ran it (README.md): generation 984 s on one thread and 25.1 GB of memory; the parts 61 hours of
# Lean time in all (one thread per process, at most 6.8 GB committed by one process); the head file 11.4 GB
# and the final step 17.9 GB, each alone; about 12 GB of generated source and 11 GB of compiled files.

HERE="$(cd "$(dirname "$0")" && pwd)"
LOWER="$(cd "$HERE/../.." && pwd)"
. "$LOWER/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
K=14 CN=843 BN=63334 Q=16000
NAME="C${K}_${CN}_${BN}_${Q}"
W="$BUILD/$NAME"
SG="$W/sgen"
PHASE="${1:-all}"
case "$PHASE" in generate | build | final | all) ;; *) die "usage: build.sh [generate | build | final | all]" ;; esac
export PYTHONDONTWRITEBYTECODE=1
STANDARD=': \[propext, Classical\.choice, Quot\.sound\]$'

generate() {
  if [ -f "$SG/done.txt" ]; then
    echo "generated before: $(cat "$SG/done.txt")"
  else
    rm -rf "$SG"
    mkdir -p "$SG/LowerBounds"
    cp "$LOWER"/tools/s_*.py "$SG/"
    local t0
    t0=$(date +%s)
    (cd "$SG" && nice -n 19 "$PYTHON" s_plan2.py "$K" "$CN" "$BN" "$Q" "$NAME" --leaf 400 --band 250 --per-file 3000) \
      < /dev/null > "$W/s_plan2.log" 2>&1 || die "s_plan2.py failed, see $W/s_plan2.log"
    "$PYTHON" "$HERE/fix_imports.py" "$SG" "$NAME" < /dev/null >> "$W/s_plan2.log" 2>&1 \
      || die "fix_imports.py failed, see $W/s_plan2.log"
    echo "$(date '+%F %T'), $(( $(date +%s) - t0 )) s, $(ls "$SG/LowerBounds/SGen" | wc -l | tr -d ' ') files" \
      > "$SG/done.txt"
  fi
  [ "$(ls "$SG/LowerBounds/SGen" | wc -l | tr -d ' ')" = "$(wc -l < "$HERE/generated.sha256" | tr -d ' ')" ] \
    || die "the number of generated files differs from generated.sha256"
  check_hashes "$HERE/generated.sha256" "$SG/LowerBounds/SGen"
  echo "the $(wc -l < "$HERE/generated.sha256" | tr -d ' ') generated files agree with generated.sha256"
}

build() {
  [ -f "$SG/done.txt" ] || die "run the phase generate first"
  [ -f "$BUILD/lib/LowerBounds/SRun.olean" ] || die "no compiled LowerBounds/SRun in $BUILD/lib: run ../../build.sh first"
  build_modules "LowerBounds.SGen.$NAME" -- "$SG" "$LOWER"
}

final() {
  "$PYTHON" "$HERE/make_final.py" "$K" "$CN" "$BN" "$Q" "$SG/LowerBounds/SGen/$NAME.lean" "$W/Final_$NAME.lean" \
    < /dev/null || die "make_final.py failed"
  cmp -s "$W/Final_$NAME.lean" "$HERE/Final_$NAME.lean" || die "make_final.py wrote a file that differs from Final_$NAME.lean"
  JOBS=1 build_modules "Final_$NAME" -- "$HERE" "$SG" "$LOWER" "$ROOT/words" "$PANTONE_DIR" \
    "${HUNTER_DIR:-$ROOT/deps/superpermutations-hunter}" \
    "${PREIMAGE_DIR:-$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
  local ax
  ax="$(print_axioms "Final_$NAME" | grep "depends on axioms")"
  echo "$ax"
  [ "$(echo "$ax" | grep -c .)" = 2 ] && [ "$(echo "$ax" | grep -c -E "$STANDARD")" = 2 ] \
    || die "expected two #print axioms lines with propext, Classical.choice, Quot.sound only"
  echo "proven: covers_length_ge_93891141126 and ssuper_ge_93891141126"
}

check_tools
mkdir -p "$W" "$BUILD/logs"
case "$PHASE" in
  generate) generate ;;
  build) build ;;
  final) final ;;
  all) generate; build; final ;;
esac
echo "== done ($PHASE): $(date '+%F %T')"
