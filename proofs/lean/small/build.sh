#!/bin/bash
# Build the exact values S(1), ..., S(6) = 1, 3, 9, 33, 153, 872, from sources, into an empty build directory.
#
#     ./build.sh         everything: Small/Exact.lean (n = 1 to 6) and AuditSmall.lean
#     ./build.sh 5       n = 1 to 5 only: Small/Upto5.lean (no search at n = 6)
#
# What happens, in this order:
#   1. The tools are checked.  The files that the theorems are compiled from (those of this directory, and the
#      reused Lean files of ../n7, ../lower and ../words) are compared with sources.sha256, and the sources of
#      the two libraries and Challenge.lean with their lists (../words/hunter-sources.sha256,
#      ../words/preimage-sources.sha256, ../constant/pantone-sources.sha256).
#   2. gen_k6.py, gen_cap.py, gen_tight.py and gen_teval.py write the tables and the 72 parts of the search at
#      n = 6 into the build directory; each of the 76 files must be identical to the one in K6/.  check_witness.py
#      checks that the word written out in superperm6/Superperm6/Witness.lean is the word of the data file.
#   3. Lean compiles, in dependency order, every module that the targets import: the Hunter-Raudvere library,
#      Liu's library, Challenge.lean, the reused files of ../words, ../lower and ../n7, Grayzel's two files in
#      superperm6/, and the files of K6/ and Small/.  The part K6/TE/T2P2Q6.lean (33 GB) is compiled alone.
#      Nothing compiled outside the build directory is read, except Mathlib.
#   4. The "#print axioms" lines are printed.  The script fails if any line in the build directory names an
#      axiom other than propext, Classical.choice and Quot.sound.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR         the build directory: ../build/small
#   JOBS              Lean processes at the same time (the part T2P2Q6 always runs alone): 1
#   HUNTER_DIR        a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR      a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                     ../deps/superpermutations-preimage-chain-lower-bounds
#   LEAN_PREFIX       words put in front of every Lean command, split at spaces (for example a program that
#                     limits the memory of the process): empty
#   LEAN_PREFIX_BIG   the same for the part T2P2Q6: $LEAN_PREFIX
#   CHECK_SOURCES     1: stop if a source differs from the lists of hashes of step 1: 1
#
# Memory (committed): most modules import Mathlib and need about 8 GB; LowerBounds.PArith of ../n7 11 GB; the
# parts K6/TE/*.lean up to 23 GB, and T2P2Q6 33 GB.  README.md has the measured times.  To stop: Ctrl-C, or create
# the file STOP in the build directory; the same command continues where the build stopped.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/small}"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${LEAN_PREFIX:=}"
: "${LEAN_PREFIX_BIG:=$LEAN_PREFIX}"
: "${CHECK_SOURCES:=1}"
TARGET="${1:-all}"
case "$TARGET" in all | 5) ;; *) die "usage: build.sh [5]" ;; esac
export PYTHONDONTWRITEBYTECODE=1
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
ROOTS=("$HERE" "$HERE/superperm6" "$ROOT/n7" "$ROOT/lower" "$ROOT/words" "$PANTONE_DIR" "$HUNTER_DIR"
       "$PREIMAGE_DIR")

# compile_one as in ../tools/common.sh, with two additions: $LEAN_PREFIX in front of Lean, and no limit on the
# heartbeats of the elaborator for the files of K6/ (their proofs were developed with -DmaxHeartbeats=0).
compile_one() {
  local mod="$1" root="$2" src="$3" stamp="$4"
  local out="$BUILD/lib/${mod//.//}" log="$BUILD/logs/$mod.log" t0 secs opts=()
  case "$mod" in K6.*) opts=(-DmaxHeartbeats=0) ;; esac
  mkdir -p "$(dirname "$out")"
  rm -f "$out.stamp"
  t0=$(date +%s)
  # shellcheck disable=SC2086
  if (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS="$LEAN_THREADS" nice -n 19 $LEAN_PREFIX "$LEAN" \
        -j "$LEAN_THREADS" "${opts[@]}" "--root=$(native "$root")" -o "$(native "$out.olean")" \
        -i "$(native "$out.ilean")" "$(native "$src")") < /dev/null > "$log" 2>&1; then
    secs=$(( $(date +%s) - t0 ))
    echo "$stamp" > "$out.stamp"
    echo "$(date '+%F %T') ok $secs s $mod" >> "$BUILD/build.log"
    echo "  compiled $mod ($secs s)"
  else
    secs=$(( $(date +%s) - t0 ))
    rm -f "$out.olean" "$out.ilean"
    echo "$(date '+%F %T') FAILED $secs s $mod" >> "$BUILD/build.log"
    echo "  FAILED $mod, see $log"
    echo "$mod" >> "$FAILED_FILE"
  fi
}

echo "== 1. tools and sources ($TARGET)"
check_tools
[ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
[ -f "$PREIMAGE_DIR/PreimageChain/PathwiseFinalCore.lean" ] \
  || die "no PreimageChain/PathwiseFinalCore.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
mkdir -p "$BUILD/logs" "$BUILD/gen"
if [ "$CHECK_SOURCES" = 1 ]; then
  check_hashes "$HERE/sources.sha256" "$ROOT"
  check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
  check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  grep "  Challenge.lean$" "$ROOT/constant/pantone-sources.sha256" > "$BUILD/hashes_challenge.txt"
  check_hashes "$BUILD/hashes_challenge.txt" "$PANTONE_DIR"
  echo "the files of this proof, the sources of both libraries and Challenge.lean agree with the lists of hashes"
fi

echo "== 2. generated files and the witness"
rm -rf "$BUILD/gen/K6"
for g in gen_k6 gen_cap gen_tight gen_teval; do
  "$PYTHON" "$HERE/$g.py" "$BUILD/gen" < /dev/null > "$BUILD/gen/$g.log" 2>&1 || die "$g.py failed, see $BUILD/gen/$g.log"
done
n=0
for f in $(cd "$BUILD/gen" && find K6 -name '*.lean' | sort); do
  cmp -s "$BUILD/gen/$f" "$HERE/$f" || die "the generators wrote a $f that differs from the one in this directory"
  n=$((n + 1))
done
[ "$n" = 76 ] || die "the generators wrote $n Lean files, not 76"
echo "the generators wrote $n files, identical to those in K6/"
"$PYTHON" "$HERE/check_witness.py" "$HERE/superperm6/data/superperm6_872_clean.txt" \
  "$HERE/superperm6/Superperm6/Witness.lean" < /dev/null || die "check_witness.py failed"

echo "== 3. Lean"
if [ "$TARGET" = 5 ]; then
  FINAL="Small.Words Small.Upto5"
  build_modules Small.Upto5 -- "${ROOTS[@]}"
else
  FINAL="Small.Words Small.Upto5 K6.Final871 K6.Final872 K6.A6 Small.Exact AuditSmall"
  build_modules Small.Upto5 K6.TightRules K6.Final871 Superperm6.Witness -- "${ROOTS[@]}"
  JOBS=1 LEAN_PREFIX="$LEAN_PREFIX_BIG" build_modules K6.TE.T2P2Q6 -- "${ROOTS[@]}"
  build_modules Small.Exact AuditSmall -- "${ROOTS[@]}"
fi

echo "== 4. axioms"
# shellcheck disable=SC2086
print_axioms $FINAL
OTHER="$(axiom_lines "$BUILD"/logs/*.log | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
echo "== all \"#print axioms\" lines of the build, counted by the list of axioms"
axiom_summary
echo "$(grep -c " ok " "$BUILD/build.log") modules compiled in this build directory so far," \
  "$(awk '$3 == "ok" { s += $4 } END { print s }' "$BUILD/build.log") s of Lean time"
echo "== done ($TARGET): $(date '+%F %T')"
