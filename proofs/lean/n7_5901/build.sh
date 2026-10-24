#!/bin/bash
# Build level 1 of the Lean form of L(7) >= 5,901: the reduction of the bound to search equations.
#
#     ./build.sh
#
# This is not a proof of 5,901 in Lean. It proves covers_5901_of_search: if the search equations of 5,899 and
# 5,900 hold, together with the eleven fields of K16.Evals (K0 to K10) and the nineteen fields of J16.Evals (the
# eighteen joint runs and the ring search RX), then every word that contains all permutations of 7 symbols has at
# least 5,901 letters. Which of these thirty equations are evaluated, and how the others are checked, is in
# ../../n7_5901/README.md.
#
# Run ../n7/build.sh and ../n7_5900/build.sh first: this script works in the same build directory, and the files it
# shares with them (the model, the accounting and the engines of 5,899 and 5,900) are those of ../n7/LowerBounds/
# and ../n7_5900/LowerBounds/.
#
#   1. The Lean files of this directory are compared with sources.sha256.
#   2. Lean compiles F5901Search.lean, F5901.lean, F5901Audit.lean, the counting copy K16Count.lean and the kernel
#      tests A16Test.lean, J16Test.lean and K16SmallSearch.lean. No native_decide. JOBS_BIG processes at a time.
#   3. The "#print axioms" lines; the script fails if one names an axiom other than propext, Classical.choice and
#      Quot.sound.
#
# Settings: those of ../tools/common.sh, and BUILD_DIR (default ../build/words), JOBS_BIG (1), HUNTER_DIR,
# PREIMAGE_DIR as in ../n7/build.sh.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
SOURCES=("$HERE" "$ROOT/n7_5900" "$ROOT/n7" "$ROOT/lower" "$ROOT/words" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR")
MODS="LowerBounds.F5901Search LowerBounds.F5901 LowerBounds.F5901Audit LowerBounds.K16Count"
MODS="$MODS LowerBounds.A16Test LowerBounds.J16Test LowerBounds.K16SmallSearch"

check_tools
mkdir -p "$BUILD/logs"
echo "== 1. the sources"
check_hashes "$HERE/sources.sha256" "$HERE"
echo "== 2. level 1"
# shellcheck disable=SC2086
JOBS="$JOBS_BIG" build_modules $MODS -- "${SOURCES[@]}"
echo "== 3. axioms"
# shellcheck disable=SC2086
print_axioms $MODS
# shellcheck disable=SC2086
OTHER="$(print_axioms $MODS | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
echo "== done: $(date '+%F %T')"
