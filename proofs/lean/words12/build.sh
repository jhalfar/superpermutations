#!/bin/bash
# Build the proof that the word of 522,737,175 letters for n = 12 is a superpermutation, and the statements
# that use it.
#
#     ./build.sh           everything, in the order below
#     ./build.sh word      steps 1 and 2 only (needs Pantone's Challenge.lean and Mathlib, nothing else)
#
# The script works in the build directory of ../words/build.sh.  What that script has compiled is not
# compiled again; what is missing is compiled here.
#
#   1. ../words/check_word.sh takes the word file through all of its steps: it generates the certificate
#      Superperm/N12/ (255 files, 0.9 GB) into the build directory, lets Lean check it (254 modules, about 6
#      hours of Lean time), and checks the blocks in the Lean files against the word file.
#   2. The generated files are compared with the list of hashes generated.sha256, and Lean compiles
#      Superperm/Upper12.lean.
#   3. Lean compiles Superperm/UpperHunter12.lean and TwoSided12.lean: the upper bound for Hunter.Ssuper 12
#      and the two-sided statement with Liu's lower bound.  Then Audit12.lean, which writes the statements
#      out in full.
#   4. The "#print axioms" lines of the statements are printed.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.  gen12.py needs numpy and 2 GB.
#   BUILD_DIR       the build directory: ../build/words
#   SUPERPERM_REPO  a checkout of github.com/jhalfar/superpermutations: ../../..
#   WORD12          $SUPERPERM_REPO/words/superpermutation-12-522737175.txt.xz
#   HUNTER_DIR      a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR    a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                   ../deps/superpermutations-preimage-chain-lower-bounds
#   JOBS_BIG        Lean processes at the same time in step 3: 1
#   CHECK_SOURCES   1: stop if the sources of the two libraries differ from the lists of hashes: 1
#
# Memory: a process of step 1 needs up to 1.3 GB (one module 1.8 GB).  A process of step 3 loads all of
# Mathlib: about 4 GB.  Step 1 is long, so JOBS matters here.  README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
REPO="${SUPERPERM_REPO:-$ROOT/../..}"
: "${WORD12:=$REPO/words/superpermutation-12-522737175.txt.xz}"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${CHECK_SOURCES:=1}"
PHASE="${1:-all}"
GEN="$BUILD/gen"

echo "== 1. the word, with ../words/check_word.sh"
[ -f "$WORD12" ] || die "word file not found: $WORD12 (set WORD12)"
bash "$ROOT/words/check_word.sh" "$WORD12" --out "$BUILD" --jobs "$JOBS" --minfree "$MINFREE_GB" --yes \
  || exit $?

echo "== 2. the literal word"
check_hashes "$HERE/generated.sha256" "$GEN"
echo "N12: the generated files agree with generated.sha256"
build_modules Superperm.Upper12 -- "$HERE" "$ROOT/words" "$GEN" "$PANTONE_DIR"

STATEMENTS="Superperm.Upper12"
if [ "$PHASE" = all ]; then
  echo "== 3. the statements for Hunter.Ssuper 12"
  [ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
  [ -f "$PREIMAGE_DIR/PreimageChain/SuperpermNumericalBounds.lean" ] \
    || die "no PreimageChain/SuperpermNumericalBounds.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
  if [ "$CHECK_SOURCES" = 1 ]; then
    check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
    check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  fi
  TWO="Superperm.UpperHunter12 Superperm.TwoSided12 Audit12"
  JOBS="$JOBS_BIG" build_modules $TWO -- \
    "$HERE" "$ROOT/words" "$GEN" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR"
  STATEMENTS="$STATEMENTS $TWO"
fi

echo "== 4. axioms of the statements"
print_axioms $STATEMENTS
echo "== all \"#print axioms\" lines in the build directory, counted by the list of axioms"
axiom_summary
echo "== done ($PHASE): $(date '+%F %T')"
