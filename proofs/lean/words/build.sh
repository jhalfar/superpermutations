#!/bin/bash
# Build the proofs for literal words on 7 to 11 symbols, the bridge to the Hunter-Raudvere library and the
# two-sided statements, from sources, into an empty build directory.
#
#     ./build.sh           everything, in the order below
#     ./build.sh words     steps 1 and 2 only (needs Pantone's Challenge.lean and Mathlib, nothing else)
#     ./build.sh lower     step 3 only
# "words" and "lower" compile different modules, so they can run at the same time in two shells.
#
#   1. Certificates.  gen.py (one table entry for every permutation) and gen11.py (one for every rotation
#      class) write Superperm/NAME/ into the build directory, from the word files:
#        N7, N8, N9      gen.py     5,905 / 46,181 / 408,731 letters
#        N10, N10b       gen.py     4,034,873 (rumstd's word, optional) and 4,034,855 letters
#        N9cyc, N10cyc   gen11.py   the words of N9 and N10b again
#        N11             gen11.py   43,930,578 letters
#      Every generated file is compared with the list of hashes generated.sha256, and verify_word.py or
#      verify_blocks.py (which share no code with the generators) checks that the number in the Lean files
#      spells the word file.  Without a word file, the generated files that come with this directory
#      (generated/: N7, N8, N9, N9cyc) are used; N10 is left out; N10b, N10cyc and N11 are required.
#   2. Lean compiles Challenge.lean (Pantone's definitions of Covers and HasWord), the checkers
#      (Superperm/Literal.lean, Groups.lean, Cyc.lean), the certificates, and the statements
#      (Superperm/Upper*.lean, UpperHR*.lean, PermForm.lean, Audit11.lean).
#   3. Lean compiles the 151 modules of the two lower-bound libraries from their sources.
#   4. Lean compiles the bridge and the two-sided statements (Superperm/Bridge.lean, UpperHunter*.lean,
#      TwoSided*.lean).
#   5. The "#print axioms" lines of all statements are printed.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.  gen11.py needs numpy.
#   BUILD_DIR       the build directory: ../build/words
#   SUPERPERM_REPO  a checkout of github.com/jhalfar/superpermutations: ../../..
#                   (right when this directory is proofs/lean/words of that repository)
#   WORD10, WORD11  $SUPERPERM_REPO/words/superpermutation-10-4034855.txt.xz and
#                   $SUPERPERM_REPO/words/superpermutation-11-43930578.txt.xz
#   WORD8           $PANTONE_DIR/words/8/superpermutation-8-46181.txt
#   WORD7, WORD9, WORD10A   no default: see README.md for where these three files come from
#   HUNTER_DIR      a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR    a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                   ../deps/superpermutations-preimage-chain-lower-bounds
#   JOBS_BIG        Lean processes at the same time in steps 3 and 4: 1
#   CHECK_SOURCES   1: stop if the sources of the three outside libraries differ from the lists of hashes
#                   (../constant/pantone-sources.sha256, hunter-sources.sha256, preimage-sources.sha256): 1
#
# Memory: a process of step 2 needs about 1 GB (Tree of N11: 2 GB).  A process of steps 3 and 4 loads all of
# Mathlib: about 4 GB, and it is slow unless the Mathlib files stay in the file cache (keep 6 GB free).
# README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
REPO="${SUPERPERM_REPO:-$ROOT/../..}"
: "${WORD7:=}" "${WORD9:=}" "${WORD10A:=}"
: "${WORD8:=$PANTONE_DIR/words/8/superpermutation-8-46181.txt}"
: "${WORD10:=$REPO/words/superpermutation-10-4034855.txt.xz}"
: "${WORD11:=$REPO/words/superpermutation-11-43930578.txt.xz}"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${CHECK_SOURCES:=1}"
PHASE="${1:-all}"
GEN="$BUILD/gen"

# The text that the generators write into the head of their files (it is part of the hashed files).
SRC7="n=7, 5905 letters: 5905_7_sol1.txt, the first of the four words of 5905 letters that Teodorescu posted to the superpermutators group on 2026-08-18 (groups.google.com/g/superpermutators/c/D5sKkV2jBuc)."
SRC8="n=8, 46181 letters: words/8/superpermutation-8-46181.txt of github.com/jaypantone/superperm-upper-43-80."
SRC9="n=9, 408731 letters: the word of rumstd's pull request 1 to github.com/jaypantone/superperm-upper-43-80."
SRC10A="n=10, 4034873 letters: the word of rumstd's pull request 3 to github.com/jaypantone/superperm-upper-43-80."
SRC10="n=10, 4034855 letters: words/superpermutation-10-4034855.txt.xz of github.com/jhalfar/superpermutations."
SRC11="n=11, 43930578 letters: words/superpermutation-11-43930578.txt.xz of github.com/jhalfar/superpermutations."

# hashes_ok NAME: the files of $GEN/Superperm/NAME are exactly those listed in generated.sha256
hashes_ok() {
  local list="$BUILD/hashes_$1.txt"
  grep "  Superperm/$1/" "$HERE/generated.sha256" > "$list"
  [ "$(ls "$GEN/Superperm/$1" 2> /dev/null | wc -l | tr -d ' ')" = "$(wc -l < "$list" | tr -d ' ')" ] \
    && "$PYTHON" "$ROOT/tools/check_hashes.py" "$list" "$GEN" < /dev/null > /dev/null 2>&1
}

# certificate NAME GENERATOR VERIFIER WORDFILE SOURCE [generator options]
# Returns 1 if there is neither a word file nor a generated copy.
certificate() {
  local name="$1" generator="$2" verifier="$3" word="$4" source="$5"
  shift 5
  if [ -n "$word" ] && [ -f "$word" ]; then
    if ! hashes_ok "$name"; then
      "$PYTHON" "$HERE/$generator" "$word" "$name" --source "$source" --out "$GEN" "$@" \
        < /dev/null > "$BUILD/logs/gen_$name.log" 2>&1 || die "$generator failed, see $BUILD/logs/gen_$name.log"
    fi
    "$PYTHON" "$HERE/$verifier" "$name" "$word" "$GEN" < /dev/null || die "$verifier failed for $name"
  elif [ -d "$HERE/generated/Superperm/$name" ]; then
    mkdir -p "$GEN/Superperm"
    rm -rf "$GEN/Superperm/$name"
    cp -r "$HERE/generated/Superperm/$name" "$GEN/Superperm/$name"
    echo "$name: no word file given; the generated files of this directory are used (not checked against a word)"
  else
    return 1
  fi
  hashes_ok "$name" || die "the files in $GEN/Superperm/$name differ from generated.sha256"
  echo "$name: the generated files agree with generated.sha256"
}

check_tools
mkdir -p "$BUILD/logs" "$GEN"
if [ "$CHECK_SOURCES" = 1 ]; then
  grep "  Challenge.lean$" "$HERE/../constant/pantone-sources.sha256" > "$BUILD/hashes_challenge.txt"
  check_hashes "$BUILD/hashes_challenge.txt" "$PANTONE_DIR"
fi

WORD_TARGETS="Superperm.Upper Superperm.UpperHR Superperm.PermForm Superperm.Upper10b Superperm.UpperCyc"
WORD_TARGETS="$WORD_TARGETS Superperm.Upper11 Audit11"
TWO_TARGETS="Superperm.UpperHunter Superperm.UpperHunter10b Superperm.UpperHunter11"
TWO_TARGETS="$TWO_TARGETS Superperm.TwoSided Superperm.TwoSided10b Superperm.TwoSided11"

if [ "$PHASE" = all ] || [ "$PHASE" = words ]; then
  echo "== 1. certificates"
  MISSING10="word file not found: $WORD10 (set WORD10)"
  MISSING11="word file not found: $WORD11 (set WORD11)"
  certificate N7     gen.py   verify_word.py   "$WORD7"   "$SRC7"   || die "no certificate for N7"
  certificate N8     gen.py   verify_word.py   "$WORD8"   "$SRC8"   || die "no certificate for N8"
  certificate N9     gen.py   verify_word.py   "$WORD9"   "$SRC9"   || die "no certificate for N9"
  certificate N9cyc  gen11.py verify_blocks.py "$WORD9"   "$SRC9"   --depth 6 --bpf 16 || die "no certificate for N9cyc"
  certificate N10cyc gen11.py verify_blocks.py "$WORD10"  "$SRC10"  || die "$MISSING10"
  certificate N11    gen11.py verify_blocks.py "$WORD11"  "$SRC11"  --depth 12 || die "$MISSING11"
  certificate N10b   gen.py   verify_word.py   "$WORD10"  "$SRC10"  || die "$MISSING10"
  certificate N10    gen.py   verify_word.py   "$WORD10A" "$SRC10A" \
    || echo "N10: no word file (WORD10A); the statements for rumstd's word of 4,034,873 letters are left out"
fi
if [ -f "$GEN/Superperm/N10/Main.lean" ]; then
  WORD_TARGETS="$WORD_TARGETS Superperm.Upper10 Superperm.UpperHR10"
  TWO_TARGETS="$TWO_TARGETS Superperm.UpperHunter10 Superperm.TwoSided10"
fi

if [ "$PHASE" = all ] || [ "$PHASE" = words ]; then
  echo "== 2. the literal words"
  build_modules $WORD_TARGETS -- "$HERE" "$GEN" "$PANTONE_DIR"
fi

if [ "$PHASE" = all ] || [ "$PHASE" = lower ]; then
  echo "== 3. the two lower-bound libraries"
  [ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
  [ -f "$PREIMAGE_DIR/PreimageChain/SuperpermNumericalBounds.lean" ] \
    || die "no PreimageChain/SuperpermNumericalBounds.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
  if [ "$CHECK_SOURCES" = 1 ]; then
    check_hashes "$HERE/hunter-sources.sha256" "$HUNTER_DIR"
    check_hashes "$HERE/preimage-sources.sha256" "$PREIMAGE_DIR"
    echo "the sources of both libraries agree with the lists of hashes"
  fi
  JOBS="$JOBS_BIG" build_modules PreimageChain.SuperpermNumericalBounds -- "$HUNTER_DIR" "$PREIMAGE_DIR"
fi

if [ "$PHASE" = all ]; then
  echo "== 4. the bridge and the two-sided statements"
  JOBS="$JOBS_BIG" build_modules $TWO_TARGETS -- "$HERE" "$GEN" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR"
fi

if [ "$PHASE" != lower ]; then
  echo "== 5. axioms of the statements"
  STATEMENTS="$WORD_TARGETS"
  [ "$PHASE" = all ] && STATEMENTS="$STATEMENTS Superperm.Bridge $TWO_TARGETS"
  print_axioms $STATEMENTS
  echo "== all \"#print axioms\" lines of the build, counted by the list of axioms"
  axiom_summary
fi
echo "== done ($PHASE): $(date '+%F %T')"
