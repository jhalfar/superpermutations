#!/bin/bash
# Build the proof that a superpermutation on 7 symbols has at least 5,900 letters.
#
#     ./build.sh           level 1, the two engines, the kernel tests and the native tests (a few hours)
#     ./build.sh full      the same, then the 72 evaluations, the theorem and its audit (about 4,200 thread-hours)
#     ./build.sh one NAME  the default level, then the one evaluation module NAME of evaluations.txt (a test)
#
# The proof stands on the proof of 5,899 in ../n7/: its model, its level 1 and, for the theorem, its 17
# evaluation modules and PFinalNative. Run ../n7/build.sh (with "full" before "./build.sh full") first: this script
# works in the same build directory and compiles here only what is missing, so the files of ../n7/, ../lower/ and
# ../words/ that it imports are compiled once.
#
#   1. The Lean files of this directory are compared with sources.sha256, and the sources of the two libraries and
#      Challenge.lean with their lists.
#   2. The engines. One Lean process each compiles ../n7/LowerBounds/PSearch.lean, LowerBounds/KSearch.lean and
#      LowerBounds/J15Search.lean (files that import nothing beyond each other) and writes them as C as well; the C
#      compiler of the Lean toolchain (leanc) makes two shared libraries in $BUILD_DIR/native: KSearch (KSearch.c,
#      PSearch.c) and J15Search (J15Search.c, KSearch.c, PSearch.c).
#   3. Level 1: LowerBounds/F5900.lean (covers_5900_of_search: the bound from the search equations),
#      F5900Joint.lean, Audit5900.lean, Audit5900Search.lean, and the kernel tests KSmall, KSmallSearch,
#      J15SmallSearch, A15Test. No native_decide. JOBS_BIG processes at a time.
#   4. KTestNative and J15TestNative: small searches evaluated by native_decide with the libraries loaded, among them
#      searches that the kernel also evaluates in step 3 and searches whose answer is "true".
#   5. At the level "full": the modules of evaluations.txt, one Lean process each with its library loaded
#      (--load-dynlib) and JOBS threads, in the order of the file. A module that is up to date is not run again.
#   6. At the level "full": LowerBounds/F5900Native.lean (the theorem) and Audit5900Native.lean. This step needs
#      PFinalNative of ../n7/ in the build directory (../n7/build.sh full).
#   7. The "#print axioms" lines. The script fails unless every statement of step 3 depends on propext,
#      Classical.choice, Quot.sound only, every evaluated equation on propext and its own native_decide axiom only
#      (kernel checks inside the test modules on propext only), and, at the level "full",
#      covers_lower_bound_7_5900_native on the three standard axioms and exactly 99 native_decide axioms.
#
# Settings (environment variables; default after the colon). LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR         the build directory: ../build/words (the one of ../n7/build.sh)
#   LEANC             the C compiler front end of the Lean toolchain: leanc next to $LEAN, or "leanc"
#   JOBS              threads of one evaluation: 1
#   JOBS_BIG          Lean processes at the same time in steps 3 and 6: 1
#   HUNTER_DIR, PREIMAGE_DIR, CHECK_SOURCES   as in ../n7/build.sh
#
# Memory: most files of steps 3 and 6 import all of Mathlib (about 3.5 GB of working set, 8 GB committed). An
# evaluation needs 0.5 to 4 GB. README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
NATIVE="$BUILD/native"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${CHECK_SOURCES:=1}"
PHASE="${1:-default}"
ONE="${2:-}"
case "$PHASE" in default | full) ;; one) [ -n "$ONE" ] || die "usage: build.sh one NAME" ;; *) die "usage: build.sh [full | one NAME]" ;; esac
if [ -z "${LEANC:-}" ]; then
  case "$LEAN" in */*) LEANC="$(dirname "$LEAN")/leanc" ;; *) LEANC=leanc ;; esac
fi
case "$(uname -s)" in
  MINGW* | MSYS* | CYGWIN*) EXT=dll; PIC="" ;;
  Darwin) EXT=dylib; PIC="-fPIC" ;;
  *) EXT=so; PIC="-fPIC" ;;
esac
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
SOURCES=("$HERE" "$ROOT/n7" "$ROOT/lower" "$ROOT/words" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR")
LEVEL1="LowerBounds.F5900 LowerBounds.F5900Joint Audit5900 Audit5900Search"
LEVEL1="$LEVEL1 LowerBounds.KSmall LowerBounds.KSmallSearch LowerBounds.J15SmallSearch LowerBounds.A15Test"
TESTS="K:LowerBounds.KTestNative J:LowerBounds.J15TestNative"
FINAL="LowerBounds.F5900Native Audit5900Native"

stamp_of() {   # MODULE: its stamp as tools/order.py computes it with the roots of this build
  "$PYTHON" "$ROOT/tools/order.py" "$1" -- "${SOURCES[@]}" < /dev/null | awk -F'\t' -v m="$1" '$2 == m { print $5 }'
}

# engine NAME SOURCE ROOTDIR: one Lean run writes NAME.olean and NAME.c from the same source
engine() {
  local mod="LowerBounds.$1" src="$2" root="$3" out="$BUILD/lib/LowerBounds/$1" stamp
  stamp="$(stamp_of "$mod")"
  [ -n "$stamp" ] || die "tools/order.py gave no stamp for $mod"
  if [ -f "$out.olean" ] && [ -f "$NATIVE/$1.c" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] \
       && [ "$(cat "$NATIVE/$1.c.stamp" 2> /dev/null)" = "$stamp" ]; then
    echo "  $1 and its C file are up to date"
    return
  fi
  mkdir -p "$BUILD/lib/LowerBounds" "$NATIVE"
  rm -f "$out.stamp" "$NATIVE/$1.c.stamp"
  (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS=1 nice -n 19 "$LEAN" "--root=$(native "$root")" \
     -o "$(native "$out.olean")" -i "$(native "$out.ilean")" -c "$(native "$NATIVE/$1.c")" \
     "$(native "$src")") < /dev/null > "$BUILD/logs/$mod.log" 2>&1 || die "Lean failed on $src, see $BUILD/logs/$mod.log"
  echo "$stamp" > "$out.stamp"
  echo "$stamp" > "$NATIVE/$1.c.stamp"
  echo "  compiled $1.lean to $1.olean and $1.c"
}

# library NAME C-FILES...: leanc links the C files into NAME.EXT
library() {
  local name="$1" lib="$NATIVE/$1.$EXT" args=() f
  shift
  for f in "$@"; do args+=("$(native "$NATIVE/$f.c")"); done
  # shellcheck disable=SC2086
  (cd "$ROOT" && nice -n 19 "$LEANC" -shared -O3 $PIC -o "$(native "$lib")" "${args[@]}") < /dev/null \
    > "$BUILD/logs/leanc.$name.log" 2>&1 || die "$LEANC failed on $name, see $BUILD/logs/leanc.$name.log"
  [ -f "$lib" ] || die "$LEANC wrote no $lib"
  echo "  $LEANC made $name.$EXT"
}

# evaluate KIND:MODULE...: one Lean process per module, with the library of its kind (K: KSearch, J: J15Search)
evaluate() {
  local item kind mod lib out stamp t0 secs
  for item in "$@"; do
    kind="${item%%:*}"; mod="${item#*:}"
    case "$kind" in K) lib="$NATIVE/KSearch.$EXT" ;; J) lib="$NATIVE/J15Search.$EXT" ;; *) die "kind $kind" ;; esac
    out="$BUILD/lib/${mod//.//}"
    stamp="$(stamp_of "$mod")"
    [ -n "$stamp" ] || die "tools/order.py gave no stamp for $mod"
    if [ -f "$out.olean" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ]; then
      echo "  $mod is up to date"
      continue
    fi
    [ -e "$BUILD/STOP" ] && { echo "stopped by the file $BUILD/STOP"; exit 2; }
    rm -f "$out.stamp"
    t0=$(date +%s)
    echo "  evaluating $mod with $JOBS threads ($(date '+%F %T'))"
    if (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS="$JOBS" nice -n 19 "$LEAN" -j "$JOBS" \
          "--load-dynlib=$(native "$lib")" "--root=$(native "$HERE")" \
          -o "$(native "$out.olean")" -i "$(native "$out.ilean")" \
          "$(native "$HERE/${mod//.//}.lean")") < /dev/null > "$BUILD/logs/$mod.log" 2>&1; then
      secs=$(( $(date +%s) - t0 ))
      echo "$stamp" > "$out.stamp"
      echo "$(date '+%F %T') ok $secs s $mod ($JOBS threads)" >> "$BUILD/build.log"
      echo "  evaluated $mod ($secs s)"
    else
      rm -f "$out.olean" "$out.ilean"
      die "Lean failed on $mod, see $BUILD/logs/$mod.log"
    fi
  done
}

check_tools
(cd "$ROOT" && "$LEANC" --version > /dev/null 2>&1) \
  || die "\"$LEANC --version\" fails (set LEANC to the leanc of the Lean toolchain)"
mkdir -p "$BUILD/logs" "$NATIVE"
set_lean_path

echo "== 1. the sources ($PHASE level)"
[ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
[ -f "$PREIMAGE_DIR/PreimageChain/PathwiseFinalCore.lean" ] \
  || die "no PreimageChain/PathwiseFinalCore.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
if [ "$CHECK_SOURCES" = 1 ]; then
  check_hashes "$HERE/sources.sha256" "$HERE"
  check_hashes "$ROOT/n7/sources.sha256" "$ROOT"
  check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
  check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  grep "  Challenge.lean$" "$ROOT/constant/pantone-sources.sha256" > "$BUILD/hashes_challenge.txt"
  check_hashes "$BUILD/hashes_challenge.txt" "$PANTONE_DIR"
  echo "the Lean files of this proof and of ../n7, the two libraries and Challenge.lean agree with the lists of hashes"
fi

echo "== 2. the engines and their libraries"
engine PSearch "$ROOT/n7/LowerBounds/PSearch.lean" "$ROOT/n7"
engine KSearch "$HERE/LowerBounds/KSearch.lean" "$HERE"
engine J15Search "$HERE/LowerBounds/J15Search.lean" "$HERE"
library KSearch KSearch PSearch
library J15Search J15Search KSearch PSearch

echo "== 3. level 1 and the kernel tests"
# shellcheck disable=SC2086
JOBS="$JOBS_BIG" build_modules $LEVEL1 -- "${SOURCES[@]}"

echo "== 4. the compiled searches against the kernel and against known answers"
# shellcheck disable=SC2086
evaluate $TESTS

EVALS=""
FINALS=""
if [ "$PHASE" = one ]; then
  echo "== 5. one evaluation: $ONE"
  KIND="$(awk -v m="$ONE" '$2 == m { print $1 }' "$HERE/evaluations.txt")"
  [ -n "$KIND" ] || die "$ONE is not in evaluations.txt"
  EVALS="$KIND:LowerBounds.$ONE"
  evaluate $EVALS
fi
if [ "$PHASE" = full ]; then
  echo "== 5. the 72 evaluations"
  while read -r kind name; do
    case "$kind" in "" | "#"*) continue ;; esac
    EVALS="$EVALS $kind:LowerBounds.$name"
  done < "$HERE/evaluations.txt"
  # shellcheck disable=SC2086
  evaluate $EVALS
  echo "== 6. the theorem and its audit"
  [ -f "$BUILD/lib/LowerBounds/PFinalNative.olean" ] || die "no PFinalNative in $BUILD: run ../n7/build.sh full first"
  # shellcheck disable=SC2086
  JOBS="$JOBS_BIG" build_modules $FINAL -- "${SOURCES[@]}"
  FINALS="$FINAL"
fi

echo "== 7. axioms"
# shellcheck disable=SC2086
print_axioms $LEVEL1
# shellcheck disable=SC2086
OTHER="$(print_axioms $LEVEL1 | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement of level 1 with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
NATMODS="$(for x in $TESTS $EVALS; do printf '%s ' "${x#*:}"; done)"
# shellcheck disable=SC2086
OTHER="$(print_axioms $NATMODS | awk '{ s = $1; gsub(/\047/, "", s)
  if ($0 != "\047" s "\047 depends on axioms: [propext, " s "._native.native_decide.ax_1_1]" &&
      $0 != "\047" s "\047 depends on axioms: [propext]") print }')"
[ -z "$OTHER" ] || die "an evaluated equation that depends on more than propext and its own axiom:
$OTHER"
echo "$(print_axioms $NATMODS | grep -c "depends on axioms") evaluated equations and tests, each with propext and its own axiom"
if [ "$PHASE" = full ]; then
  LINE="$(print_axioms Audit5900Native LowerBounds.F5900Native | grep "covers_lower_bound_7_5900_native' depends on axioms" | head -1)"
  [ -n "$LINE" ] || die "no #print axioms line for covers_lower_bound_7_5900_native"
  NNAT="$(echo "$LINE" | grep -o "_native\.native_decide\.ax_1_1" | wc -l | tr -d ' ')"
  REST="$(echo "$LINE" | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' | sed 's/^ *//' \
    | grep -v "_native\.native_decide\.ax_1_1$" | LC_ALL=C sort | tr '\n' ' ')"
  [ "$NNAT" = 99 ] && [ "$REST" = "Classical.choice Quot.sound propext " ] \
    || die "covers_lower_bound_7_5900_native: $NNAT native_decide axioms (99 expected), other axioms: $REST"
  echo "covers_lower_bound_7_5900_native: propext, Classical.choice, Quot.sound and 99 native_decide axioms"
fi
echo "== done ($PHASE): $(date '+%F %T')"
