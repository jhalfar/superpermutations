#!/bin/bash
# Build the proof that a superpermutation on 8 symbols has at least 46,134 letters (Theorem D, with three
# equations evaluated by native_decide).
#
#     ./build.sh           level 1 (no native_decide), the engine, the three evaluations, the theorem, the audit
#     ./build.sh level1    level 1 only: the bound from the three equations, and the kernel test on 5 symbols
#
# The files that this proof shares with the proof for n = 7 (DSearch, DSound, DCapacity, DJunction, JCoverage,
# ...) are those of ../n7/LowerBounds/ and are not copied here; ../lower/ and ../words/ give the rest.
#
#   1. The sources of the two lower-bound libraries and Challenge.lean are compared with their lists of hashes.
#   2. The engine.  One Lean process compiles ../n7/LowerBounds/DSearch.lean (a file with no imports) and writes
#      it as C as well; the C compiler of the Lean toolchain (leanc) makes a shared library of that C file:
#      $BUILD_DIR/native/DSearch.dll, .so or .dylib.
#   3. Level 1: LowerBounds/DFinal.lean (covers_boundD_8_of_search: the bound from the three equations) and
#      LowerBounds/DSmall.lean (the whole chain on 5 symbols, with the search evaluated by the kernel:
#      ssuper_ge_153_D).  No native_decide.  JOBS_BIG processes at a time.
#   4. The evaluations, one Lean process each with the library loaded (--load-dynlib) and JOBS threads:
#      DTestNative (small searches whose answers are known), DLine1Native, DLine2Native, DZoneNative.
#   5. LowerBounds/DFinalNative.lean (the theorem) and AuditD.lean (the statement written with the
#      definitions of Challenge.lean only).
#   6. The "#print axioms" lines.  The script fails unless every statement of level 1 depends on propext,
#      Classical.choice, Quot.sound only, every evaluated equation on propext and its own native_decide axiom
#      only (the two kernel tests of DTestNative on propext only), and covers_lower_bound_8_native on the three standard axioms and the three axioms of the
#      equations.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR         the build directory: ../build/n8_46134
#   LEANC             the C compiler front end of the Lean toolchain: leanc next to $LEAN, or "leanc"
#   JOBS              threads of one evaluation: 1
#   JOBS_BIG          Lean processes at the same time in steps 3 and 5: 1
#   HUNTER_DIR        a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR      a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                     ../deps/superpermutations-preimage-chain-lower-bounds
#   CHECK_SOURCES     1: stop if a source differs from the lists of hashes of step 1: 1
#
# Memory: the files of step 3 import all of Mathlib (about 3.3 GB of working set, 8 GB committed); an
# evaluation needs little.  README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/n8_46134}"
NATIVE="$BUILD/native"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${CHECK_SOURCES:=1}"
PHASE="${1:-full}"
case "$PHASE" in full | level1) ;; *) die "usage: build.sh [level1]" ;; esac
if [ -z "${LEANC:-}" ]; then
  case "$LEAN" in */*) LEANC="$(dirname "$LEAN")/leanc" ;; *) LEANC=leanc ;; esac
fi
case "$(uname -s)" in
  MINGW* | MSYS* | CYGWIN*) LIB="$NATIVE/DSearch.dll"; PIC="" ;;
  Darwin) LIB="$NATIVE/DSearch.dylib"; PIC="-fPIC" ;;
  *) LIB="$NATIVE/DSearch.so"; PIC="-fPIC" ;;
esac
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
SOURCES=("$HERE" "$ROOT/n7" "$ROOT/lower" "$ROOT/words" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR")
LEVEL1="LowerBounds.DFinal LowerBounds.DSmall"
EVALS="LowerBounds.DTestNative LowerBounds.DLine1Native LowerBounds.DLine2Native LowerBounds.DZoneNative"
FINAL="LowerBounds.DFinalNative AuditD"

stamp_of() {   # MODULE: its stamp as tools/order.py computes it with the roots of this build
  "$PYTHON" "$ROOT/tools/order.py" "$1" -- "${SOURCES[@]}" < /dev/null | awk -F'\t' -v m="$1" '$2 == m { print $5 }'
}

# build_engine: step 2.  One Lean run writes DSearch.olean and DSearch.c, so both come from the same source.
build_engine() {
  local mod=LowerBounds.DSearch src="$ROOT/n7/LowerBounds/DSearch.lean" out="$BUILD/lib/LowerBounds/DSearch" stamp
  stamp="$(stamp_of $mod)"
  [ -n "$stamp" ] || die "tools/order.py gave no stamp for $mod"
  if [ -f "$out.olean" ] && [ -f "$LIB" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] \
       && [ "$(cat "$NATIVE/DSearch.stamp" 2> /dev/null)" = "$stamp" ]; then
    echo "DSearch and its library are up to date"
    return
  fi
  mkdir -p "$BUILD/lib/LowerBounds" "$NATIVE"
  rm -f "$out.stamp" "$NATIVE/DSearch.stamp" "$LIB"
  (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS=1 nice -n 19 "$LEAN" "--root=$(native "$ROOT/n7")" \
     -o "$(native "$out.olean")" -i "$(native "$out.ilean")" -c "$(native "$NATIVE/DSearch.c")" \
     "$(native "$src")") < /dev/null > "$BUILD/logs/$mod.log" 2>&1 \
    || die "Lean failed on DSearch.lean, see $BUILD/logs/$mod.log"
  # shellcheck disable=SC2086
  (cd "$ROOT" && nice -n 19 "$LEANC" -shared -O3 $PIC -o "$(native "$LIB")" "$(native "$NATIVE/DSearch.c")") \
    < /dev/null > "$BUILD/logs/leanc.DSearch.log" 2>&1 \
    || die "$LEANC failed on DSearch.c, see $BUILD/logs/leanc.DSearch.log (set LEANC)"
  [ -f "$LIB" ] || die "$LEANC wrote no $LIB"
  echo "$stamp" > "$out.stamp"
  echo "$stamp" > "$NATIVE/DSearch.stamp"
  echo "$(date '+%F %T') ok engine $mod" >> "$BUILD/build.log"
  echo "  compiled DSearch.lean to DSearch.olean, DSearch.c and $(basename "$LIB")"
}

# evaluate MODULE...: step 4, one module after the other, each with JOBS threads and the library loaded.
evaluate() {
  local mod out stamp t0 secs
  for mod in "$@"; do
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
    echo "  evaluating $mod with $JOBS threads ($(date '+%T'))"
    if (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS="$JOBS" nice -n 19 "$LEAN" -j "$JOBS" \
          "--load-dynlib=$(native "$LIB")" "--root=$(native "$HERE")" \
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

echo "== 1. the sources"
[ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
[ -f "$PREIMAGE_DIR/PreimageChain/PathwiseFinalCore.lean" ] \
  || die "no PreimageChain/PathwiseFinalCore.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
if [ "$CHECK_SOURCES" = 1 ]; then
  check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
  check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  grep "  Challenge.lean$" "$ROOT/constant/pantone-sources.sha256" > "$BUILD/hashes_challenge.txt"
  check_hashes "$BUILD/hashes_challenge.txt" "$PANTONE_DIR"
  echo "the sources of both libraries and Challenge.lean agree with the lists of hashes"
fi

echo "== 2. the engine and its library"
build_engine

echo "== 3. level 1"
# shellcheck disable=SC2086
JOBS="$JOBS_BIG" build_modules $LEVEL1 -- "${SOURCES[@]}"
L1_MODS="LowerBounds.DTheorem LowerBounds.D8 LowerBounds.DModel LowerBounds.DFinal LowerBounds.DSmall"

if [ "$PHASE" = full ]; then
  echo "== 4. the evaluations"
  # shellcheck disable=SC2086
  evaluate $EVALS
  echo "== 5. the theorem and its audit"
  # shellcheck disable=SC2086
  JOBS="$JOBS_BIG" build_modules $FINAL -- "${SOURCES[@]}"
fi

echo "== 6. axioms"
# shellcheck disable=SC2086
print_axioms $L1_MODS
# shellcheck disable=SC2086
OTHER="$(print_axioms $L1_MODS | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement of level 1 with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
if [ "$PHASE" = full ]; then
  # shellcheck disable=SC2086
  print_axioms $EVALS $FINAL
  # shellcheck disable=SC2086
  OTHER="$(print_axioms $EVALS | awk '{ s = $1; gsub(/\047/, "", s)
    if ($0 != "\047" s "\047 depends on axioms: [propext, " s "._native.native_decide.ax_1_1]" &&
        $0 != "\047" s "\047 depends on axioms: [propext]") print }')"
  [ -z "$OTHER" ] || die "an evaluated equation that depends on more than propext and its own axiom:
$OTHER"
  WANT="'SuperpermLowerBounds.covers_lower_bound_8_native' depends on axioms: [propext, Classical.choice,"
  WANT="$WANT Quot.sound, SuperpermLowerBounds.S.lineSearch_8_17_38_264._native.native_decide.ax_1_1,"
  WANT="$WANT SuperpermLowerBounds.S.lineSearch_8_4_9_56._native.native_decide.ax_1_1,"
  WANT="$WANT SuperpermLowerBounds.S.zoneSearch_8._native.native_decide.ax_1_1]"
  print_axioms LowerBounds.DFinalNative | grep -q -F -x "$WANT" \
    || die "covers_lower_bound_8_native does not depend on exactly the three standard axioms and the three of the equations"
  echo "covers_lower_bound_8_native: the three standard axioms and the three axioms of the evaluated equations"
fi
echo "== done ($PHASE): $(date '+%F %T')"
