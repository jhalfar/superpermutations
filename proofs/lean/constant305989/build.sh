#!/bin/bash
# Build the Lean development for the coefficient 305989/604800 from sources, into an empty build directory.
#
#     ./build.sh
#
# What happens, in this order:
#   1. The tools are checked, and the sources of Pantone's library are compared with the list of hashes
#      ../constant/pantone-sources.sha256 (his commit c8fb7ff).
#   2. gen_cert.py is run on the two public input files, and gen_blockB.py on the three files in data/ (the
#      block above one loop of 10 symbols and its connector cycles).  Their output is compared with the
#      certificate files in SuperpermutationUpperBound305989/Certificate/.  They must be identical.  gen_cert.py
#      needs numpy and scipy (an integer programme, solved by HiGHS, chooses connector cycles).
#   3. Lean compiles, in dependency order:
#        the modules of Pantone's library that the development imports, from his sources
#          (one of them, Assembly/SupportedStates.lean, from the patched copy in ../constant/patches/);
#        the modules of SuperpermutationUpperBound305989.
#   4. The "#print axioms" lines of the final statements are printed.
#
# Nothing that Pantone's project has compiled is used, and nothing is written outside the build directory.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR       the build directory: ../build/constant305989
#   SUPERPERM_REPO  a checkout of github.com/jhalfar/superpermutations: ../../..
#                   (right when this directory is proofs/lean/constant305989 of that repository)
#   SELECTION       the selection on 11 symbols: $SUPERPERM_REPO/arrange/data/n12t-selection.txt.xz
#   CYCLES          the 203 connector cycles: $SUPERPERM_REPO/selection/data/zcycles_n12.txt
#   CHECK_PANTONE   1: stop if his sources differ from pantone-sources.sha256.  0: go on anyway: 1
#
# Memory: the largest Lean process needs about 4 GB of working set, so JOBS=2 wants 8 GB free.
# README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/constant305989}"
REPO="${SUPERPERM_REPO:-$ROOT/../..}"
SELECTION="${SELECTION:-$REPO/arrange/data/n12t-selection.txt.xz}"
CYCLES="${CYCLES:-$REPO/selection/data/zcycles_n12.txt}"
CHECK_PANTONE="${CHECK_PANTONE:-1}"
NAME=SuperpermutationUpperBound305989
PATCHES="$ROOT/constant/patches"

echo "== 1. tools and sources"
check_tools
mkdir -p "$BUILD"
if [ "$CHECK_PANTONE" = 1 ]; then
  check_hashes "$ROOT/constant/pantone-sources.sha256" "$PANTONE_DIR"
  echo "Pantone's sources agree with constant/pantone-sources.sha256"
fi

echo "== 2. the certificate files"
if [ -f "$SELECTION" ] && [ -f "$CYCLES" ]; then
  rm -rf "$BUILD/gen"
  mkdir -p "$BUILD/gen"
  "$PYTHON" "$HERE/gen_cert.py" "$SELECTION" "$CYCLES" --out "$BUILD/gen" < /dev/null > "$BUILD/gen_cert.log" \
    || die "gen_cert.py failed, see $BUILD/gen_cert.log"
  for f in "$BUILD/gen"/*.lean "$BUILD/gen"/modules.txt; do
    cmp -s "$f" "$HERE/$NAME/Certificate/$(basename "$f")" \
      || die "gen_cert.py wrote a $(basename "$f") that differs from the one in $NAME/Certificate/"
  done
  "$PYTHON" "$HERE/gen_blockB.py" "$HERE/data/s103_old2_0.txt" "$HERE/data/cyc_s103_old2_0.txt" "$HERE/data/cyc_t_s103_old2_0_n16.txt"     --out "$BUILD/gen" < /dev/null > "$BUILD/gen_blockB.log" || die "gen_blockB.py failed, see $BUILD/gen_blockB.log"
  for f in "$BUILD/gen"/*.lean; do
    cmp -s "$f" "$HERE/$NAME/Certificate/$(basename "$f")"       || die "a generator wrote a $(basename "$f") that differs from the one in $NAME/Certificate/"
  done
  echo "the generators wrote $(ls "$BUILD/gen"/*.lean | wc -l | tr -d ' ') files, identical to those in $NAME/Certificate/"
else
  echo "input files not found ($SELECTION, $CYCLES):"
  echo "the certificate files are used as they are in $NAME/Certificate/ and are NOT generated again"
fi

echo "== 3. Lean"
build_modules $NAME.CorollariesB -- "$HERE" "$PATCHES" "$PANTONE_DIR"

echo "== 4. axioms of the final statements"
print_axioms $NAME.MainB $NAME.CorollariesB
echo "== all \"#print axioms\" lines of the build, counted by the list of axioms"
axiom_summary
echo "== done: $(date '+%F %T')"
