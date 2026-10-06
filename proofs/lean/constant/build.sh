#!/bin/bash
# Build the Lean development for the coefficient 1771/3456 from sources, into an empty build directory.
#
#     ./build.sh
#
# What happens, in this order:
#   1. The tools are checked, and the sources of Pantone's library are compared with the list of hashes
#      pantone-sources.sha256 (his commit c8fb7ff, the one this development was written against).
#   2. gen_cert.py is run on the two public input files, and its output is compared with the certificate
#      files in SuperpermutationUpperBound1771/Certificate/.  They must be identical.
#   3. Lean compiles, in dependency order:
#        the 95 modules of Pantone's library that the development imports, from his sources
#          (one of them, Assembly/SupportedStates.lean, from the patched copy in patches/);
#        the 49 modules of SuperpermutationUpperBound1771;
#        Audit1771.lean, which restates the results with the definitions of his Challenge.lean only.
#   4. The "#print axioms" lines of the final statements are printed.
#
# Nothing that Pantone's project has compiled is used, and nothing is written outside the build directory.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR       the build directory: ../build/constant
#   SUPERPERM_REPO  a checkout of github.com/jhalfar/superpermutations: ../../..
#                   (right when this directory is proofs/lean/constant of that repository)
#   SELECTION       the selection on 11 symbols: $SUPERPERM_REPO/arrange/data/n12t-selection.txt.xz
#   CYCLES          the 203 connector cycles: $SUPERPERM_REPO/selection/data/zcycles_n12.txt
#   USE_PATCH       1: compile patches/SupportedStates.lean in place of his file.  0: use his file; then his
#                   certificate for 9 symbols (Certificates/NineRecipe.lean) is compiled as well, which did
#                   not fit into 13.6 GB of memory on my machine: 1
#   CHECK_PANTONE   1: stop if his sources differ from pantone-sources.sha256.  0: go on anyway: 1
#
# Memory: the largest Lean process needs about 4 GB of working set, so JOBS=2 wants 8 GB free.
# README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/constant}"
REPO="${SUPERPERM_REPO:-$ROOT/../..}"
SELECTION="${SELECTION:-$REPO/arrange/data/n12t-selection.txt.xz}"
CYCLES="${CYCLES:-$REPO/selection/data/zcycles_n12.txt}"
USE_PATCH="${USE_PATCH:-1}"
CHECK_PANTONE="${CHECK_PANTONE:-1}"
NAME=SuperpermutationUpperBound1771

echo "== 1. tools and sources"
check_tools
mkdir -p "$BUILD"
if [ "$CHECK_PANTONE" = 1 ]; then
  check_hashes "$HERE/pantone-sources.sha256" "$PANTONE_DIR"
  echo "Pantone's sources agree with pantone-sources.sha256"
fi

echo "== 2. the certificate files"
if [ -f "$SELECTION" ] && [ -f "$CYCLES" ]; then
  rm -rf "$BUILD/gen"
  mkdir -p "$BUILD/gen"
  "$PYTHON" "$HERE/gen_cert.py" "$SELECTION" "$CYCLES" --out "$BUILD/gen" < /dev/null > "$BUILD/gen_cert.log" \
    || die "gen_cert.py failed, see $BUILD/gen_cert.log"
  for f in "$BUILD/gen"/*.lean; do
    cmp -s "$f" "$HERE/$NAME/Certificate/$(basename "$f")" \
      || die "gen_cert.py wrote a $(basename "$f") that differs from the one in $NAME/Certificate/"
  done
  echo "gen_cert.py wrote $(ls "$BUILD/gen"/*.lean | wc -l | tr -d ' ') files, identical to those in $NAME/Certificate/"
else
  echo "input files not found ($SELECTION, $CYCLES):"
  echo "the certificate files are used as they are in $NAME/Certificate/ and are NOT generated again"
fi

echo "== 3. Lean"
if [ "$USE_PATCH" = 1 ]; then
  build_modules $NAME.Corollaries Audit1771 -- "$HERE" "$HERE/patches" "$PANTONE_DIR"
else
  build_modules $NAME.Corollaries Audit1771 -- "$HERE" "$PANTONE_DIR"
fi

echo "== 4. axioms of the final statements"
print_axioms $NAME.Main13 $NAME.Main $NAME.Corollaries
echo "== all \"#print axioms\" lines of the build, counted by the list of axioms"
axiom_summary
echo "== done: $(date '+%F %T')"
