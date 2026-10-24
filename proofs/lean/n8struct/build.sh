#!/bin/bash
# Build the Lean files about the 27-walk and the packing of four 27-walks at n = 8, from sources, into an empty
# build directory.
#
#     ./build.sh
#
# What happens, in this order:
#   1. The tools are checked, and the sources of Pantone's library are compared with the list of hashes
#      ../constant/pantone-sources.sha256 (his commit c8fb7ff).
#   2. gen.py recomputes the finite data with the model of words/n8/tools and writes gen_out.txt and
#      gen_out2.txt into the build directory; both must be identical to the files here.  The Lean files do not
#      read these files: every table in them is tied to the definitions by a kernel decision.  The step only
#      shows that the tables agree with the tool.
#   3. Lean compiles, in dependency order, the modules of Pantone's library that N8Struct/Definitions.lean
#      imports (from his sources, with the patched file of ../constant/patches/), and the nine files of
#      N8Struct/.
#   4. The "#print axioms" lines are printed.  The script fails if one of them names an axiom other than
#      propext, Classical.choice and Quot.sound.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR       the build directory: ../build/n8struct
#   SUPERPERM_REPO  a checkout of github.com/jhalfar/superpermutations: ../../..
#   CHECK_PANTONE   1: stop if his sources differ from pantone-sources.sha256.  0: go on anyway: 1
#
# Memory: the largest Lean process (Symmetry.lean) needs about 5 GB of committed memory.  README.md has the
# measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/n8struct}"
REPO="${SUPERPERM_REPO:-$ROOT/../..}"
CHECK_PANTONE="${CHECK_PANTONE:-1}"
PATCHES="$ROOT/constant/patches"
MODULES="N8Struct.Definitions N8Struct.Walk27 N8Struct.Symmetry N8Struct.PackBase N8Struct.Partners"
MODULES="$MODULES N8Struct.Classify N8Struct.Orbits N8Struct.Published N8Struct.Reversal"
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'

echo "== 1. tools and sources"
check_tools
mkdir -p "$BUILD/gen"
if [ "$CHECK_PANTONE" = 1 ]; then
  check_hashes "$ROOT/constant/pantone-sources.sha256" "$PANTONE_DIR"
  echo "Pantone's sources agree with constant/pantone-sources.sha256"
fi

echo "== 2. the finite data, recomputed with the model of words/n8/tools"
if [ -f "$REPO/words/n8/tools/n8lib/model.py" ]; then
  PYTHONDONTWRITEBYTECODE=1 "$PYTHON" "$HERE/gen.py" "$BUILD/gen" < /dev/null > "$BUILD/gen.log" 2>&1 \
    || die "gen.py failed, see $BUILD/gen.log"
  for f in gen_out.txt gen_out2.txt; do
    cmp -s "$BUILD/gen/$f" "$HERE/$f" || die "gen.py wrote a $f that differs from the one in this directory"
  done
  echo "gen.py wrote gen_out.txt and gen_out2.txt, identical to the files here"
else
  echo "no words/n8/tools/n8lib/model.py under $REPO: step skipped (the Lean files do not need it)"
fi

echo "== 3. Lean"
# shellcheck disable=SC2086
build_modules $MODULES -- "$HERE" "$PATCHES" "$PANTONE_DIR"

echo "== 4. axioms"
# shellcheck disable=SC2086
print_axioms $MODULES
# shellcheck disable=SC2086
OTHER="$(print_axioms $MODULES | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
echo "== all \"#print axioms\" lines of the build, counted by the list of axioms"
axiom_summary
echo "== done: $(date '+%F %T')"
