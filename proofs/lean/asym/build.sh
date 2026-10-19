#!/bin/bash
# Build ConstAsym.Main: L(n) is within F3(n) and F3(n) + eps (n-3)! for large n, so that
# (L(n) - F3(n)) / (n-3)! tends to 0.
#
#     ./build.sh
#
# Needs, besides what ../tools/common.sh describes (LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES, JOBS, ...):
#   PREIMAGE_DIR a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds (Liu's library,
#                used unchanged; the commit is the one in ../words/preimage-sources.sha256), for Remainder8
#   HUNTER_DIR   a checkout of github.com/urdvr/superpermutations-hunter at commit d4522219 (the Hunter-Raudvere
#                library, used unchanged): ../deps/superpermutations-hunter
# What happens: Pantone's sources are checked, then Lean compiles the modules that ConstAsym.Main needs, in
# dependency order: his library (with the patched file of ../constant/patches/), the Hunter modules behind
# Hunter.Paper (75 of them), the development of ../constant43586371 up to Uniform.Main, and the two files here.
# The "#print axioms" lines of the final statements are printed.
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
BUILD="${BUILD_DIR:-$ROOT/build/asym}"
CHECK_PANTONE="${CHECK_PANTONE:-1}"
echo "== 1. tools and sources"
check_tools
[ -f "$HUNTER_DIR/Hunter/Paper.lean" ] || die "no Hunter/Paper.lean in $HUNTER_DIR (set HUNTER_DIR; commit d4522219)"
mkdir -p "$BUILD"
if [ "$CHECK_PANTONE" = 1 ]; then
  check_hashes "$ROOT/constant/pantone-sources.sha256" "$PANTONE_DIR"
fi
echo "== 2. Lean"
build_modules ConstAsym.Main ConstAsym.Remainder ConstAsym.Remainder8 -- "$HERE" "$ROOT/constant43586371" "$ROOT/lower" "$ROOT/words" "$ROOT/constant/patches" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR"
echo "== 3. axioms of the final statements"
print_axioms ConstAsym.Main ConstAsym.Remainder ConstAsym.Remainder8
echo "== done: $(date '+%F %T')"
