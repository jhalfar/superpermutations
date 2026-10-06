#!/bin/bash
# Build three variants of William Echols's Lean proof of a lower bound for n = 8, none of which uses
# native_decide:
#     v46130k    46,130 <= L(8)   his bound
#     v46131k    46,131 <= L(8)
#     v46132bk   46,132 <= L(8)
#
#     ./build.sh                  all three
#     ./build.sh v46131k          one of them (or several)
#
# Nothing is fetched.  You clone github.com/williamechols/superperm8-ge-46130 at commit
# 893ab2d92669ea56d012ceca626bf01ca631e920 yourself (see README.md) and point ECHOLS_DIR at it.  His checkout
# is only read.
#
# For each variant:
#   1. Sources.  His 36 Lean files are compared with the list of hashes echols-sources.sha256 and copied into
#      the build directory with LF line ends.  Then:
#        the two files of his that the variant does not use are left out
#          (Superperm8/AffineSound.lean, AffineCheck.lean: his search under native_decide);
#        variants/VARIANT/changes.diff is applied (the port to Lean 4.31.0, the constants of the variant,
#          the passage to the kernel-checked search);
#        the new files are added: kernel/Superperm8/KSearch.lean, KCode.lean, KSound.lean and
#          variants/VARIANT/Plain.lean.
#      These files are compared, one by one, with the list of hashes variants/VARIANT/files.sha256.  Then the
#      placeholder @ATTRIBUTION@ in the notices of the changed and the new files is filled in (see ATTRIBUTION
#      below), and tools/plan.py writes the parts of the search (Superperm8/K<NAME>*.lean), which are compared
#      with variants/VARIANT/generated.sha256.
#   2. Lean compiles Solution, Plain and AxiomAudit and everything they import, from these sources.
#   3. The "#print axioms" lines are printed.  The script fails if any of them names an axiom other than
#      propext, Classical.choice, Quot.sound.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.  This part needs of Pantone's checkout
# only the compiled Mathlib in it.  The program patch must be installed.
#   ECHOLS_DIR   the checkout of Echols's repository: ../deps/superperm8-ge-46130
#   BUILD_DIR    the build directory; each variant gets a directory of its own in it: ../build/n8
#
# Memory: a Lean process needs up to 2.6 GB.  README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
: "${ECHOLS_DIR:=$ROOT/deps/superperm8-ge-46130}"
BUILD_ROOT="${BUILD_DIR:-$ROOT/build/n8}"
VARIANTS="${*:-v46130k v46131k v46132bk}"
export PYTHONDONTWRITEBYTECODE=1          # Python writes nothing next to tools/plan.py
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'

# The words of the notice in every file of Echols that a variant changes ("Changed ATTRIBUTION: ...") and in
# every Plain.lean ("Written ATTRIBUTION.").  This line is the one place where they are set: the diffs and the
# Plain.lean files under variants/ have the placeholder @ATTRIBUTION@ in their place.
ATTRIBUTION="2026-10-06 by Jakub Halfar (github.com/jhalfar/superpermutations)"

# The search of each variant: the inequality  A * rows <= Bd + Cc * charge  for every model trail, proven by
# `K.fsearch A Cc Bd FUEL = false`; NAME is the name of the generated files.
search_of() {
  case "$1" in
    v46130k)  echo "20 49 136 68 T136";;
    v46131k)  echo "5 12 38 91 L38";;
    v46132bk) echo "20 47 172 168 L172";;
    *) die "unknown variant: $1 (known: v46130k v46131k v46132bk)";;
  esac
}

# files_ok LIST DIR: the Lean files under DIR are exactly those of LIST
files_ok() {
  local have want
  have="$( (cd "$2" 2> /dev/null && ls ./*.lean Superperm8/*.lean 2> /dev/null) | wc -l | tr -d ' ')"
  want="$(wc -l < "$1" | tr -d ' ')"
  [ "$have" = "$want" ] && "$PYTHON" "$ROOT/tools/check_hashes.py" "$1" "$2" < /dev/null > /dev/null 2>&1
}

# make_sources VARIANT SRC: write the sources of the variant into SRC.  The hand-written files are written
# anew on every run (it takes seconds, and Lean compiles a module again only if its text has changed).  The
# parts of the search are kept if they agree with generated.sha256; otherwise tools/plan.py writes them.
make_sources() {
  local v="$1" src="$2" new="$2.new" f esc
  rm -rf "$new"
  mkdir -p "$new/Superperm8"
  while read -r _ f; do                                   # his files, with LF line ends
    tr -d '\r' < "$ECHOLS_DIR/$f" > "$new/$f"
  done < "$HERE/echols-sources.sha256"
  rm -f "$new/Superperm8/AffineSound.lean" "$new/Superperm8/AffineCheck.lean"
  patch -s -p1 --no-backup-if-mismatch -d "$new" < "$HERE/variants/$v/changes.diff" \
    || die "variants/$v/changes.diff does not apply to the files of $ECHOLS_DIR"
  cp "$HERE"/kernel/Superperm8/K*.lean "$new/Superperm8/"
  cp "$HERE/variants/$v/Plain.lean" "$new/Plain.lean"
  files_ok "$HERE/variants/$v/files.sha256" "$new" \
    || die "the files in $new differ from variants/$v/files.sha256"
  esc="$(printf '%s' "$ATTRIBUTION" | sed 's/[\\&|]/\\&/g')"
  grep -l '@ATTRIBUTION@' "$new"/*.lean "$new"/Superperm8/*.lean | while read -r f; do
    sed -i "s|@ATTRIBUTION@|$esc|g" "$f"
  done
  if "$PYTHON" "$ROOT/tools/check_hashes.py" "$HERE/variants/$v/generated.sha256" "$src" \
       < /dev/null > /dev/null 2>&1; then
    while read -r _ f; do mv "$src/$f" "$new/$f"; done < "$HERE/variants/$v/generated.sha256"
  else
    # shellcheck disable=SC2046
    "$PYTHON" "$HERE/tools/plan.py" $(search_of "$v") "$new/Superperm8" < /dev/null > "$BUILD/logs/plan.log" 2>&1 \
      || die "tools/plan.py failed, see $BUILD/logs/plan.log"
    check_hashes "$HERE/variants/$v/generated.sha256" "$new"
  fi
  rm -rf "$src"
  mv "$new" "$src"
}

check_tools
command -v patch > /dev/null 2>&1 || die "the program patch is not installed"
[ -f "$ECHOLS_DIR/Superperm8/Main.lean" ] \
  || die "no Superperm8/Main.lean in $ECHOLS_DIR (set ECHOLS_DIR to a checkout of Echols's repository)"
check_hashes "$HERE/echols-sources.sha256" "$ECHOLS_DIR"
echo "Echols's sources agree with echols-sources.sha256"

for v in $VARIANTS; do
  search_of "$v" > /dev/null
  BUILD="$BUILD_ROOT/$v"
  SRC="$BUILD/src"
  mkdir -p "$BUILD/logs"
  echo "== $v: 1. sources"
  make_sources "$v" "$SRC"
  echo "$v: $(wc -l < "$HERE/variants/$v/files.sha256" | tr -d ' ') Lean files as in variants/$v/files.sha256," \
    "$(wc -l < "$HERE/variants/$v/generated.sha256" | tr -d ' ') parts of the search as in generated.sha256"
  echo "== $v: 2. Lean"
  build_modules Solution Plain AxiomAudit -- "$SRC"
  echo "== $v: 3. axioms"
  print_axioms Plain AxiomAudit
  axiom_summary
  OTHER="$(axiom_lines "$BUILD"/logs/*.log | grep "depends on axioms" | grep -v -E "$STANDARD")"
  [ -z "$OTHER" ] || die "$v: an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
  LINES="$(axiom_lines "$BUILD"/logs/*.log | wc -l | tr -d ' ')"
  echo "$v: no axiom other than propext, Classical.choice, Quot.sound in the $LINES lines of this variant"
done
echo "== done: $(date '+%F %T')"
