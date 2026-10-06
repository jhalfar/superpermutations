#!/bin/bash
# Build the lower bounds of LowerBounds/ (Theorems A, B and C) and the two-sided statements that use them.
#
#     ./build.sh              the default level: Theorems A and B, and Theorem C with its small certificates
#     ./build.sh full         the same, and the large certificates of Theorem C (hours of Lean time)
#     ./build.sh generate     step 1 only (no Lean)
#
# Run ../words/build.sh first.  This script works in the same build directory, so what that script has
# compiled (the two lower-bound libraries, the bridge, the literal words) is not compiled again.
#
#   1. The certificates of Theorem C.  For each line of certificates.txt and of certificates-large.txt a
#      generator (tools/s_plan.py or tools/s_plan2.py) runs the finite search of that certificate and writes it
#      as Lean files, cut into lemmas that the kernel can evaluate.  Then tools/s_certs.py and tools/s_final.py
#      write the files that state the results, once for the small certificates (LowerBounds/SCertWSmall.lean,
#      SCertificatesSmall.lean, SFinalSmall.lean) and once for all (SCertW.lean, SCertificates.lean,
#      SFinal.lean), and with each a file that prints the axioms of every statement (AxCertSmall.lean,
#      AxSFinalSmall.lean, AxCert.lean, AxSFinal.lean).  All of this goes into the build directory
#      ($BUILD_DIR/sgen; about a minute) and is compared, file by file, with the list of hashes
#      generated.sha256.  Both levels generate everything; they differ in what Lean compiles.
#   2. Lean evaluates the searches of the level: LowerBounds/SGen/* and the four small files they import.
#      These modules need no Mathlib; JOBS of them run at the same time.
#   3. Lean compiles everything else, JOBS_BIG at a time.  What is built is whatever is found here; a file
#      added later needs no change of this script:
#        LowerBounds/*.lean   the lower bounds.  They need the two lower-bound libraries and
#                             ../words/Superperm/Bridge.lean.
#        the generated files that state the results of step 1
#        Audit*.lean          the same statements written out with no definition of this project.
#        Superperm/*.lean     two-sided statements: a lower bound of LowerBounds/ with a literal word of
#                             ../words.  They need the certificates that ../words/build.sh generates; without
#                             them these files are left out.
#      At the default level the files that rest on the large certificates are left out: the generated
#      SCertW, SCertificates, SFinal, AxCert, AxSFinal, and every file of the last two kinds that imports one
#      of them.
#   4. The "#print axioms" lines of these files are printed.  The script fails if any of them names an axiom
#      other than propext, Classical.choice, Quot.sound.
#
# Run alone, into an empty build directory, the script compiles what it needs of the two libraries and the
# bridge itself (150 modules, about an hour) and leaves out the two-sided statements.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# JOBS, LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR        the build directory: ../build/words
#   HUNTER_DIR       a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR     a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                    ../deps/superpermutations-preimage-chain-lower-bounds
#   JOBS_BIG         Lean processes at the same time in step 3: 1
#   CHECK_SOURCES    1: stop if the sources of the two libraries differ from the lists of hashes
#                    ../words/hunter-sources.sha256 and ../words/preimage-sources.sha256: 1
#   CHECK_GENERATED  1: stop if the files of step 1 differ from generated.sha256.  Set it to 0 after a change
#                    of a list of certificates: 1
#
# Memory: a process of step 2 needs up to 3.5 GB.  Every file of step 3 imports all of Mathlib: one Lean
# process needs about 4 GB, and it is slow unless the Mathlib files stay in the file cache (keep 6 GB free).
# README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
GEN="$BUILD/gen"
SGEN="$BUILD/sgen"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${CHECK_SOURCES:=1}"
: "${CHECK_GENERATED:=1}"
PHASE="${1:-default}"
case "$PHASE" in default | full | generate) ;; *) die "usage: build.sh [full | generate]" ;; esac
export PYTHONDONTWRITEBYTECODE=1          # Python writes nothing next to the generators
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'

# names_of LIST: the names of the certificates of a list; the line "GENERATOR k cn bn q ..." is
# C<k>_<cn>_<bn>_<q>.
names_of() {
  local g k cn bn q _
  while read -r g k cn bn q _; do
    case "$g" in "" | "#"*) continue ;; esac
    printf ' C%s_%s_%s_%s' "$k" "$cn" "$bn" "$q"
  done < "$1"
}
SMALL="$(names_of "$HERE/certificates.txt")"
LARGE="$(names_of "$HERE/certificates-large.txt")"

# generated_ok: the Lean files under $SGEN are exactly those of generated.sha256
generated_ok() {
  local have want
  have="$(find "$SGEN" -name '*.lean' 2> /dev/null | wc -l | tr -d ' ')"
  want="$(wc -l < "$HERE/generated.sha256" | tr -d ' ')"
  [ "$have" = "$want" ] \
    && "$PYTHON" "$ROOT/tools/check_hashes.py" "$HERE/generated.sha256" "$SGEN" < /dev/null > /dev/null 2>&1
}

# generate_one GENERATOR k cn bn q OPTIONS...: one certificate.  The generator works in $SGEN, where it finds
# a copy of itself; what it prints (the size of the search, the files written) goes to s_plan_<NAME>.log.
generate_one() {
  local g="$1" k="$2" cn="$3" bn="$4" q="$5" name="C${2}_${3}_${4}_${5}" t0
  shift 5
  t0=$(date +%s)
  if (cd "$SGEN" && nice -n 19 "$PYTHON" "$g" "$k" "$cn" "$bn" "$q" "$name" "$@") \
       < /dev/null > "$SGEN/s_plan_$name.log" 2>&1; then
    echo "generated $(date '+%F %T')" > "$SGEN/s_gen_$name.log"
    echo "  generated $name ($(( $(date +%s) - t0 )) s)"
  else
    echo "  FAILED $name, see $SGEN/s_plan_$name.log"
    echo "$name" >> "$SGEN/failed.txt"
  fi
}

# make_certificates: step 1.  A certificate whose generator has finished (s_gen_<NAME>.log) is not made again.
make_certificates() {
  local list g k cn bn q opts
  mkdir -p "$SGEN/LowerBounds"
  cp "$HERE"/tools/s_*.py "$SGEN/"
  rm -f "$SGEN/failed.txt"
  for list in "$HERE/certificates.txt" "$HERE/certificates-large.txt"; do
    while read -r g k cn bn q opts; do
      case "$g" in "" | "#"*) continue ;; esac
      [ -f "$SGEN/s_gen_C${k}_${cn}_${bn}_${q}.log" ] && continue
      while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 1; done
      [ -e "$BUILD/STOP" ] && break
      # shellcheck disable=SC2086
      generate_one "$g" "$k" "$cn" "$bn" "$q" $opts &
    done < "$list"
  done
  wait
  [ ! -e "$SGEN/failed.txt" ] || die "a generator failed for: $(tr '\n' ' ' < "$SGEN/failed.txt")"
  if [ -e "$BUILD/STOP" ]; then
    echo "stopped by the file $BUILD/STOP (remove it and run the script again to continue)"
    exit 2
  fi
  # the files that state the results: for the small certificates, then for all
  # shellcheck disable=SC2086
  (cd "$SGEN" \
     && "$PYTHON" s_certs.py --force --suffix=Small $SMALL \
     && "$PYTHON" s_final.py --out SFinalSmall --certs SCertificatesSmall --suffix _small $SMALL \
     && "$PYTHON" s_certs.py --force $SMALL $LARGE \
     && "$PYTHON" s_final.py $SMALL $LARGE) < /dev/null > "$SGEN/s_statements.log" 2>&1 \
    || die "tools/s_certs.py or tools/s_final.py failed, see $SGEN/s_statements.log"
  mv "$SGEN"/s_proto/Ax*.lean "$SGEN/"
  rmdir "$SGEN/s_proto"
}

# needs_large FILE: the file imports a statement file that rests on all the certificates
needs_large() {
  grep -q -E '^import LowerBounds\.(SCertW|SCertificates|SFinal)[[:space:]]*$' "$1"
}

check_tools
mkdir -p "$BUILD/logs" "$GEN"

echo "== 1. the certificates of Theorem C"
if [ "$CHECK_GENERATED" = 1 ] && generated_ok; then
  :
else
  make_certificates
  if [ "$CHECK_GENERATED" = 1 ] && ! generated_ok; then
    "$PYTHON" "$ROOT/tools/check_hashes.py" "$HERE/generated.sha256" "$SGEN" < /dev/null
    die "the Lean files under $SGEN are not the files of generated.sha256 (after a change of a list of
certificates: delete $SGEN and run with CHECK_GENERATED=0)"
  fi
fi
NFILES="$(find "$SGEN" -name '*.lean' | wc -l | tr -d ' ')"
# shellcheck disable=SC2086
echo "$(echo $SMALL | wc -w | tr -d ' ') small and $(echo $LARGE | wc -w | tr -d ' ') large certificates," \
  "$NFILES Lean files in $SGEN"
[ "$CHECK_GENERATED" = 1 ] && echo "they agree with generated.sha256"
[ "$PHASE" = generate ] && exit 0

[ -f "$HUNTER_DIR/Hunter/Bounds.lean" ] || die "no Hunter/Bounds.lean in $HUNTER_DIR (set HUNTER_DIR)"
[ -f "$PREIMAGE_DIR/PreimageChain/PathwiseFinalCore.lean" ] \
  || die "no PreimageChain/PathwiseFinalCore.lean in $PREIMAGE_DIR (set PREIMAGE_DIR)"
if [ "$CHECK_SOURCES" = 1 ]; then
  check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
  check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  echo "the sources of both libraries agree with the lists of hashes"
fi

echo "== 2. Lean, the searches ($PHASE level)"
CERTS="$SMALL"
[ "$PHASE" = full ] && CERTS="$SMALL $LARGE"
LIGHT="LowerBounds.SRun"
for n in $CERTS; do LIGHT="$LIGHT LowerBounds.SGen.$n"; done
# shellcheck disable=SC2086
build_modules $LIGHT -- "$HERE" "$SGEN"

# The module names of the files found here: LowerBounds/X.lean is the module LowerBounds.X, and so on.
TARGETS=""
LEFT=""
for f in "$HERE"/LowerBounds/*.lean; do TARGETS="$TARGETS LowerBounds.$(basename "$f" .lean)"; done
TARGETS="$TARGETS LowerBounds.SCertWSmall LowerBounds.SCertificatesSmall LowerBounds.SFinalSmall"
TARGETS="$TARGETS AxCertSmall AxSFinalSmall"
if [ "$PHASE" = full ]; then
  TARGETS="$TARGETS LowerBounds.SCertW LowerBounds.SCertificates LowerBounds.SFinal AxCert AxSFinal"
fi
for f in "$HERE"/Audit*.lean; do
  if [ "$PHASE" != full ] && needs_large "$f"; then LEFT="$LEFT $(basename "$f")"; continue; fi
  TARGETS="$TARGETS $(basename "$f" .lean)"
done
if [ -f "$GEN/Superperm/N11/Main.lean" ]; then
  for f in "$HERE"/Superperm/*.lean; do
    if [ "$PHASE" != full ] && needs_large "$f"; then LEFT="$LEFT Superperm/$(basename "$f")"; continue; fi
    TARGETS="$TARGETS Superperm.$(basename "$f" .lean)"
  done
else
  echo "no certificates in $GEN (run ../words/build.sh first): the two-sided statements are left out"
fi
[ -z "$LEFT" ] || echo "left out at the default level (these need the large certificates):$LEFT"

echo "== 3. Lean, everything else"
# shellcheck disable=SC2086
JOBS="$JOBS_BIG" build_modules $TARGETS -- \
  "$HERE" "$SGEN" "$ROOT/words" "$GEN" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR"

echo "== 4. axioms of the statements"
# shellcheck disable=SC2086
print_axioms $TARGETS
# shellcheck disable=SC2086
OTHER="$(print_axioms $TARGETS | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
# shellcheck disable=SC2086
NLINES="$(print_axioms $TARGETS | wc -l | tr -d ' ')"
echo "no axiom other than propext, Classical.choice, Quot.sound in these $NLINES lines"
echo "== all \"#print axioms\" lines in the build directory, counted by the list of axioms"
axiom_summary
echo "== done: $(date '+%F %T')"
