#!/bin/bash
# Check one word: from a word file to the Lean theorem that it is a superpermutation.
#
#     ./check_word.sh WORDFILE [--jobs N] [--minfree GB] [--out DIR] [--yes]
#
# WORDFILE       the word, one symbol per character, as .txt or .txt.xz; white space at the ends is ignored.
#                The symbols are ranked in ASCII order, so any 2 to 16 different characters will do.
# --jobs N       Lean processes at the same time (default 1)
# --minfree GB   start a Lean process only while this many GB of memory are free (default 0: no check)
# --out DIR      the build directory (default ../build/check-n-L: n symbols, L letters).  Nothing is
#                written anywhere else.
# --yes          needed for a run whose estimate is above 30 minutes of Lean time
#
# The steps.  The command stops at the first step that fails, says which one, and returns a code other
# than 0.  It returns 0 only if every step passed.
#   1. Read the word: the number of symbols n, the length L, the SHA-256 of the uncompressed file.
#   2. Choose the method.  word_info.py looks at the word; nothing is generated before this.
#        every rotation class is visited in one stretch and 8 <= n <= 11:   gen11.py  (Superperm/Cyc.lean)
#        the same and n = 12:                         gen12.py  (Cyc.lean with TreeOk.lean, Cyc2.lean, Cyc3.lean)
#        otherwise, if n <= 10 and every permutation occurs:                gen.py    (Superperm/Literal.lean)
#        otherwise the command stops and says why.
#   3. Print an estimate of Lean time, disk and memory.
#   4. Generate the certificate into the build directory and let Lean check it.
#   5. Write the statement for this word, Checked_n_L.lean: HasWord n L, the same statement written out with
#      no definition of this project, and "#print axioms".  Compile it.  The axioms must be exactly
#      propext, Classical.choice, Quot.sound.
#   6. Check that the numbers in the Lean files spell the word file, with a script that shares no code with
#      the generator.
#   7. Print a summary.
#
# A run can be interrupted and started again with the same command: what is compiled is kept.
# The file STOP in the build directory stops a run after the modules that are being compiled.
#
# What the theorem says: some list over Fin n with exactly L letters contains every list of n different
# letters as a contiguous part.  Only the letters of the word are checked.  How the word was made plays no
# part, and neither does any plan or structure behind it, except that the fast methods need every rotation
# class in one stretch.
#
# Settings besides the options: LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES, LEAN_THREADS, see
# ../tools/common.sh.  gen11.py, gen12.py and word_info.py need numpy.

WORD=""; YES=0; OUT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --jobs)    JOBS="$2"; shift 2;;
    --minfree) MINFREE_GB="$2"; shift 2;;
    --out)     OUT="$2"; shift 2;;
    --yes)     YES=1; shift;;
    -h|--help) sed -n '2,13p' "$0"; exit 0;;
    -*)        echo "unknown option: $1" >&2; exit 64;;
    *)         WORD="$1"; shift;;
  esac
done
[ -n "$WORD" ] || { sed -n '2,13p' "$0"; exit 64; }

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
T_START=$(date +%s)
fail() { echo "FAILED at step $1: $2" >&2; exit 1; }
# lean_step STEP MESSAGE TARGET: compile TARGET and what it imports; a stop by the file STOP is not a failure
lean_step() {
  ( build_modules "$3" -- "$HERE" "$GEN" "$PANTONE_DIR" )
  case $? in
    0) ;;
    2) echo "stopped; run the same command again to continue"; exit 2;;
    *) fail "$1" "$2";;
  esac
}

echo "== 1. the word"
[ -f "$WORD" ] || fail 1 "no such file: $WORD"
check_tools
INFO="$("$PYTHON" "$HERE/word_info.py" "$WORD" < /dev/null)" || fail 1 "word_info.py could not read $WORD"
get() { printf '%s\n' "$INFO" | tr -d '\r' | sed -n "s/^$1=//p"; }
K=$(get symbols); L=$(get letters); SHA=$(get sha256)
CLASSES=$(get classes); FULL=$(get classes_full); PERMS=$(get permutations)
echo "$WORD"
echo "n = $K symbols, L = $L letters, SHA-256 of the uncompressed file: $SHA"

echo "== 2. the method"
{ [ "$K" -ge 2 ] && [ "$K" -le 16 ]; } || fail 2 "the word has $K different symbols; the checkers read 2 to 16"
KFACT=1; for i in $(seq 2 "$K"); do KFACT=$((KFACT * i)); done
if [ "$FULL" = "$CLASSES" ] && [ "$K" -ge 13 ]; then
  fail 2 "n = $K is out of reach for this design.  For n = 13 it would take about 60 hours of Lean time for
the 479 million rotation classes and about 11 GB of generated Lean files, and every Lean process would have to
load the whole word, about 6.7 GB of compiled blocks."
elif [ "$FULL" = "$CLASSES" ] && [ "$K" -eq 12 ]; then
  METHOD=cyc12; GENERATOR=gen12.py; VERIFIER=verify_blocks12.py; OPTIONS="--depth 16 --bpf 512 --gpf 8 --fast"
  echo "every one of the $CLASSES rotation classes is visited in one stretch: gen12.py, one table entry for"
  echo "every rotation class, with the changes for this size (TreeOk.lean, Cyc2.lean, Cyc3.lean)"
elif [ "$FULL" = "$CLASSES" ] && [ "$K" -ge 8 ]; then
  METHOD=cyc; GENERATOR=gen11.py; VERIFIER=verify_blocks.py; OPTIONS=""
  [ "$K" -eq 9 ] && OPTIONS="--depth 6 --bpf 16"
  [ "$K" -eq 11 ] && OPTIONS="--depth 12"
  echo "every one of the $CLASSES rotation classes is visited in one stretch: gen11.py, one table entry for"
  echo "every rotation class (Cyc.lean)"
elif [ "$K" -le 10 ]; then
  [ "$PERMS" = "$KFACT" ] \
    || fail 2 "the word is not a superpermutation: $PERMS of the $KFACT permutations of its $K symbols occur in it"
  METHOD=general; GENERATOR=gen.py; VERIFIER=verify_word.py; OPTIONS=""
  if [ "$FULL" = "$CLASSES" ]; then
    echo "n = $K is below the 8 symbols that the method with rotation classes needs:"
  else
    echo "only $FULL of the $CLASSES rotation classes are visited in one stretch:"
  fi
  echo "gen.py, one table entry for every permutation (Literal.lean)"
else
  fail 2 "only $FULL of the $CLASSES rotation classes are visited in one stretch.  For n >= 11 the only method
here needs all of them; one table entry for every permutation is not feasible at this size.  The word may
still be a superpermutation; this command cannot check it."
fi

echo "== 3. the estimate"
# Lean time in minutes with one process, disk of the build directory, memory of one Lean process, as
# measured on a Ryzen 9 5950X (see README.md)
case "$METHOD-$K" in
  cyc-8)      MINUTES=2;   DISK="5 MB";   MEMORY="1 GB";;
  cyc-9)      MINUTES=3;   DISK="5 MB";   MEMORY="1 GB";;
  cyc-10)     MINUTES=9;   DISK="20 MB";  MEMORY="1 GB";;
  cyc-11)     MINUTES=80;  DISK="0.2 GB"; MEMORY="1 GB (2 GB for one module)";;
  cyc12-12)   MINUTES=360; DISK="2.1 GB"; MEMORY="1.3 GB (1.8 GB for one module)";;
  general-10) MINUTES=75;  DISK="0.1 GB"; MEMORY="1.1 GB";;
  general-9)  MINUTES=6;   DISK="10 MB";  MEMORY="1 GB";;
  *)          MINUTES=2;   DISK="5 MB";   MEMORY="1 GB";;
esac
echo "Lean time: about $MINUTES min (divide by the number of processes, now $JOBS)"
echo "disk: $DISK; memory of one Lean process: $MEMORY"
if [ "$MINUTES" -gt 30 ] && [ "$YES" != 1 ]; then
  echo "this is a long run: start it again with --yes"
  exit 3
fi

echo "== 4. the certificate"
BUILD="${OUT:-$ROOT/build/check-$K-$L}"
GEN="$BUILD/gen"
NAME="N$K"
MARK="$GEN/Superperm/$NAME.from"
mkdir -p "$BUILD/logs" "$GEN/Superperm"
echo "build directory: $BUILD"
if [ "$(cat "$MARK" 2> /dev/null)" != "$SHA $GENERATOR $OPTIONS" ]; then
  rm -f "$MARK"
  # shellcheck disable=SC2086
  "$PYTHON" "$HERE/$GENERATOR" "$WORD" "$NAME" $OPTIONS --source "n=$K, $L letters: $(basename "$WORD")." \
    --out "$GEN" < /dev/null > "$BUILD/logs/gen_$NAME.log" 2>&1 \
    || fail 4 "$GENERATOR did not accept the word, see $BUILD/logs/gen_$NAME.log"
  echo "$SHA $GENERATOR $OPTIONS" > "$MARK"
  echo "$GENERATOR wrote $(ls "$GEN/Superperm/$NAME" | wc -l | tr -d ' ') files into $GEN/Superperm/$NAME"
else
  echo "the certificate in $GEN/Superperm/$NAME was generated from this word before; it is used as it is"
fi
lean_step 4 "Lean did not accept the certificate, see the messages above and $BUILD/logs" "Superperm.$NAME.Main"

echo "== 5. the statement for this word"
STATEMENT="Checked_${K}_${L}"
cat > "$GEN/$STATEMENT.lean" << EOF
import Superperm.$NAME.Main

/-!
Written by check_word.sh for the word file $(basename "$WORD"):
$K symbols, $L letters, SHA-256 of the uncompressed file $SHA.
-/

open SuperpermutationBounds

namespace $STATEMENT

/-- A superpermutation on $K symbols with $L letters, in the words of Pantone's \`Challenge.lean\`. -/
theorem hasWord : HasWord $K $L := LiteralSuperperm.$NAME.hasWord

/-- The same with no definition of this project: a list over \`Fin $K\` of exactly $L letters in which
every list of $K different letters occurs as a contiguous part. -/
theorem written_out : exists w : List (Fin $K),
    (forall p : List (Fin $K), p.length = $K -> p.Nodup -> exists u v : List (Fin $K), w = u ++ p ++ v) /\\
      w.length = $L :=
  Exists.intro LiteralSuperperm.$NAME.word
    (And.intro LiteralSuperperm.$NAME.word_covers LiteralSuperperm.$NAME.word_length)

end $STATEMENT

#print axioms $STATEMENT.hasWord
#print axioms $STATEMENT.written_out
EOF
lean_step 5 "Lean did not accept $GEN/$STATEMENT.lean, see $BUILD/logs/$STATEMENT.log" "$STATEMENT"
AXIOMS="$(axiom_lines "$BUILD/logs/$STATEMENT.log")"
WANT=": [propext, Classical.choice, Quot.sound]"
[ "$(printf '%s\n' "$AXIOMS" | grep -c "depends on axioms")" = 2 ] \
  || fail 5 "expected two \"#print axioms\" lines in $BUILD/logs/$STATEMENT.log"
[ "$(printf '%s\n' "$AXIOMS" | grep -c -F "depends on axioms$WANT")" = 2 ] \
  || fail 5 "the axioms are not exactly propext, Classical.choice, Quot.sound:
$AXIOMS"
printf '%s\n' "$AXIOMS"

echo "== 6. the Lean files against the word file"
"$PYTHON" "$HERE/$VERIFIER" "$NAME" "$WORD" "$GEN" < /dev/null \
  || fail 6 "$VERIFIER: the numbers in $GEN/Superperm/$NAME do not spell $WORD"

echo "== 7. summary"
echo "proven: HasWord $K $L"
echo "  a list over Fin $K of exactly $L letters contains every list of $K different letters as a contiguous part"
echo "axioms: propext, Classical.choice, Quot.sound"
echo "word:   $WORD"
echo "        SHA-256 of the uncompressed file $SHA"
echo "method: $GENERATOR $OPTIONS"
echo "time:   $(( ($(date +%s) - T_START) / 60 )) min $(( ($(date +%s) - T_START) % 60 )) s for this run"
echo "files:  $GEN/$STATEMENT.lean (the statement), $GEN/Superperm/$NAME (the certificate),"
echo "        $BUILD/lib (compiled), $BUILD/logs, $BUILD/build.log"
