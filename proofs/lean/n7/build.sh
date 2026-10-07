#!/bin/bash
# Build the proof that a superpermutation on 7 symbols has at least 5,899 letters.
#
#     ./build.sh           the default level: everything but the long evaluations
#     ./build.sh full      the same, then the 13 long evaluations, the final theorem and its audit
#
# The script works in the build directory of ../words/build.sh and ../lower/build.sh.  What those scripts
# have compiled (the two lower-bound libraries, the bridge, the files of ../lower) is not compiled again; what
# is missing is compiled here, so the script can also be run alone.
#
#   1. The Lean files that the final theorem is compiled from (60 here, 17 of ../lower, 2 of ../words) are
#      compared with the list of hashes sources.sha256, and the sources of the two libraries and Challenge.lean
#      with their lists.
#   2. The engine.  One Lean process compiles LowerBounds/PSearch.lean (a file with no imports) and writes
#      it as C as well; the C compiler of the Lean toolchain (leanc) makes a shared library of that C file:
#      $BUILD_DIR/native/PSearch.dll, .so or .dylib.
#   3. Level 1 of the proof, the proof that the engine is complete, and the kernel tests.  Nothing here uses
#      native_decide: LowerBounds/*.lean except the files *Native.lean, and Audit5899.lean,
#      Audit5899Search.lean, AuditN.lean.  JOBS_BIG processes at a time; LowerBounds/PArith.lean is compiled
#      by itself, and so is LowerBounds/PSmall6Search.lean, a kernel evaluation on 6 symbols that is
#      compiled at the level "full" only (TEST6): these two need the most memory.
#   4. LowerBounds/PTestNative.lean: 27 small searches evaluated by native_decide with the library loaded,
#      among them searches that the kernel evaluates in step 3 and searches whose answer is "true".
#   5. The evaluations: the modules of evaluations.txt, each one Lean process that loads the library
#      (--load-dynlib) and proves its equations by native_decide.  The default level runs the four short
#      ones (9 of the 22 equations), "full" all 17.  Several run at the same time, within JOBS threads in
#      all: a module gets the threads that the running ones leave idle (measured by their CPU time through
#      /proc; without /proc one module runs at a time with JOBS threads).  A module that has finished is not
#      run again; what a module costs is written to $BUILD_DIR/evaluations.log.
#   6. At the level "full": LowerBounds/PFinalNative.lean (the theorem) and Audit5899Native.lean.
#   7. The "#print axioms" lines are printed.  The script fails unless
#        every statement of step 3 depends on propext, Classical.choice, Quot.sound only,
#        every equation NAME of steps 4 and 5 depends on propext and on its own axiom
#          NAME._native.native_decide.ax_1_1 only,
#        and, at the level "full", covers_lower_bound_7_native depends on exactly the three standard
#          axioms and the 22 axioms of the equations named in evaluations.txt.
#
# Settings (environment variables; default after the colon).  LEAN, PYTHON, PANTONE_DIR, MATHLIB_PACKAGES,
# LEAN_THREADS and MINFREE_GB are described in ../tools/common.sh.
#   BUILD_DIR         the build directory: ../build/words
#   LEANC             the C compiler front end of the Lean toolchain: leanc next to $LEAN, or "leanc"
#   JOBS              threads of the evaluations of steps 4 and 5, all processes together: 1
#   JOBS_BIG          Lean processes at the same time in steps 3 and 6: 1
#   MINFREE_BIG_GB    PArith and PSmall6Search are started only while this many GB are free: $MINFREE_GB
#   TEST6             1: compile PSmall6Search as well: 1 at the level "full", else 0
#   HUNTER_DIR        a checkout of github.com/urdvr/superpermutations-hunter: ../deps/superpermutations-hunter
#   PREIMAGE_DIR      a checkout of github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds:
#                     ../deps/superpermutations-preimage-chain-lower-bounds
#   CHECK_SOURCES     1: stop if a source differs from the lists of hashes of step 1: 1
#
# Memory: most files of steps 3 and 6 import all of Mathlib (about 3.3 GB of working set, 8 GB committed).
# PArith needs 5.8 GB of working set and commits 10.7 GB; PSmall6Search needs 7.3 GB or more.  An evaluation
# needs little.  To stop: Ctrl-C, or create the file STOP in the build directory (no new process is started;
# a running evaluation may still take an hour).  README.md has the measured times.

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../tools/common.sh"
BUILD="${BUILD_DIR:-$ROOT/build/words}"
NATIVE="$BUILD/native"
: "${HUNTER_DIR:=$ROOT/deps/superpermutations-hunter}"
: "${PREIMAGE_DIR:=$ROOT/deps/superpermutations-preimage-chain-lower-bounds}"
: "${JOBS_BIG:=1}"
: "${MINFREE_BIG_GB:=$MINFREE_GB}"
: "${CHECK_SOURCES:=1}"
PHASE="${1:-default}"
case "$PHASE" in default | full) ;; *) die "usage: build.sh [full]" ;; esac
if [ "$PHASE" = full ]; then : "${TEST6:=1}"; else : "${TEST6:=0}"; fi
if [ -z "${LEANC:-}" ]; then
  case "$LEAN" in */*) LEANC="$(dirname "$LEAN")/leanc" ;; *) LEANC=leanc ;; esac
fi
case "$(uname -s)" in
  MINGW* | MSYS* | CYGWIN*) LIB="$NATIVE/PSearch.dll"; PIC="" ;;
  Darwin) LIB="$NATIVE/PSearch.dylib"; PIC="-fPIC" ;;
  *) LIB="$NATIVE/PSearch.so"; PIC="-fPIC" ;;
esac
STANDARD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
SOURCES=("$HERE" "$ROOT/lower" "$ROOT/words" "$PANTONE_DIR" "$HUNTER_DIR" "$PREIMAGE_DIR")

# The modules of evaluations.txt: those of this level, and the names of all 22 equations.
EVALS=""
NAMES=""
while read -r mod level names; do
  case "$mod" in "" | "#"*) continue ;; esac
  NAMES="$NAMES $names"
  if [ "$level" = default ] || [ "$PHASE" = full ]; then EVALS="$EVALS LowerBounds.$mod"; fi
done < "$HERE/evaluations.txt"

# The modules of step 3: every file of LowerBounds/ that is not an evaluation, and the audits of level 1.
PLAIN=""
for f in "$HERE"/LowerBounds/*.lean; do
  case "$(basename "$f" .lean)" in
    *Native) ;;
    PSmall6Search) ;;
    *) PLAIN="$PLAIN LowerBounds.$(basename "$f" .lean)" ;;
  esac
done
PLAIN="$PLAIN Audit5899 Audit5899Search AuditN"

file_hashes() {   # FILE...: SHA-256 and name of each file
  "$PYTHON" -c "
import hashlib, os, sys
for f in sys.argv[1:]:
    print('  ' + hashlib.sha256(open(f, 'rb').read()).hexdigest() + '  ' + os.path.basename(f))" "$@" < /dev/null
}

stamp_of() {   # MODULE: its stamp (../tools/order.py); the evaluations and the engine import files of this part only
  "$PYTHON" "$ROOT/tools/order.py" "$1" -- "$HERE" < /dev/null | awk -F'\t' -v m="$1" '$2 == m { print $5 }'
}

# build_engine: step 2.  One Lean run writes PSearch.olean and PSearch.c, so both come from the same source.
build_engine() {
  local mod=LowerBounds.PSearch out="$BUILD/lib/LowerBounds/PSearch" stamp t0 secs
  stamp="$(stamp_of $mod)"
  [ -n "$stamp" ] || die "tools/order.py gave no stamp for $mod"
  if [ -f "$out.olean" ] && [ -f "$LIB" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] \
       && [ "$(cat "$NATIVE/PSearch.stamp" 2> /dev/null)" = "$stamp" ]; then
    echo "PSearch and its library are up to date"
  else
    mkdir -p "$BUILD/lib/LowerBounds" "$NATIVE"
    rm -f "$out.stamp" "$NATIVE/PSearch.stamp" "$LIB"
    t0=$(date +%s)
    (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS=1 nice -n 19 "$LEAN" "--root=$(native "$HERE")" \
       -o "$(native "$out.olean")" -i "$(native "$out.ilean")" -c "$(native "$NATIVE/PSearch.c")" \
       "$(native "$HERE/LowerBounds/PSearch.lean")") < /dev/null > "$BUILD/logs/$mod.log" 2>&1 \
      || die "Lean failed on PSearch.lean, see $BUILD/logs/$mod.log"
    secs=$(( $(date +%s) - t0 ))
    echo "  compiled $mod to PSearch.olean and PSearch.c ($secs s)"
    t0=$(date +%s)
    # shellcheck disable=SC2086
    (cd "$ROOT" && nice -n 19 "$LEANC" -shared -O3 $PIC -o "$(native "$LIB")" "$(native "$NATIVE/PSearch.c")") \
      < /dev/null > "$BUILD/logs/leanc.PSearch.log" 2>&1 \
      || die "$LEANC failed on PSearch.c, see $BUILD/logs/leanc.PSearch.log (set LEANC)"
    [ -f "$LIB" ] || die "$LEANC wrote no $LIB"
    echo "  $LEANC made $(basename "$LIB") ($(( $(date +%s) - t0 )) s)"
    echo "$stamp" > "$out.stamp"
    echo "$stamp" > "$NATIVE/PSearch.stamp"
    echo "$(date '+%F %T') ok $secs s $mod" >> "$BUILD/build.log"
  fi
  file_hashes "$HERE/LowerBounds/PSearch.lean" "$NATIVE/PSearch.c" "$LIB"
}

# cpu_ticks PID: the CPU time that a process has used, in clock ticks; nothing on a system without /proc
cpu_ticks() { awk '{ print $14 + $15 }' "/proc/$1/stat" 2> /dev/null; }
TICKS="$(getconf CLK_TCK 2> /dev/null || echo 100)"

# end_eval MODULE EXIT STAMP START THREADS TICKS: what is written when the Lean process of a module has ended
end_eval() {
  local mod="$1" out="$BUILD/lib/${1//.//}" secs=$(( $(date +%s) - $4 )) cpu="$(( $6 / TICKS )) s"
  [ -r /proc/self/stat ] || cpu="unknown"
  if [ "$2" = 0 ] && [ -f "$out.olean" ]; then
    echo "$3" > "$out.stamp"
    echo "$(date '+%F %T') ok $secs s $mod" >> "$BUILD/build.log"
    echo "  evaluated $mod ($secs s with $5 threads, CPU time $cpu)"
  else
    rm -f "$out.olean" "$out.ilean"
    echo "$(date '+%F %T') FAILED $secs s $mod" >> "$BUILD/build.log"
    echo "  FAILED $mod (exit $2), see $BUILD/logs/$mod.log"
    echo "$mod" >> "$FAILED_FILE"
  fi
  printf '%s\t%s\texit %s\t%s s\t%s threads\tCPU time %s\n' "$(date '+%F %T')" "$mod" "$2" "$secs" "$5" \
    "$cpu" >> "$BUILD/evaluations.log"
}

# evaluate MODULE...: steps 4 and 5.  Each module is one Lean process with the library loaded.  A new one is
# started with the threads that the running ones do not use; a process younger than 30 seconds counts with
# all its threads.  The CPU time written at the end is the one seen at the last look, up to 10 s early.
evaluate() {
  local mod out stamp now tick=0 last=0 busy free use c i n need=$(( (JOBS + 2) / 3 )) qi=0
  local Q_MOD=() Q_STAMP=() R_PID=() R_MOD=() R_STAMP=() R_THR=() R_T0=() R_CPU=() K
  FAILED_FILE="$BUILD/failed.$$.txt"
  rm -f "$FAILED_FILE"
  for mod in "$@"; do
    out="$BUILD/lib/${mod//.//}"
    stamp="$(stamp_of "$mod")"
    [ -n "$stamp" ] || die "tools/order.py gave no stamp for $mod"
    [ -f "$out.olean" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] && continue
    Q_MOD+=("$mod"); Q_STAMP+=("$stamp")
  done
  echo "$# modules, ${#Q_MOD[@]} to evaluate, within $JOBS threads"
  trap '[ "${#R_PID[@]}" -gt 0 ] && kill "${R_PID[@]}" 2> /dev/null; exit 130' INT TERM
  while [ "$qi" -lt "${#Q_MOD[@]}" ] || [ "${#R_PID[@]}" -gt 0 ]; do
    now=$(date +%s); busy=0; n=${#R_PID[@]}; K=()
    for ((i = 0; i < n; i++)); do
      if kill -0 "${R_PID[i]}" 2> /dev/null; then
        c="$(cpu_ticks "${R_PID[i]}")"
        use=$(( R_THR[i] * 1000 ))                        # in thousandths of a thread
        if [ -n "$c" ] && [ $(( now - R_T0[i] )) -ge 30 ] && [ "$now" -gt "$tick" ]; then
          use=$(( (c - R_CPU[i]) * 1000 / TICKS / (now - tick) ))
          [ "$use" -gt $(( R_THR[i] * 1000 )) ] && use=$(( R_THR[i] * 1000 ))
        fi
        [ -n "$c" ] && R_CPU[i]="$c"
        busy=$(( busy + use )); K+=("$i")
      else
        wait "${R_PID[i]}"
        end_eval "${R_MOD[i]}" $? "${R_STAMP[i]}" "${R_T0[i]}" "${R_THR[i]}" "${R_CPU[i]}"
      fi
    done
    if [ "${#K[@]}" -lt "$n" ]; then                      # drop the processes that have ended
      local P=() M=() S=() T=() Z=() U=()
      for i in "${K[@]}"; do
        P+=("${R_PID[i]}"); M+=("${R_MOD[i]}"); S+=("${R_STAMP[i]}"); T+=("${R_THR[i]}"); Z+=("${R_T0[i]}")
        U+=("${R_CPU[i]}")
      done
      R_PID=("${P[@]}"); R_MOD=("${M[@]}"); R_STAMP=("${S[@]}"); R_THR=("${T[@]}"); R_T0=("${Z[@]}")
      R_CPU=("${U[@]}")
    fi
    tick=$now
    if [ -e "$FAILED_FILE" ] || [ -e "$BUILD/STOP" ]; then
      [ "${#R_PID[@]}" -eq 0 ] && break
      sleep 10; continue
    fi
    free=$(( JOBS - (busy + 999) / 1000 ))
    [ "${#R_PID[@]}" -eq 0 ] && free=$JOBS
    if [ "$qi" -lt "${#Q_MOD[@]}" ] && [ "$free" -ge "$need" ] && [ "$free" -ge 1 ] \
         && { [ "${#R_PID[@]}" -eq 0 ] || [ $(( now - last )) -ge 30 ]; }; then
      mod="${Q_MOD[qi]}"; out="$BUILD/lib/${mod//.//}"
      rm -f "$out.stamp"
      (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS="$free" exec nice -n 19 "$LEAN" -j "$free" \
         "--load-dynlib=$(native "$LIB")" "--root=$(native "$HERE")" \
         -o "$(native "$out.olean")" -i "$(native "$out.ilean")" \
         "$(native "$HERE/${mod//.//}.lean")") < /dev/null > "$BUILD/logs/$mod.log" 2>&1 &
      R_PID+=("$!"); R_MOD+=("$mod"); R_STAMP+=("${Q_STAMP[qi]}"); R_THR+=("$free"); R_T0+=("$now")
      R_CPU+=(0)
      echo "  started $mod with $free threads ($(date '+%T'))"
      last=$now; qi=$(( qi + 1 ))
      continue
    fi
    sleep 10
  done
  trap - INT TERM
  if [ -e "$FAILED_FILE" ]; then
    echo "failed: $(tr '\n' ' ' < "$FAILED_FILE")"
    echo "first lines of the log of $(head -1 "$FAILED_FILE"):"
    head -20 "$BUILD/logs/$(head -1 "$FAILED_FILE").log" | cut -c1-300
    rm -f "$FAILED_FILE"
    exit 1
  fi
  if [ -e "$BUILD/STOP" ]; then
    echo "stopped by the file $BUILD/STOP (remove it and run the script again to continue)"
    exit 2
  fi
}

# not_own_axiom: the "#print axioms" lines that are NOT of the form
#   'S' depends on axioms: [propext, S._native.native_decide.ax_1_1]
not_own_axiom() {
  awk '{ s = $1; gsub(/\047/, "", s)
         if ($0 != "\047" s "\047 depends on axioms: [propext, " s "._native.native_decide.ax_1_1]") print }'
}

# axiom_names: the axioms named in "#print axioms" lines, one per line, without the namespace of this project
axiom_names() {
  grep "depends on axioms" | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' \
    | sed 's/^ *//; s/^SuperpermLowerBounds\.//' | sort -u
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
  check_hashes "$HERE/sources.sha256" "$ROOT"
  check_hashes "$ROOT/words/hunter-sources.sha256" "$HUNTER_DIR"
  check_hashes "$ROOT/words/preimage-sources.sha256" "$PREIMAGE_DIR"
  grep "  Challenge.lean$" "$ROOT/constant/pantone-sources.sha256" > "$BUILD/hashes_challenge.txt"
  check_hashes "$BUILD/hashes_challenge.txt" "$PANTONE_DIR"
  echo "the Lean files of this proof, the sources of both libraries and Challenge.lean agree with the lists" \
    "of hashes"
fi

echo "== 2. the engine and its library"
build_engine

echo "== 3. level 1, the completeness of the engine, the kernel tests"
JOBS="$JOBS_BIG" build_modules LowerBounds.PModel LowerBounds.PTables -- "${SOURCES[@]}"
JOBS=1 MINFREE_GB="$MINFREE_BIG_GB" build_modules LowerBounds.PArith -- "${SOURCES[@]}"
# shellcheck disable=SC2086
JOBS="$JOBS_BIG" build_modules $PLAIN -- "${SOURCES[@]}"
if [ "$TEST6" = 1 ]; then
  JOBS=1 MINFREE_GB="$MINFREE_BIG_GB" build_modules LowerBounds.PSmall6Search -- "${SOURCES[@]}"
  PLAIN="$PLAIN LowerBounds.PSmall6Search"
fi

echo "== 4. the compiled search against the kernel and against known answers"
evaluate LowerBounds.PTestNative

echo "== 5. the evaluations ($PHASE level)"
# shellcheck disable=SC2086
evaluate $EVALS

FINAL=""
if [ "$PHASE" = full ]; then
  echo "== 6. the theorem"
  FINAL="LowerBounds.PFinalNative Audit5899Native"
  # shellcheck disable=SC2086
  JOBS="$JOBS_BIG" build_modules $FINAL -- "${SOURCES[@]}"
fi

echo "== 7. axioms of the statements"
# shellcheck disable=SC2086
print_axioms $PLAIN LowerBounds.PTestNative $EVALS $FINAL
# shellcheck disable=SC2086
OTHER="$(print_axioms $PLAIN | grep "depends on axioms" | grep -v -E "$STANDARD")"
[ -z "$OTHER" ] || die "a statement of step 3 with an axiom other than propext, Classical.choice, Quot.sound:
$OTHER"
# shellcheck disable=SC2086
OTHER="$(print_axioms LowerBounds.PTestNative $EVALS | not_own_axiom)"
[ -z "$OTHER" ] || die "an evaluated equation that depends on more than propext and its own axiom:
$OTHER"
# shellcheck disable=SC2086
echo "$(print_axioms $PLAIN | wc -l | tr -d ' ') statements with no axiom other than propext," \
  "Classical.choice, Quot.sound;" \
  "$(print_axioms LowerBounds.PTestNative $EVALS | wc -l | tr -d ' ') evaluated equations, each with" \
  "propext and its own axiom"
if [ "$PHASE" = full ]; then
  WANT="$( { printf '%s\n' propext Classical.choice Quot.sound
             for n in $NAMES; do echo "PS.$n._native.native_decide.ax_1_1"; done; } | sort -u)"
  for mod in $FINAL; do
    GOT="$(print_axioms "$mod" | grep "covers_lower_bound_7_native' depends on axioms" | axiom_names)"
    [ "$GOT" = "$WANT" ] || die "$mod: the axioms of covers_lower_bound_7_native are not exactly propext,
Classical.choice, Quot.sound and the 22 axioms of the equations of evaluations.txt:
$GOT"
  done
  # shellcheck disable=SC2086
  OTHER="$(print_axioms $FINAL | axiom_names | grep -v -x -F "$WANT")"
  [ -z "$OTHER" ] || die "a statement of step 6 with an axiom outside that list:
$OTHER"
  echo "covers_lower_bound_7_native depends on propext, Classical.choice, Quot.sound and on the" \
    "$(echo $NAMES | wc -w | tr -d ' ') axioms of the evaluated equations, and on nothing else"
fi
echo "== all \"#print axioms\" lines in the build directory, counted by the list of axioms"
axiom_summary | cut -c1-160
echo "== done ($PHASE): $(date '+%F %T')"
