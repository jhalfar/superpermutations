# Shared settings and functions of constant/build.sh and words/build.sh.
# This file is read by those scripts (". tools/common.sh"); it starts nothing by itself.
#
# Settings (environment variables; the value after the colon is the default):
#   LEAN              the Lean binary: lean
#                     (with elan, "lean" run inside this directory is the version named in lean-toolchain)
#   PYTHON            Python 3: python3
#   PANTONE_DIR       a checkout of github.com/jaypantone/superperm-upper-43-80 in which Mathlib has been
#                     fetched (lake exe cache get): deps/superperm-upper-43-80
#   MATHLIB_PACKAGES  the directory with the compiled Mathlib and the packages it needs:
#                     $PANTONE_DIR/.lake/packages
#   JOBS              how many Lean processes run at the same time: 1
#   LEAN_THREADS      threads of one Lean process: 1
#   MINFREE_GB        a Lean process is started only while this many GB of memory are free; 0 = no check: 0
#
# The calling script sets BUILD (the build directory) before it calls build_modules.
#   $BUILD/lib        compiled modules (.olean, .ilean) and, next to each, a .stamp file
#   $BUILD/logs       what Lean printed for each module (the "#print axioms" lines are in there)
#   $BUILD/build.log  one line per compiled module: date, result, seconds, module
# To stop a build: create the file $BUILD/STOP.  Running processes finish, no new one starts.
# To continue: run the same script again.  A module is compiled again only if its source or something it
# imports has changed (see tools/order.py).

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${LEAN:=lean}"
: "${PYTHON:=python3}"
: "${PANTONE_DIR:=$ROOT/deps/superperm-upper-43-80}"
: "${MATHLIB_PACKAGES:=$PANTONE_DIR/.lake/packages}"
: "${JOBS:=1}"
: "${LEAN_THREADS:=1}"
: "${MINFREE_GB:=0}"

die() { echo "error: $*" >&2; exit 1; }

# Lean on Windows wants paths with a drive letter and a search path separated by ";".
if command -v cygpath > /dev/null 2>&1; then
  native() { cygpath -m "$1"; }
  PATH_SEP=";"
else
  native() { printf '%s' "$1"; }
  PATH_SEP=":"
fi

# Free memory in GB (Linux and Git Bash for Windows; elsewhere the check is skipped).
free_gb() {
  if [ -r /proc/meminfo ]; then
    awk '/^MemAvailable:/ {a = $2} /^MemFree:/ {f = $2} END {print int((a ? a : f) / 1048576)}' /proc/meminfo
  else
    echo 1000000
  fi
}

# Stop early with a clear message if Lean, Mathlib or the checkout of Pantone's repository is missing.
check_tools() {
  local want
  want="$(sed 's/.*:v//' "$ROOT/lean-toolchain" | tr -d '\r\n')"
  (cd "$ROOT" && "$LEAN" --version 2> /dev/null) | grep -q "version $want" \
    || die "\"$LEAN --version\" does not report Lean $want (set LEAN to the binary of that version)"
  "$PYTHON" -c "import sys; sys.exit(sys.version_info < (3, 8))" 2> /dev/null \
    || die "\"$PYTHON\" is not Python 3.8 or newer (set PYTHON)"
  [ -f "$PANTONE_DIR/Challenge.lean" ] \
    || die "no Challenge.lean in $PANTONE_DIR (set PANTONE_DIR to a checkout of Pantone's repository)"
  [ -f "$MATHLIB_PACKAGES/mathlib/.lake/build/lib/lean/Mathlib.olean" ] \
    || die "no compiled Mathlib under $MATHLIB_PACKAGES (run \"lake exe cache get\" in $PANTONE_DIR)"
}

# The search path of Lean: the compiled Mathlib packages and our own build directory.  Compiled modules of
# Pantone's project are NOT on it: what we need of his library is compiled here from his sources.
set_lean_path() {
  local d
  LEAN_SEARCH="$(native "$BUILD/lib")"
  for d in "$MATHLIB_PACKAGES"/*/.lake/build/lib/lean; do
    [ -d "$d" ] && LEAN_SEARCH="$LEAN_SEARCH$PATH_SEP$(native "$d")"
  done
}

# compile_one MODULE ROOT SOURCE STAMP: one Lean process.  The output goes to $BUILD/lib, what Lean prints
# to $BUILD/logs/MODULE.log.  The stamp is written only after success, so an interrupted module is redone.
compile_one() {
  local mod="$1" root="$2" src="$3" stamp="$4"
  local out="$BUILD/lib/${mod//.//}" log="$BUILD/logs/$mod.log" t0 secs
  mkdir -p "$(dirname "$out")"
  rm -f "$out.stamp"
  t0=$(date +%s)
  if (cd "$ROOT" && LEAN_PATH="$LEAN_SEARCH" LEAN_NUM_THREADS="$LEAN_THREADS" nice -n 19 "$LEAN" \
        "--root=$(native "$root")" -o "$(native "$out.olean")" -i "$(native "$out.ilean")" \
        "$(native "$src")") < /dev/null > "$log" 2>&1; then
    secs=$(( $(date +%s) - t0 ))
    echo "$stamp" > "$out.stamp"
    echo "$(date '+%F %T') ok $secs s $mod" >> "$BUILD/build.log"
    echo "  compiled $mod ($secs s)"
  else
    secs=$(( $(date +%s) - t0 ))
    rm -f "$out.olean" "$out.ilean"
    echo "$(date '+%F %T') FAILED $secs s $mod" >> "$BUILD/build.log"
    echo "  FAILED $mod, see $log"
    echo "$mod" >> "$FAILED_FILE"
  fi
}

# build_modules TARGET... -- ROOT...
# Compiles the target modules and every module under the roots that they import, in dependency order
# (tools/order.py), JOBS processes at a time.  Modules that are up to date are skipped.
build_modules() {
  local list="$BUILD/order.$$.txt" level="" lv mod root src stamp out todo=0 n=0
  FAILED_FILE="$BUILD/failed.$$.txt"
  mkdir -p "$BUILD/lib" "$BUILD/logs"
  rm -f "$FAILED_FILE"
  set_lean_path
  "$PYTHON" "$ROOT/tools/order.py" "$@" < /dev/null > "$list" || die "tools/order.py failed"
  while IFS=$'\t' read -r lv mod root src stamp; do
    out="$BUILD/lib/${mod//.//}"
    [ -f "$out.olean" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] || todo=$((todo + 1))
  done < "$list"
  echo "$(wc -l < "$list" | tr -d ' ') modules, $todo to compile, $JOBS at a time"
  while IFS=$'\t' read -r lv mod root src stamp; do
    out="$BUILD/lib/${mod//.//}"
    [ -f "$out.olean" ] && [ "$(cat "$out.stamp" 2> /dev/null)" = "$stamp" ] && continue
    if [ "$lv" != "$level" ]; then wait; level="$lv"; fi      # a level is finished before the next starts
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 1; done
    while [ "$(free_gb)" -lt "$MINFREE_GB" ] && [ ! -e "$BUILD/STOP" ]; do sleep 20; done
    [ -e "$FAILED_FILE" ] && break
    [ -e "$BUILD/STOP" ] && break
    compile_one "$mod" "$root" "$src" "$stamp" &
  done < "$list"
  wait
  rm -f "$list"
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

# axiom_lines FILE...: what "#print axioms" printed into these logs, one statement per line.  Lean breaks a
# long list of axioms over several lines; they are joined here, so that no axiom can hide on a later line.
axiom_lines() {
  cat "$@" | awk '
    /does not depend on any axioms/ { print; next }
    /depends on axioms:/            { buf = $0; if ($0 ~ /\]$/) { print buf; buf = "" }; next }
    buf != ""                       { sub(/^ +/, " "); buf = buf $0; if ($0 ~ /\]$/) { print buf; buf = "" } }'
}

# print_axioms MODULE...: the "#print axioms" lines that Lean printed when it compiled these modules.
print_axioms() {
  local mod
  for mod in "$@"; do
    axiom_lines "$BUILD/logs/$mod.log"
  done
}

# axiom_summary: every "#print axioms" line of the whole build, counted by its list of axioms.  A build of
# this directory must show the three lists [propext], [propext, Quot.sound] and
# [propext, Classical.choice, Quot.sound] (or no axioms) and nothing else.
axiom_summary() {
  axiom_lines "$BUILD"/logs/*.log \
    | sed "s/.*depends on axioms: //; s/.*does not depend on any axioms/(no axioms)/" | sort | uniq -c
}

# check_hashes LIST DIR: the files named in LIST exist under DIR with the listed hashes (tools/check_hashes.py).
check_hashes() {
  "$PYTHON" "$ROOT/tools/check_hashes.py" "$1" "$2" < /dev/null || die "files under $2 differ from the list $1"
}
