#!/bin/bash
# rounds.sh - rounds of search, each followed by the deterministic passes.
#
# A round is: a search with trailsearch_gpu for SEARCH_SEC seconds from the best plan, then on its result the
# fixed-order pass (recut), the loop moves (loopscan) followed by the fixed-order pass again, the relocation
# (relocate) and the segment insertion (segins).  Every word is checked with delcheck, and only the best stays on
# disk.  DIR/best.txt holds "LENGTH PLAN WORD", DIR/steps.log one line per step.
# A loop of this kind (search, fixed-order pass, loop moves) took my n = 12 word from 522,745,530 to 522,745,464; the
# relocation and the segment insertion were added to it later.  When its rounds find nothing more, the passes alone
# (polish.sh) and then kick.sh take over.
#
# usage: rounds.sh DIR BASE PLAN0 ROUNDS SEARCH_SEC THREADS SEED0 "SEARCH_OPTS" CO_FIRST [DELCHECK_THREADS=4]
#   SEARCH_OPTS: options of the search; several sets separated by | are used in turn, for example
#     "--kmax 14 --T0 0.6 --focus 0.8 --sync 120 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --coit 2000 --co-skip|--kmax 12 --T0 0.4 --focus 0.85 --sync 120 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --coit 2000 --co-skip"
#   CO_FIRST = 1: the fixed-order pass and the loop moves run once on PLAN0 before the first round.
# What I used: n = 12  rounds.sh DIR BASE PLAN 12 1200 4 SEED "OPTS" 1          (20-minute rounds)
#              n = 13  rounds.sh DIR BASE PLAN 6 3600 4 SEED "OPTS with --coit 200000 --sync 300" 1   (one process: 11 to 13 GB)
# Environment: TOOLS = directory of the binaries and of kern.ptx (default: the directory of this script); GPU = 1
# (default) or 0 (search on the CPU path); LOOPS, DPA, OR3 = 0 switches that pass off; LSOPT, LSTHR, LSTIME,
# DPATHR, DPATIME, DPAOPT, OR3OPT (default "--or3 3 --or3-slack 0"), OR3TIME, CKPT (default 120); LOOPFIRST,
# DPAFIRST = 1 runs that pass once before the first round.
T=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
[ $# -ge 9 ] || { sed -n '2,22p' "$0"; exit 1; }
DIR=$1; BASE=$2; PLAN=$3; ROUNDS=$4; SEC=$5; THR=$6; SEED=$7; OPTS=$8; COFIRST=$9; DT=${10:-4}
GOPT="--gpu --ptx $T/kern.ptx"; [ "${GPU:-1}" = 1 ] || GOPT=""
IFS="|" read -r -a OPTV <<< "$OPTS"
mkdir -p "$DIR"; LOG=$DIR/steps.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a "$LOG"; }
best_len=999999999999; best_word=""; last_co=""
len_of() { grep -o 'wrote .* length [0-9]*' "$1" | tail -1 | grep -o '[0-9]*$'; }
check() { "$T/delcheck" "$1" "$DT" > "$1.delcheck.json" 2>&1; grep -q '"missing_permutations":0' "$1.delcheck.json"; }
keep() {   # word plan length
  if [ "$3" -lt "$best_len" ]; then
    [ -n "$best_word" ] && [ "$best_word" != "$1" ] && rm -f "$best_word"
    best_len=$3; best_word=$1; PLAN=$2; echo "$3 $2 $1" > "$DIR/best.txt"; say "BEST $3 (plan $2)"
  else
    [ "$1" != "$best_word" ] && rm -f "$1"
  fi
}
co_pass() {   # tag plan: the fixed-order pass
  if [ -n "$last_co" ] && cmp -s "$2" "$last_co"; then say "co $1: plan unchanged, skipped"; return; fi
  OMP_NUM_THREADS=$DT nice -n 19 "$T/recut" "$BASE" "$DIR/c$1.txt" --plan-in "$2" --co-skip --time 0 > "$DIR/c$1.log" 2>&1
  L=$(len_of "$DIR/c$1.log")
  if [ -n "$L" ] && check "$DIR/c$1.txt"; then
    say "co $1: length $L valid"; last_co=$DIR/c$1.txt.plan; keep "$DIR/c$1.txt" "$DIR/c$1.txt.plan" "$L"
  else
    say "co $1: FAILED or invalid (length '$L')"; rm -f "$DIR/c$1.txt"
  fi
}
loop_pass() {   # tag: loop moves on the best plan, then the fixed-order pass on the result
  [ "${LOOPS:-1}" = 1 ] || return
  timeout "${LSTIME:-1800}" nice -n 19 "$T/loopscan" "$BASE" --plan "$PLAN" --only PABD --nogap1 --threads "${LSTHR:-4}" ${LSOPT:---quiet --greedy --neutral --nbatch 16 --maxrounds 40} --planout "$DIR/l$1.txt.plan" --out "$DIR/l$1.txt" > "$DIR/l$1.log" 2>&1
  L=$(len_of "$DIR/l$1.log")
  if [ -n "$L" ] && [ "$L" -lt "$best_len" ] && check "$DIR/l$1.txt"; then
    say "loop $1: length $L valid"
    keep "$DIR/l$1.txt" "$DIR/l$1.txt.plan" "$L"
    co_pass "${1}b" "$PLAN"
  else
    say "loop $1: no gain (length '$L')"; rm -f "$DIR/l$1.txt" "$DIR/l$1.txt.plan"
  fi
}
dpa_pass() {   # tag: relocation on the best plan
  [ "${DPA:-1}" = 1 ] || return
  OMP_NUM_THREADS=${DPATHR:-4} timeout "${DPATIME:-3600}" nice -n 19 "$T/relocate" "$BASE" "$DIR/d$1.txt" --plan-in "$PLAN" --threads 1 --time 0 --dpa --dpa-thr "${DPATHR:-4}" ${DPAOPT:-} > "$DIR/d$1.log" 2>&1
  L=$(len_of "$DIR/d$1.log")
  if [ -n "$L" ] && [ "$L" -lt "$best_len" ] && check "$DIR/d$1.txt"; then
    say "dpa $1: length $L valid"; cp "$DIR/d$1.txt.plan" "$DIR/d$1.keep.plan"
    keep "$DIR/d$1.txt" "$DIR/d$1.keep.plan" "$L"
  else
    say "dpa $1: no gain (length '$L')"; rm -f "$DIR/d$1.txt"
  fi
}
or3_pass() {   # tag: segment insertion on the best plan
  [ "${OR3:-1}" = 1 ] || return
  OMP_NUM_THREADS=$THR timeout "${OR3TIME:-2700}" nice -n 19 "$T/segins" "$BASE" "$DIR/s$1.txt" --plan-in "$PLAN" --time 0 --threads "$THR" ${OR3OPT:---or3 3 --or3-slack 0} > "$DIR/s$1.log" 2>&1
  L=$(len_of "$DIR/s$1.log")
  if [ -n "$L" ] && [ "$L" -lt "$best_len" ] && check "$DIR/s$1.txt"; then
    say "or3 $1: length $L valid"; cp "$DIR/s$1.txt.plan" "$DIR/s$1.keep.plan"
    keep "$DIR/s$1.txt" "$DIR/s$1.keep.plan" "$L"
  else
    say "or3 $1: no gain (length '$L')"; rm -f "$DIR/s$1.txt"
  fi
}
say "start: base $BASE plan $PLAN rounds $ROUNDS x ${SEC}s threads $THR opts '$OPTS'"
[ "$COFIRST" = 1 ] && co_pass 0 "$PLAN"
{ [ "$COFIRST" = 1 ] || [ "${LOOPFIRST:-0}" = 1 ]; } && loop_pass 0
[ "${DPAFIRST:-0}" = 1 ] && dpa_pass 0
for r in $(seq 1 "$ROUNDS"); do
  O=${OPTV[$(( (r - 1) % ${#OPTV[@]} ))]}
  OMP_NUM_THREADS=$THR nice -n 19 "$T/trailsearch_gpu" "$BASE" "$DIR/r$r.txt" --plan-in "$PLAN" --time "$SEC" --seed $((SEED + r)) --threads "$THR" $O --ckpt "${CKPT:-120}" $GOPT > "$DIR/r$r.log" 2> "$DIR/r$r.err"
  L=$(len_of "$DIR/r$r.log")
  if [ -n "$L" ] && check "$DIR/r$r.txt"; then
    say "search $r ($O): length $L valid; $(grep -o 'LNS done: [0-9]* iterations' "$DIR/r$r.log")"
    cp "$DIR/r$r.txt.plan" "$DIR/r$r.keep.plan"
    keep "$DIR/r$r.txt" "$DIR/r$r.keep.plan" "$L"
    co_pass "$r" "$DIR/r$r.keep.plan"
    loop_pass "$r"
    dpa_pass "$r"
    or3_pass "$r"
  else
    say "search $r: FAILED or invalid (length '$L'): $(tail -1 "$DIR/r$r.log" | cut -c1-120) | $(tail -1 "$DIR/r$r.err" | cut -c1-160)"; rm -f "$DIR/r$r.txt"
  fi
done
say "done: best $best_len"
