#!/bin/bash
# test.sh - run the scripts of this folder on the pieces of the reproduction package and compare what they print with
# the numbers of the README.
#
# usage:   bash test.sh REPRO [WORK]
#   REPRO    the folder of the reproduction package: selections/n10-selection.txt, selections/n11-selection.txt,
#            tools/geng.py, tools/gen12.py, and its plans (plan/n10-*.plan, plan/n11-*.plan)
#   WORK     directory for everything that is written (default: test_work in the current directory)
# What runs is chosen by variables:
#   (nothing)        n = 10 and n = 11 without a solver: base words, the checks, the bounds on the n = 10 pieces,
#                    the chains of n = 10.  About 5 minutes, 0.5 GB.
#   GUROBI=1         also the steps that need the solver: the chained plans at n = 11, the plans of gen13.py,
#                    order13.py and plan13n.py at n = 11, one partition of the n = 10 programme when its tables
#                    exist.  About 1 minute more.
#   RECUT=FILE       the fixed-order pass of tools/ (recut, built).  With it the chained plan of n = 11 is made
#                    exactly as in the README and its SHA-256 is compared.
#   SLOW=1           the tables of the n = 10 programme (about 40 minutes, 1.7 GB); with GUROBI=1 then the
#                    programme for partition 2 and the plan of the n = 10 word.
#   BIG=1            the n = 12 chain on the transported selection: file of cuts, symmetry, joins, run systems,
#                    block programme, bound, list of vertices.  About 20 minutes more, 2.75 GB, 2 GB of disk; needs
#                    a C compiler (CC, default gcc); the run systems need GUROBI=1, the plan built from one needs
#                    RECUT.
#   PY=python3       the interpreter (default: python)
# Not run here: anything at n = 13, cert11.py (3.8 GB, 40 minutes), liftmip.py.
# A line "NOTE" is not a failure: it marks a result that depends on which of several optimal solutions the solver
# returned.  needs: bash, Python 3, numpy, scipy; sha256sum; the rest as chosen above.
set -u
export PYTHONDONTWRITEBYTECODE=1        # leave no __pycache__ next to the scripts
REPRO=${1:?usage: bash test.sh REPRO [WORK]}
WORK=${2:-test_work}
PY=${PY:-python}
CC=${CC:-gcc}
HERE=$(cd "$(dirname "$0")" && pwd)
REPRO=$(cd "$REPRO" && pwd) || exit 2
mkdir -p "$WORK" || exit 2
WORK=$(cd "$WORK" && pwd)
if [ -n "${RECUT:-}" ]; then RECUT=$(cd "$(dirname "$RECUT")" && pwd)/$(basename "$RECUT"); fi
PLANS=$REPRO/plan
[ -d "$PLANS" ] || PLANS=$REPRO/plans
# gen12.py and geng.py are imported by some scripts
if command -v cygpath > /dev/null 2>&1; then
    export PYTHONPATH="$(cygpath -w "$REPRO/tools")"
else
    export PYTHONPATH="$REPRO/tools"
fi
npass=0; nfail=0; nnote=0

ok()   { npass=$((npass + 1)); echo "PASS  $*"; }
bad()  { nfail=$((nfail + 1)); echo "FAIL  $*"; }
note() { nnote=$((nnote + 1)); echo "NOTE  $*"; }
# run NAME "TEXT THAT MUST APPEAR" command...      (the output goes to WORK/NAME.log)
run() {
    local name=$1 want=$2
    shift 2
    if "$@" > "$WORK/$name.log" 2>&1 && grep -q -F -- "$want" "$WORK/$name.log"; then
        ok "$name: $want"
    else
        bad "$name (see $WORK/$name.log; expected: $want)"
    fi
}
# sha NAME FILE EXPECTED
sha() {
    local got
    got=$(sha256sum "$2" 2> /dev/null | cut -c1-64)
    if [ "$got" = "$3" ]; then ok "$1  $got"; else bad "$1: SHA-256 ${got:-no file}, expected $3"; fi
}
# shanote NAME FILE EXPECTED: the same for a file that depends on the solver's choice among optimal solutions
shanote() {
    local got
    got=$(sha256sum "$2" 2> /dev/null | cut -c1-64)
    if [ "$got" = "$3" ]; then
        ok "$1  $got"
    else
        note "$1: SHA-256 ${got:-no file}; mine was $3 (another optimal solution of the solver gives another file)"
    fi
}
# pplan BASE.tsv BASE.txt OUT: the plan that writes every piece of a base word as it is
pplan() {
    "$PY" -c "
import sys
n = sum(1 for l in open(sys.argv[1]) if l.strip())
w = open(sys.argv[2], 'rb').read().strip()
sym = '0123456789ABCDEF'.index(chr(max(w[:4096]))) + 1
head = 'TRAILSEARCH-PLAN %d %d %d\n' % (sym, len(w), n)
open(sys.argv[3], 'w', newline='\n').write(head + ''.join('P %d\n' % k for k in range(n)))" "$1" "$2" "$3"
}

B10=0ccfcddc26ed6a3268d38dabd8398c308cdf3a14e0d957c88fa554c9ecbd48c3     # base word of the n = 10 pieces
B11=9bcb862f56592583c4e4f34e9c7d366e2c3753be98b08d3ce1877ecec02a4e84     # base word of the n = 11 pieces
C11=0feeeb14e2d9de6795f25509303a003d95263bbd534fcd0625593769b57feab3     # chained plan of n = 11
P10=6ced8b2589feda32fadc6cfd9701b02d8c50df492acd79cffec74214e33cda02     # plan of the n = 10 word (4,034,855)
C12T=a3d836f3583674fad4272947c12824bbe5b598a0dafdf9df07b21fa780dc1371    # chained plan, transported selection, n = 12
V12T=b7e4e973d4ba67a01898db6f7b039e9ab6744b5c71a637fa0d2484fab7db8fef    # list of vertices for the lift
S12T=12cfdcf10eb417101e86056522287b3483400cb960e5e98ff0c79b0b8c47c7a3    # data lines of data/n12t-selection.txt.xz

cd "$WORK" || exit 1
echo "== n = 10: pieces, checks, bounds, chains"
run geng10 "trails 350" "$PY" "$REPRO/tools/geng.py" "$REPRO/selections/n10-selection.txt" n10-base.txt --table n10-base.tsv
sha "base word of n = 10" n10-base.txt $B10
run verify10 "193/360" "$PY" "$HERE/verify.py" "$REPRO/selections/n10-selection.txt"
run gen12_10 "trails 350" "$PY" "$REPRO/tools/gen12.py" "$REPRO/selections/n10-selection.txt" n10-base-b.txt --table n10-base-b.tsv
run cmptrails10 "identical as sets of cyclic words: True" "$PY" "$HERE/cmptrails.py" n10-base.txt n10-base-b.txt 10
run gt10 "group 47" "$PY" "$HERE/gt.py" n10-base.txt gt10m.npz
run cert10_single "length >= 4034848" "$PY" "$HERE/cert10.py" n10-base.txt gt10m.npz --a 2 --cap 2
run cert10_multi "big trails single-port, narrow, A = 1, cap = 2: 4 cost >= 1920 + 12 = 1932  ->  2 cost >= 966, cost >= 483, length >= 4034842" \
    "$PY" "$HERE/cert10.py" n10-base.txt gt10m.npz --a 1 --cap 2 --multi
run t_minplus10 "0 differences in 2250 comparisons" "$PY" "$HERE/t_minplus.py" n10-base.txt
run trav10 "directed 6-cycles of traversals at W = 8: 56; traversals on cycles 336" "$PY" "$HERE/trav10.py" n10-base.txt gt10m.npz
run parts10 "partitions of the 48 groups into 8 of the 56 chains: 56" "$PY" "$HERE/parts10.py"
for p in "$PLANS"/n10-*.plan; do
    [ -f "$p" ] || continue
    L=$(basename "$p" .plan | sed 's/.*-//')
    run plancost10 "length $L = h + sum R" "$PY" "$HERE/plancost.py" n10-base.txt n10-base.tsv "$p"
done
if [ "${SLOW:-0}" = 1 ]; then
    run chain10_tables "tables written" "$PY" "$HERE/chain10.py" tables n10-base.txt gt10m.npz
fi
if [ "${GUROBI:-0}" = 1 ] && [ -f c10m_tab.npz ]; then
    run chain10_solve "partition  2 (254004 variables): 2 cost 992 (status 2, bound 992)" "$PY" "$HERE/chain10.py" solve 2 --verify
    run chain10_verify "PRUNED blocks with reduced cost below the gap: 0" cat chain10_solve.log
    run plans10 "exact 2 cost 992, length 4034855" "$PY" "$HERE/plans10.py" c10m_sol_2.pkl n10-base.txt gt10m.npz
    shanote "plan of the n = 10 word" plan10m_p2_4034855.plan $P10
fi

echo "== n = 11: pieces, links, cuts, start plans"
run geng11 "trails 800" "$PY" "$REPRO/tools/geng.py" "$REPRO/selections/n11-selection.txt" n11-base.txt --table n11-base.tsv
sha "base word of n = 11" n11-base.txt $B11
run linkcheck11 "(all openings): 651; pairs of loops consecutive in an F-orbit: 651; the two sets are equal: True" \
    "$PY" "$HERE/linkcheck.py" n11-base.txt n11-base.tsv
for p in "$PLANS"/n11-*.plan; do
    [ -f "$p" ] || continue
    L=$(basename "$p" .plan | sed 's/.*-//')
    run plancost11 "length $L = h + sum R" "$PY" "$HERE/plancost.py" n11-base.txt n11-base.tsv "$p"
done
if "$CC" -O2 -o cuts12 "$HERE/cuts12.c" > cc_cuts12.log 2>&1; then
    run cuts11 "cuts 3668472 (plain D=0 363770, D=1 3265030; skip D=0 39672" ./cuts12 n11-base.txt n11-base.tsv cuts11.bin
    rm -f cuts11.bin
else
    note "no C compiler ($CC): cuts12.c and hop12.c are not tested"
fi
if [ "${GUROBI:-0}" = 1 ]; then
    pplan n11-base.tsv n11-base.txt n11-p.plan
    run chainplan11 "one F-orbit per loop: 522 (status 2, bound 522) -> 150 chains for 672 trails" \
        "$PY" "$HERE/chainplan.py" n11-base.txt n11-base.tsv n11-p.plan n11-chain-p.plan
    if [ -n "${RECUT:-}" ]; then
        run recut11 "length 43932949" "$RECUT" n11-base.txt n11-dp.txt --co-skip --time 0 --threads 1
        run chainplan11_recut "150 chains for 672 trails" "$PY" "$HERE/chainplan.py" n11-base.txt n11-base.tsv n11-dp.txt.plan n11-chain.plan
        tr -d '\r' < n11-chain.plan > n11-chain.lf.plan
        shanote "chained plan of n = 11" n11-chain.lf.plan $C11
        run plancost11_chain "length 43931105 = h + sum R + 1891" "$PY" "$HERE/plancost.py" n11-base.txt n11-base.tsv n11-chain.plan
    fi
    run plan13n_11 "plan: predicted model length 43930950" "$PY" "$HERE/plan13n.py" "$REPRO/selections/n11-selection.txt" n11-base.txt n11-base.tsv n11-plan13n.plan
    run plancost11_plan13n "length 43930950 = h + sum R" "$PY" "$HERE/plancost.py" n11-base.txt n11-base.tsv n11-plan13n.plan
    echo "== the 9-symbol selection transported once: pieces of n = 11 (gen13.py, order13.py)"
    run gen13_11 "plan: predicted model length 43930818" "$PY" "$HERE/gen13.py" "$REPRO/selections/n10-selection.txt" n11t-base.txt --table n11t-base.tsv --plan n11t-chain.plan
    run order13_11 "new plan: predicted model length 43930755" "$PY" "$HERE/order13.py" "$REPRO/selections/n10-selection.txt" n11t-base.txt n11t-base.tsv n11t-chain.plan n11t-order.plan
    run plancost11t "length 43930755 = h + sum R" "$PY" "$HERE/plancost.py" n11t-base.txt n11t-base.tsv n11t-order.plan
fi

if [ "${BIG:-0}" = 1 ]; then
    echo "== n = 12 on the transported selection"
    "$PY" -c "
import lzma, sys, hashlib
t = lzma.open(sys.argv[1], 'rb').read()
open('n12t-selection.txt', 'wb').write(t)
print(hashlib.sha256(b''.join(l + b'\n' for l in t.split(b'\n') if l.strip() and not l.startswith(b'#'))).hexdigest())" "$HERE/data/n12t-selection.txt.xz" > n12t-selection.sha
    if [ "$(cat n12t-selection.sha)" = "$S12T" ]; then ok "data lines of the selection  $S12T"; else bad "data lines of the selection: $(cat n12t-selection.sha)"; fi
    run verify12t "193/378" "$PY" "$HERE/verify.py" n12t-selection.txt
    run gen12_12t "base word 522789969 letters" "$PY" "$REPRO/tools/gen12.py" n12t-selection.txt n12t-base.txt --table n12t-base.tsv
    run cuts12t "cuts 40272960 (plain D=0 3628800, D=1 36288000; skip D=0 356160" ./cuts12 n12t-base.txt n12t-base.tsv cuts12c.bin
    run sym12 "that keep ALL small cuts: 168" "$PY" "$HERE/sym12.py"
    run attach12 "short-walk trails: in+out {4: 2016" "$PY" "$HERE/attach12.py"
    rm -f attach12.npz
    run smallpos "words agree with cuts12c.bin" "$PY" "$HERE/smallpos.py" n12t-base.txt n12t-base.tsv
    run prep_hop "first big cut 2678592" "$PY" "$HERE/prep_hop.py"
    if "$CC" -O2 -o hop12 "$HERE/hop12.c" > cc_hop12.log 2>&1; then
        ./hop12 cuts12c.bin 2678592 hop_src.i16 hop_snk.i16 hop_d.i16 hop_d.i16 19 5 > hop12_19.log 2> hop12_19.err
        if [ "$(tr -d '\r' < hop12_19.log | awk '$1 ~ /^[0-9]+$/ && $1 <= 18 { printf "%s ", $2 }')" = "16 16 20 24 28 32 36 40 44 44 50 54 60 64 66 70 74 76 " ]; then ok "hop12: block values for 1 to 18 big trails"; else bad "hop12: block values (see $WORK/hop12_19.log)"; fi
        run hop12_pot "FIXED POINT: mu = 7 / 2 per join; every block of k cuts: 2 * B_k >= 7 (k - 1) + 8 + 8" \
            ./hop12 cuts12c.bin 2678592 hop_src.i16 hop_snk.i16 hop_d.i16 hop_d.i16 300 5 --pot 7 2
    fi
    run bound12 "E = 12: 4 cost >= 46162 at R = 649 runs, 144 short-walk singles, 504 big sub-blocks in 504 connections  ->  cost >= 11541, length >= 522736830" \
        "$PY" "$HERE/bound12.py"
    run mkverts "wrote vertices.txt: 3282720 words" "$PY" "$HERE/mkverts.py" vertices.txt n12t-selection.txt
    sha "list of vertices" vertices.txt $V12T
    if [ "${GUROBI:-0}" = 1 ]; then
        run joins12 "usable at once (one cut per trail, no cycle): 3504 (status 2, bound 3504.0)" "$PY" "$HERE/joins12.py"
        run runs12 "2*6*6048 - 2*14112 = 44352" "$PY" "$HERE/runs12.py" 4 6
        run runs12_level4 "2*4*6048 - 2*7008 = 34368" cat runs12.log
        run q12 "E = 12: LPmax = 284.000 x 168 = 47712.0" "$PY" "$HERE/q12.py" 4 6 7 8 9 10 11 12
        for e in "E =  4: LPmax = 42.000" "E =  6: LPmax = 84.000" "E =  7: LPmax = 115.000" "E =  8: LPmax = 148.000" "E =  9: LPmax = 181.000" "E = 10: LPmax = 214.000" "E = 11: LPmax = 249.000"; do
            run q12_values "$e" cat q12.log
        done
        run q12b_8 "symmetric integer optimum 140.0 x 168 = 23520 (status 2, bound 140.0); runs 1344, cycles 0" "$PY" "$HERE/q12b.py" 8
        run q12b_10d0 "symmetric integer optimum 200.0 x 168 = 33600 (status 2, bound 200.0); runs 1008, cycles 0" "$PY" "$HERE/q12b.py" 10 --d0
        run q12b_12d0 "symmetric integer optimum 266.0 x 168 = 44688 (status 2, bound 266.0); runs 504, cycles 0" "$PY" "$HERE/q12b.py" 12 --d0
        if [ -n "${RECUT:-}" ]; then
            run recut12t "length 522761507" "$RECUT" n12t-base.txt n12t-dp.txt --co-skip --time 0 --threads 2
            rm -f n12t-dp.txt
            run chainplan12t "one F-orbit per loop: 3504 (status 2, bound 3504) -> 2544 chains for 6048 trails" \
                "$PY" "$HERE/chainplan.py" n12t-base.txt n12t-base.tsv n12t-dp.txt.plan n12t-chain.plan
            tr -d '\r' < n12t-chain.plan > n12t-chain.lf.plan
            shanote "chained plan, transported selection" n12t-chain.lf.plan $C12T
            run plancost12t "h + sum R + " "$PY" "$HERE/plancost.py" n12t-base.txt n12t-base.tsv n12t-chain.plan
            run build12 "runs 504, joins inside 5544 (W-sum 21840)" "$PY" "$HERE/build12.py" runs12_12_d0.pkl n12t-chain.plan n12t-runs.plan n12t-base.txt n12t-base.tsv
            "$RECUT" n12t-base.txt n12t-runs.txt --plan-in n12t-runs.plan --co-skip --time 0 --threads 2 > recut12t_runs.log 2>&1
            rm -f n12t-runs.txt
            if tr '\r' '\n' < recut12t_runs.log | grep -q "length 522741782"; then ok "plan of the level-12 run system after the fixed-order pass: 522741782"
            else note "plan of the level-12 run system after the fixed-order pass: $(tr '\r' '\n' < recut12t_runs.log | grep -o 'wrote .* length [0-9]*' | grep -o '[0-9]*$'); mine was 522741782 (it depends on the optimal system the solver returned)"; fi
            "$PY" "$HERE/lift13.py" n12t-runs.txt.plan none n12t-selection.txt --dp-only > lift13_dp.log 2>&1
            if grep -q "joins cost 17406 letters" lift13_dp.log; then ok "the same order cut at vertices: 17406, so 6,747,810,567 at n = 13"
            else note "the same order cut at vertices: $(grep -o 'joins cost [0-9]* letters' lift13_dp.log); mine was 17406"; fi
        fi
    fi
fi

echo
echo "$npass passed, $nfail failed, $nnote notes; logs in $WORK"
[ "$nfail" = 0 ]
