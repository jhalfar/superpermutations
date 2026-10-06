#!/bin/bash
# test.sh - build the four selections again from Pantone's construction-input.txt and the data files of this
# directory, compare them with the expected SHA-256 values, and run the checkers on them.
#
# usage:   bash test.sh construction-input.txt [WORK] [SELDIR]
#   WORK     directory for the files that are written (default: test_work in the current directory)
#   SELDIR   directory with the selection files of the reproduction package (n10-selection.txt, n11-selection.txt,
#            n12-selection.txt.xz, n13-selection.txt.xz).  When given, the data lines of the files built here are
#            compared with them too.  Without GUROBI=1 it must be given: the n = 10 selection is then read from it
#            (the other three are built from it and from Pantone's file).
#   GUROBI=1 bash test.sh ...   also run the steps that need the solver: the search that found the n = 10
#            selection, and the block solvers (about 4 minutes more, two threads)
#   PY=python3 bash test.sh ... the interpreter (default: python)
#
# A selection file is compared by the SHA-256 of its data lines: every line that is not a comment, with LF line
# ends.  needs: bash, Python 3, numpy; Gurobi only with GUROBI=1.
# cost (measured, one thread): 2 to 3 minutes and 1.0 GB without GUROBI=1.
set -u
export PYTHONDONTWRITEBYTECODE=1        # leave no __pycache__ next to the scripts
IN=${1:?usage: bash test.sh construction-input.txt [WORK] [SELDIR]}
WORK=${2:-test_work}
SELDIR=${3:-}
PY=${PY:-python}
HERE=$(cd "$(dirname "$0")" && pwd)
D=$HERE/data
# the scripts are run from their own directory, so the three paths are made absolute first
mkdir -p "$WORK" || exit 2
WORK=$(cd "$WORK" && pwd)
[ -f "$IN" ] || { echo "no such file: $IN"; exit 2; }
IN=$(cd "$(dirname "$IN")" && pwd)/$(basename "$IN")
if [ -n "$SELDIR" ]; then SELDIR=$(cd "$SELDIR" && pwd) || exit 2; fi
npass=0; nfail=0

ok()   { npass=$((npass + 1)); echo "PASS  $*"; }
bad()  { nfail=$((nfail + 1)); echo "FAIL  $*"; }
# SHA-256 of the data lines of a selection file (plain or .xz)
dsha() { "$PY" -c "
import sys, hashlib, lzma
raw = (lzma.open if sys.argv[1].endswith('.xz') else open)(sys.argv[1], 'rb').read()
print(hashlib.sha256(b''.join(l.rstrip(b'\r\n') + b'\n' for l in raw.split(b'\n') if l.strip() and not l.startswith(b'#'))).hexdigest())" "$1"; }
# run NAME "TEXT THAT MUST APPEAR" command...
run()  { local name=$1 want=$2; shift 2
         if "$@" > "$WORK/$name.log" 2>&1 && grep -q -- "$want" "$WORK/$name.log"; then ok "$name"; else bad "$name (see $WORK/$name.log)"; fi; }
# same NAME FILE EXPECTED_SHA
same() { local got; got=$(dsha "$2"); if [ "$got" = "$3" ]; then ok "$1  $got"; else bad "$1: data lines $got, expected $3"; fi; }

S10=831629a05349fb4fda1c7935dff5dfb1195c0c2ebbff9a2aeff2952748e5c355     # n = 10 selection (9 symbols, two walks)
S11=ad6089beb2bce8c14f40af05d7442a5402555948555357e96b77cb1a210cc38d     # n = 11 selection (10 symbols)
S12=2c3714ed81df9ba38ba13413f4b529415556182e2fa595515079ac0b4a4b2d6c     # n = 12 selection (11 symbols)
S13=37aa449e31ecbda1447b85205c78a4329c73108fe45308950c2a2b2df08ca296     # n = 13 selection (12 symbols)
SB8=97a6e0d8c256992ae6b6039e5c0d99d9d794e7ebe99a81f439b908297a9fd8b9     # Pantone's 8-symbol selection
SX2=4bd63f5564a2bcd780b30c41e517a86ffce89fdfee5bed8baebdcb9f2dba8c74     # 10 symbols, the plain block in all 48 blocks
SC=12cfdcf10eb417101e86056522287b3483400cb960e5e98ff0c79b0b8c47c7a3      # the transportable 11-symbol selection
B72=6629d5c9d3b57b1ffa08c64fcaf2b3dd3ff6099d1ff1aa8ddfaf1ea6c6864bce     # data/block_7_2_n11.txt
B74=ee195555798ad0246da946c65a1c9303c3c4b6f3df07481e0cd43fc138149c81     # data/block_7_4_n13.txt
B74S=1f0b7ae253c5218d271148d8cf880781e8365d657643be6def9fee45e121d6e3    # data/block_7_4_step2.txt

cd "$HERE" || exit 1
echo "== the library and Pantone's input"
run gcore_test "K = 7: 40 random selections, port formula = literal endpoint graph" "$PY" gcore.py --test
run acct "floor 193/360" "$PY" acct.py "$IN"
run untransport_10 "differ from the transport of the result: 56" "$PY" untransport.py "$IN" --out "$WORK/sel9_pantone.txt"
run untransport_9 "loops without a row 48, 2 walks" "$PY" untransport.py "$WORK/sel9_pantone.txt" --out "$WORK/base8.txt"
same base8 "$WORK/base8.txt" $SB8

echo "== n = 10"
if [ "${GUROBI:-0}" = 1 ]; then
  run lns_n10 "cost 2702 = 2688 + trails 14 (2 walks)" "$PY" lns.py "$WORK/base8.txt" "$WORK/n10.txt" --transport 1 --order walk \
      --free 300 --rounds 3 --time 30 --pool 40 --seed 1 --threads 2
elif [ -n "$SELDIR" ]; then
  cp "$SELDIR/n10-selection.txt" "$WORK/n10.txt"
else
  echo "without GUROBI=1 the n = 10 selection must come from SELDIR (third argument)"; exit 2
fi
same n10 "$WORK/n10.txt" $S10
run check2_n10 "closed trails 350 -> AGREE" "$PY" check2.py "$WORK/n10.txt" --complete
run gcover_n10 "every class exactly once: True" "$PY" gcover.py "$WORK/n10.txt"

echo "== n = 11"
run gapply "880 closed trails (formula 880)" "$PY" gapply.py "$IN" "$D/block_7_2_n11.txt" "$WORK/n11_plain.txt" --literal
same n11_plain "$WORK/n11_plain.txt" $SX2
run gregion "800 closed trails (formula 800)" "$PY" gregion.py multi "$IN" "$D/block_7_2_n11.txt" "$WORK/n11.txt" \
    "$D/connect_n11_a.json" "$D/connect_n11_b.json" --walks 0:0
same n11 "$WORK/n11.txt" $S11
run gcover_n11 "every class exactly once: True" "$PY" gcover.py "$WORK/n11.txt"
run check2_n11 "closed trails 800 -> AGREE" "$PY" check2.py "$WORK/n11.txt" --complete
run check12_n11 "trails after completion 800" "$PY" check12.py "$WORK/n11.txt"

echo "== n = 12"
run hybrid3_n12 "trails at n = 12: 3648" "$PY" hybrid3.py "$WORK/base8.txt" "$WORK/n10.txt" 3 "$D/block_7_3_n12.txt" "$WORK/n12.txt"
same n12 "$WORK/n12.txt" $S12
run check2_n12 "floor (Q + trails)/(k-2)! = 43/84" "$PY" check2.py "$WORK/n12.txt"
run check12_n12 "trails after completion 3648" "$PY" check12.py "$WORK/n12.txt"
run hybrid3_c "trails at n = 12: 7200" "$PY" hybrid3.py "$WORK/base8.txt" "$WORK/n10.txt" 3 "$D/block_7_3_c.txt" "$WORK/sel11c.txt" --fsd
same sel11c "$WORK/sel11c.txt" $SC
run check12_c "floor c = (Q + trails) / (K-1)! = 185280 / 362880 = 193/378" "$PY" check12.py "$WORK/sel11c.txt"

echo "== n = 13"
run build12 "wrote" "$PY" build12.py "$WORK/sel11c.txt" "$WORK/base8.txt" "$D/block_7_4_n13.txt" "$WORK/n13.txt"
same n13 "$WORK/n13.txt" $S13
run check12_n13 "trails after completion 23808" "$PY" check12.py "$WORK/n13.txt"

if [ -n "$SELDIR" ]; then
  echo "== the selection files of the reproduction package"
  same package_n10 "$SELDIR/n10-selection.txt" $S10
  same package_n11 "$SELDIR/n11-selection.txt" $S11
  same package_n12 "$SELDIR/n12-selection.txt.xz" $S12
  same package_n13 "$SELDIR/n13-selection.txt.xz" $S13
fi

echo "== the block solutions: literal completion"
for b in block_7_2_n11 block_7_3_c block_7_3_n12 block_7_4_step1 block_7_4_step2 block_7_4_n13; do
  run lit_$b "AGREE" "$PY" lit_block.py "$D/$b.txt"
done

echo "== rows of other lengths have no transport (K = 6)"
run transport_search "d = 3 (L = 3): 0 transport rules" "$PY" transport_search.py 6
run transport_search2 "K = 6, d = 3" "$PY" transport_search2.py 6

echo "== connector cycles"
run conn_lift_9 "-> ALL MET" "$PY" conn.py "$WORK/base8.txt" --lift "$D/cycles_n9.txt"
run conn_lift_10 "-> ALL MET" "$PY" conn.py "$WORK/n10.txt" --lift "$D/cycles_n10.txt"
if command -v "${CC:-gcc}" > /dev/null 2>&1; then
  if "${CC:-gcc}" -O2 -o "$WORK/cyccheck" cyccheck.c > "$WORK/cyccheck_build.log" 2>&1; then
    run cyccheck_n12 "walk trails met: 1152 of 1152 -> ALL WALK TRAILS MET" "$WORK/cyccheck" "$WORK/sel11c.txt" "$D/zcycles_n12.txt"
  else
    bad "cyccheck.c does not compile (see $WORK/cyccheck_build.log)"
  fi
else
  echo "SKIP  cyccheck (no C compiler found; set CC)"
fi

if [ "${GUROBI:-0}" = 1 ]; then
  echo "== the block solvers"
  run gblock_n11 "priced 60.00: Q 38, D 14 in 3 chains, walk trails 2" "$PY" gblock.py 7 2 --cC 2 --pool 3000 --gap 1.01 \
      --time 200 --threads 1 --out "$WORK/block_7_2.txt"
  same block_7_2 "$WORK/block_7_2.txt" $B72
  run gblock_49 "objective 49.00, bound 49.00" "$PY" gblock.py 7 2 --pool 2000 --gap 0 --threads 1
  run grb_72 "optimum of the model objective = 49.0 (bound 49.0) in block units; pool: 336 solutions" "$PY" block_grb.py 7 2 --sym none --slack 0
  run grb_73_fs "optimum of the model objective = 308.0 (bound 308.0) in block units; pool: 6 solutions" "$PY" block_grb.py 7 3 --sym old --maxd 2 --slack 0
  run grb_73 "optimum of the model objective = 301.0 (bound 301.0) in block units; pool: 12 solutions" "$PY" block_grb.py 7 3 --sym old --slack 0
  run gsegip_step2 "Q 2611 D 266 chains 84 walks 5 trails 24 floor 2901" "$PY" gsegip.py 7 4 --dmax 6 --P 2.6 --wt 3.5 --chains \
      --lns 2000 --sub 50 --frac 0.3 --time 100 --threads 1 --seed 101 --start "$D/block_7_4_step1.txt" --out "$WORK/block_7_4_step2.txt"
  same block_7_4_step2 "$WORK/block_7_4_step2.txt" $B74S
  # the round that finds this block ends by its time limit of 60 s: on a much slower machine it can fail
  run gsegip_n13 "Q 2611 D 266 chains 84 walks 5 trails 20 floor 2897" "$PY" gsegip.py 7 4 --dmax 6 --P 4.5 --wt 1 --wu 4.5 --zprice \
      --chains --lns 2000 --sub 60 --frac 0.35 --time 100 --threads 1 --seed 91 --start "$D/block_7_4_step2.txt" --out "$WORK/block_7_4.txt"
  same block_7_4_n13 "$WORK/block_7_4.txt" $B74
fi

echo
if [ $nfail = 0 ]; then echo "ALL $npass TESTS PASSED"; else echo "$nfail of $((npass + nfail)) TESTS FAILED"; exit 1; fi
