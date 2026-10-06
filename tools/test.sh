#!/bin/bash
# test.sh - build every tool and run short end-to-end sequences at n = 10 and n = 11 with known lengths and SHA-256
# values: on Jay Pantone's n = 11 word (tests 1 to 16) and on the words of the other selections (tests 17 to 20).
#
# usage: bash tools/test.sh PANTONE11.txt [REPO=the directory above tools/] [WORK=./test-n11] [THREADS=1]
#
#   PANTONE11.txt  Jay Pantone's word of 43,930,680 letters, unpacked:
#                    git clone https://github.com/jaypantone/superperm-upper-43-80
#                    xz -dkc superperm-upper-43-80/words/11/superpermutation-11-43930680.txt.xz > pantone-11.txt
#   REPO           this repository (the script reads words/, plan/ and reproduce/ from it)
#   WORK           a directory for binaries and outputs (about 600 MB while it runs; the words are removed at the end
#                  unless KEEP=1 is set)
#   THREADS        threads of the passes.  The expected values do not depend on it.
#
# Needs: bash, gcc with OpenMP, xz, sha256sum, and Python 3 for tests 17 to 20 (they are skipped without it).
# 10 to 15 minutes on one thread and 0.6 GB of RAM.
# Every word written is checked with delcheck (all permutations present, no letter that can be deleted).
# GPU=1 also runs the search and segment insertion on the card.  It needs an NVIDIA card and the two kernel files
# WORK/bin/kern.ptx and WORK/bin/segins_kern.ptx (bash tools/mkptx.sh WORK/bin).
# The script prints one line per test and ends with "ALL n TESTS PASSED" or with the list of failures.
# The lengths and hashes below were produced on Windows (MinGW gcc 13.2) and on Linux (gcc 13.3), both x86-64.
HERE=$(cd "$(dirname "$0")" && pwd)
[ $# -ge 1 ] || { sed -n '2,18p' "$0"; exit 1; }
P680=$1; REPO=${2:-$(cd "$HERE/.." && pwd)}; WORK=${3:-./test-n11}; THR=${4:-1}
CC=${CC:-gcc}; CFLAGS=${CFLAGS:--O2 -mpopcnt -fopenmp}
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) DL= ;; *) DL=-ldl ;; esac      # the two GPU files open the CUDA driver library at run time
mkdir -p "$WORK/bin" || exit 1; B=$WORK/bin; export OMP_NUM_THREADS=$THR
npass=0; fails=""
ok()   { npass=$((npass + 1)); echo "ok    $*"; }
bad()  { fails="$fails
  $*"; echo "FAIL  $*"; }
sha()  { sha256sum < "$1" | cut -c1-64; }
len_of() { grep -o 'wrote .* length [0-9]*' "$1" | tail -1 | grep -o '[0-9]*$'; }
# word TAG FILE LENGTH SHA: the file has that many letters, that hash, every permutation and no deletable letter
word() {
  local tag=$1 f=$2 want=$3 wsha=$4 got s
  [ -f "$f" ] || { bad "$tag: $f was not written"; return; }
  got=$(( $(wc -c < "$f") - 1 )); s=$(sha "$f")
  "$B/delcheck" "$f" "$THR" > "$f.delcheck.json" 2>&1
  if ! grep -q '"missing_permutations":0' "$f.delcheck.json"; then bad "$tag: delcheck does not report a valid word"; return; fi
  if ! grep -q '"coverage_preserving_deletions":\[\]' "$f.delcheck.json"; then bad "$tag: delcheck lists a letter that can be deleted"; return; fi
  if [ "$got" != "$want" ]; then bad "$tag: length $got, expected $want"; return; fi
  if [ "$s" != "$wsha" ]; then bad "$tag: length $got as expected, but SHA-256 $s, expected $wsha"; return; fi
  ok "$tag: $got letters, SHA-256 ${s:0:16}..., delcheck clean"
}

echo "== build ($CC $CFLAGS)"
for t in trailsearch recut relocate segins segins_ils letter; do
  $CC $CFLAGS -o "$B/$t" "$HERE/$t.c" -lm || bad "build of $t.c"
done
for t in trailsearch_gpu recut_wide segins_gpu; do
  $CC $CFLAGS -o "$B/$t" "$HERE/$t.c" -lm $DL || bad "build of $t.c"
done
$CC $CFLAGS -o "$B/loopscan" "$HERE/loopscan.c" || bad "build of loopscan.c"
$CC $CFLAGS -o "$B/delcheck" "$HERE/delcheck.c" || bad "build of delcheck.c"
$CC -O2 -o "$B/word2plan" "$HERE/word2plan.c" || bad "build of word2plan.c"
[ -z "$fails" ] && ok "build: 12 programs" || { echo "build failed:$fails"; exit 1; }

echo "== inputs"
W674=$WORK/w674.txt; W628=$WORK/w628.txt
xz -dkc "$REPO/words/superpermutation-11-43930674.txt.xz" > "$W674" || bad "cannot unpack the 43,930,674 word"
xz -dkc "$REPO/words/superpermutation-11-43930628.txt.xz" > "$W628" || bad "cannot unpack the 43,930,628 word"
[ "$(sha "$P680")" = c8de119305a2fd646ba6294832515ff464b399a88a5fe1da9727ed07383f970a ] && ok "Pantone's 43,930,680 word: SHA-256 as expected" || bad "Pantone's word: SHA-256 $(sha "$P680") (is it the unpacked 43,930,680 word, one line and a line feed?)"
[ "$(sha "$W674")" = 7000aa063643e4784e0e10e0c59a5d7220ca000e6d5346babbca3f1692f4ecce ] && ok "my 43,930,674 word: SHA-256 as expected" || bad "the 43,930,674 word: unexpected SHA-256"
[ "$(sha "$W628")" = 47654c92d38eec567897517c7827b1beac9eb81a688c2cf75b6231faf876a7c0 ] && ok "my 43,930,628 word: SHA-256 as expected" || bad "the 43,930,628 word: unexpected SHA-256"

echo "== 1. rebuild of the 43,930,614 word from its plan (trailsearch --time 0)"
"$B/trailsearch" "$W674" "$WORK/t1.txt" --plan-in "$REPO/plan/trailsearch-11-43930614.plan" --time 0 --threads 1 > "$WORK/t1.log" 2>&1
word "rebuild 614" "$WORK/t1.txt" 43930614 388ec7d60116acfac039b45533589f45afa85b13d83ae740a916d3a477ca44ab

echo "== 2. fixed-order pass on Pantone's word (recut --co-skip)"
"$B/recut" "$P680" "$WORK/t2.txt" --co-skip --time 0 > "$WORK/t2.log" 2>&1
word "fixed-order pass" "$WORK/t2.txt" 43930678 2a80e0794421d4c7d422f10f20bc95a7888366455d7336e11d3b8298531ee33a

echo "== 3. relocation on the result (relocate --dpa)"
"$B/relocate" "$P680" "$WORK/t3.txt" --plan-in "$WORK/t2.txt.plan" --threads 1 --time 0 --dpa --dpa-thr "$THR" --dpa-v > "$WORK/t3.log" 2>&1
word "relocation" "$WORK/t3.txt" 43930660 63f0064d741690bc060407ecd1fc88ed2221208ea2148edf099b0d393a7b1d2c

echo "== 4. segment insertion on the result (segins --or3 3 --or3-slack 0)"
"$B/segins" "$P680" "$WORK/t4.txt" --plan-in "$WORK/t3.txt.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 > "$WORK/t4.log" 2>&1
word "segment insertion" "$WORK/t4.txt" 43930653 b369a2674d84383b5886754e54d8f90da43e59ff3b82fa4febab0ba23f59e7da

echo "== 5. loop moves on the result (loopscan --greedy --neutral)"
"$B/loopscan" "$P680" --plan "$WORK/t4.txt.plan" --only PABD --nogap1 --threads "$THR" --quiet --greedy --neutral --nbatch 16 --maxrounds 40 --planout "$WORK/t5.txt.plan" --out "$WORK/t5.txt" > "$WORK/t5.log" 2>&1
word "loop moves after the passes" "$WORK/t5.txt" 43930652 e4ab763c9b93ff09255a05d9b4b2a3f0a52ab152fb2dd3b5a1f26476f48ee87f

echo "== 6. loop moves on Pantone's word as it is (two moves without a second cut are there)"
"$B/loopscan" "$P680" --only PABD --nogap1 --threads "$THR" --quiet --greedy --maxrounds 10 --planout "$WORK/t6.txt.plan" --out "$WORK/t6.txt" > "$WORK/t6.log" 2>&1
word "loop moves on Pantone's word" "$WORK/t6.txt" 43930678 aa9563062035a36ba546c2b9e7d6e0ef96a1fb2e782d368ffb43e9294e68a3e4

echo "== 7. a second cycle of relocation and segment insertion: nothing more is found, and the word must come back unchanged"
"$B/relocate" "$P680" "$WORK/t7a.txt" --plan-in "$WORK/t5.txt.plan" --threads 1 --time 0 --dpa --dpa-thr "$THR" > "$WORK/t7a.log" 2>&1
"$B/segins" "$P680" "$WORK/t7.txt" --plan-in "$WORK/t7a.txt.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 > "$WORK/t7.log" 2>&1
word "second cycle" "$WORK/t7.txt" 43930652 e4ab763c9b93ff09255a05d9b4b2a3f0a52ab152fb2dd3b5a1f26476f48ee87f

echo "== 8. word2plan, then the fixed-order pass: the published 43,930,625 word from the 43,930,628 word"
"$B/word2plan" "$W674" "$W628" "$WORK/p628.plan" --quiet > "$WORK/t8a.log" 2>&1
"$B/recut" "$W674" "$WORK/t8.txt" --plan-in "$WORK/p628.plan" --co-skip --time 0 > "$WORK/t8.log" 2>&1
word "word2plan + fixed-order pass" "$WORK/t8.txt" 43930625 f79f7775ee881bb57bb63c02b0a44b9290d078553e46eaf8f4a13de93933640a

echo "== 9. the same with cuts inside a 1-cycle (recut_wide --wide): the length of Theo H.'s word"
"$B/recut_wide" "$W674" "$WORK/t9.txt" --plan-in "$WORK/p628.plan" --wide --co-skip --time 0 > "$WORK/t9.log" 2>&1
word "fixed-order pass, wide" "$WORK/t9.txt" 43930624 f1688f6ca2a7db3356c907bdddf6a2626c4b5dd41463a779d999e11ad45dff34

echo "== 10. segment insertion on the published 43,930,623 plan"
"$B/segins" "$W674" "$WORK/t10.txt" --plan-in "$REPO/plan/trailsearch-11-43930623.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 > "$WORK/t10.log" 2>&1
word "segment insertion on 623" "$WORK/t10.txt" 43930622 fa6006230e2818ff29977763c6f643d38b804616e5ba17438a7e53abb8b7912a

echo "== 11. the search, one thread, 20000 iterations (the plan the first published trailsearch.c wrote; plans have LF line ends now)"
"$B/trailsearch" "$P680" "$WORK/t11.txt" --seed 7 --kmax 10 --T0 0.3 --threads 1 --iters 20000 --time 100000 > "$WORK/t11.log" 2>&1
word "search" "$WORK/t11.txt" 43930661 d257ae68b550b0e5eb7831b84d2f1ebf9d3a284d899c2bdd62598956b50d4064
[ "$(sha "$WORK/t11.txt.plan")" = 65271a8e0df470c61346e051303dc7f87e3f6e13b2031f86f70d50ecece48579 ] && ok "search: plan SHA-256 as expected" || bad "search: plan SHA-256 $(sha "$WORK/t11.txt.plan") (the temperature depends on the clock: run it again before you call it a failure)"

echo "== 12. the search of trailsearch_gpu.c on the CPU path, 5000 iterations with block moves and the pass inside"
GARGS="--seed 7 --kmax 10 --T0 0.3 --threads 1 --iters 5000 --time 100000 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --cosync"
"$B/trailsearch_gpu" "$P680" "$WORK/t12.txt" $GARGS > "$WORK/t12.log" 2>&1
word "search with block moves, CPU path" "$WORK/t12.txt" 43930662 f5947807994d83455224545901dacd3691790c5dc824b989350bebf72adf4b5a
H12=$(grep -o 'history checksum [0-9a-f]*' "$WORK/t12.log" | tail -1)
[ "$H12" = "history checksum 64a77e7c4957a464" ] && ok "search with block moves: $H12" || bad "search with block moves: '$H12', expected 64a77e7c4957a464 (as in test 11, run it again before you call it a failure)"
if [ "${GPU:-0}" = 1 ]; then
  echo "== 12b. the same on the card"
  "$B/trailsearch_gpu" "$P680" "$WORK/t12g.txt" $GARGS --gpu --ptx "$B/kern.ptx" > "$WORK/t12g.log" 2>&1
  HG=$(grep -o 'history checksum [0-9a-f]*' "$WORK/t12g.log" | tail -1)
  grep -q '^gpu: .*searching on the CPU' "$WORK/t12g.log" && bad "the card was not used: $(grep '^gpu:' "$WORK/t12g.log" | head -1)"
  [ "$HG" = "$H12" ] && [ "$(sha "$WORK/t12g.txt")" = "$(sha "$WORK/t12.txt")" ] && ok "card: same history checksum and same word as the CPU path" || bad "card: '$HG' against '$H12'"
fi

echo "== 13. letter del: no substring of the 43,930,614 word can be deleted"
"$B/letter" del "$WORK/t1.txt" --threads "$THR" > "$WORK/t13.log" 2>&1
grep -q 'coverage-preserving deletions found: 0' "$WORK/t13.log" && ok "letter del: no deletion" || bad "letter del: $(tail -1 "$WORK/t13.log")"

echo "== 14. segins_gpu on the CPU, three cuts on the plan of test 3: the word of test 4"
"$B/segins_gpu" "$P680" "$WORK/t14.txt" --plan-in "$WORK/t3.txt.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 > "$WORK/t14.log" 2>&1
word "segins_gpu, three cuts" "$WORK/t14.txt" 43930653 b369a2674d84383b5886754e54d8f90da43e59ff3b82fa4febab0ba23f59e7da

echo "== 15. segins_gpu on the CPU with moves of equal length, 6 rounds on the 43,930,623 plan (one thread: the draw depends on the number of threads)"
EQARGS="--time 0 --threads 1 --or3 3 --or3-slack 1 --or3-eq 300 --or3-seed 1 --or3-rounds 6"
OMP_NUM_THREADS=1 "$B/segins_gpu" "$W674" "$WORK/t15.txt" --plan-in "$REPO/plan/trailsearch-11-43930623.plan" $EQARGS > "$WORK/t15.log" 2>&1
word "moves of equal length" "$WORK/t15.txt" 43930620 4f2598bfb13ffc18be3d7bf4f6509b7127ca79527a98d6eda1c54cb79da54ed6

echo "== 16. segins_ils: 150 trials of local kicks on the 43,930,623 plan"
"$B/segins_ils" "$W674" "$WORK/t16.txt" --plan-in "$REPO/plan/trailsearch-11-43930623.plan" --time 0 --threads "$THR" --seed 5 --ils 100000 --ils-trials 150 --ils-kmax 1 --ils-kup 3 --ils-slack 2 --ils-near -1 > "$WORK/t16.log" 2>&1
word "local kicks" "$WORK/t16.txt" 43930619 49fb5650af13ad0ed6fa3cde106bef8874626597de70e38bc6e09e155c1bc20b

if [ "${GPU:-0}" = 1 ]; then
  echo "== 14b, 15b. segins_gpu with the candidates judged on the card: the words of tests 14 and 15"
  "$B/segins_gpu" "$P680" "$WORK/t14g.txt" --plan-in "$WORK/t3.txt.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 --or3-gpu --or3-gpu-ptx "$B/segins_kern.ptx" > "$WORK/t14g.log" 2>&1
  grep -q 'judging on the CPU' "$WORK/t14g.log" && bad "segins_gpu: the card was not used (is $B/segins_kern.ptx there?)"
  grep -q 'candidates judged on the card' "$WORK/t14g.log" || bad "segins_gpu: no candidate was judged on the card"
  word "segins_gpu on the card, three cuts" "$WORK/t14g.txt" 43930653 b369a2674d84383b5886754e54d8f90da43e59ff3b82fa4febab0ba23f59e7da
  OMP_NUM_THREADS=1 "$B/segins_gpu" "$W674" "$WORK/t15g.txt" --plan-in "$REPO/plan/trailsearch-11-43930623.plan" $EQARGS --or3-gpu-check --or3-gpu-ptx "$B/segins_kern.ptx" > "$WORK/t15g.log" 2>&1
  grep -q ' 0 MISMATCHES' "$WORK/t15g.log" && ! grep -q ' [1-9][0-9]* MISMATCHES' "$WORK/t15g.log" && ok "card against host: $(grep -o 'or3-gpu-check: [0-9]* candidates judged on both, 0 MISMATCHES' "$WORK/t15g.log" | tail -1)" || bad "segins_gpu: the card and the host disagree, or the check did not run"
  word "moves of equal length on the card" "$WORK/t15g.txt" 43930620 4f2598bfb13ffc18be3d7bf4f6509b7127ca79527a98d6eda1c54cb79da54ed6
fi

# ---- the words of the other selections: selection -> base word (reproduce/tools/geng.py) -> word, with the loader
PY=${PYTHON:-$(command -v python3 || command -v python)}
export PYTHONDONTWRITEBYTECODE=1 # leave no __pycache__ next to the scripts of reproduce/
if [ -z "$PY" ] || [ ! -d "$REPO/reproduce" ]; then
  echo "== 17 to 20 skipped: no Python 3, or no reproduce/ in $REPO"
else
  newword() {    # N LENGTH BASE-SHA WORD-SHA: generator, loader, the writer of reproduce/, and their agreement
    local n=$1 L=$2 bsha=$3 wsha=$4 R=$REPO/reproduce sel plan
    sel=$R/selections/n$n-selection.txt; plan=$R/plan/n$n-$L.plan
    [ -f "$sel" ] || { bad "n = $n: $sel is not there"; return; }
    [ -f "$plan" ] || { bad "n = $n: the plan $plan is not there"; return; }
    "$PY" "$R/tools/geng.py" "$sel" "$WORK/n$n-base.txt" --table "$WORK/n$n-base.tsv" > "$WORK/n$n-geng.log" 2>&1 || { bad "n = $n: geng.py failed: $(tail -1 "$WORK/n$n-geng.log")"; return; }
    [ "$(sha "$WORK/n$n-base.txt")" = "$bsha" ] && ok "n = $n: base word from the selection, SHA-256 as expected" || bad "n = $n: base word SHA-256 $(sha "$WORK/n$n-base.txt")"
    "$B/trailsearch" "$WORK/n$n-base.txt" "$WORK/t-n$n.txt" --plan-in "$plan" --time 0 --threads 1 > "$WORK/t-n$n.log" 2>&1
    word "n = $n: the word of the plan, written by trailsearch" "$WORK/t-n$n.txt" "$L" "$wsha"
    "$PY" "$R/tools/applyplan.py" "$WORK/n$n-base.txt" "$WORK/n$n-base.tsv" "$plan" "$WORK/a-n$n.txt" > "$WORK/a-n$n.log" 2>&1
    cmp -s "$WORK/t-n$n.txt" "$WORK/a-n$n.txt" && ok "n = $n: applyplan.py writes the same word" || bad "n = $n: applyplan.py and trailsearch write different words"
  }
  echo "== 17. n = 10: selection, base word, word"
  newword 10 4034855 0ccfcddc26ed6a3268d38dabd8398c308cdf3a14e0d957c88fa554c9ecbd48c3 09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
  echo "== 18. n = 11: selection, base word, word"
  newword 11 43930578 9bcb862f56592583c4e4f34e9c7d366e2c3753be98b08d3ce1877ecec02a4e84 65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092
  echo "== 19. the passes on the n = 10 base word as it is: fixed-order pass, then three cuts (recut, segins_gpu)"
  "$B/recut" "$WORK/n10-base.txt" "$WORK/t19a.txt" --co-skip --time 0 > "$WORK/t19a.log" 2>&1
  "$B/segins_gpu" "$WORK/n10-base.txt" "$WORK/t19.txt" --plan-in "$WORK/t19a.txt.plan" --time 0 --threads "$THR" --or3 3 --or3-slack 0 > "$WORK/t19.log" 2>&1
  word "n = 10: passes on the new pieces" "$WORK/t19.txt" 4035422 4a88917ca5ef7d0617c6f703430d9db137dab249c101de01fb6cbe9cfc2f39b8
  echo "== 20. moves of equal length on the n = 11 word: 3 rounds, the length must stay"
  OMP_NUM_THREADS=1 "$B/segins_gpu" "$WORK/n11-base.txt" "$WORK/t20.txt" --plan-in "$REPO/reproduce/plan/n11-43930578.plan" --time 0 --threads 1 --or3 3 --or3-slack 1 --or3-eq 300 --or3-seed 1 --or3-rounds 3 > "$WORK/t20.log" 2>&1
  word "n = 11: moves of equal length on the new pieces" "$WORK/t20.txt" 43930578 e07c5fbc4f28cc06a5897df22692967a48142b6aef8fbf175e13890adf2f303c
fi

[ "${KEEP:-0}" = 1 ] || rm -f "$WORK"/t*.txt "$WORK"/a-n*.txt "$WORK"/n1?-base.txt "$W674" "$W628"       # KEEP=1 keeps the words
echo
if [ -z "$fails" ]; then echo "ALL $npass TESTS PASSED"; else echo "FAILED:$fails"; exit 1; fi
