#!/bin/bash
# check.sh MODE [THREADS] [K]
#   Builds genBt and genBp from the sources next to this file, checks the SHA-256 of the selection, the block and the
#   unpacked plan, and then runs MODE:
#     predict   the length of the word from the construction and the plan (no card, 4 threads, about 7 minutes);
#               it trusts the construction, so it is a consistency check, not a proof
#     pass I    pass I (0 <= I < K) of the group check on the card: the word is spelled on the card and only the
#               groups g with g mod K = I are recorded (K = 4: about 19 minutes on an RTX 5090 with 5 host threads)
#     core      ONE pass of the core-table check (coreBp from ../n17: (n-3)! = 6,227,020,800 core bits instead of the
#               (n-2)! group bits; the same length and tree hash as the K passes; about 13 minutes on an RTX 5090,
#               2.5 GB on the card); the word is a superpermutation exactly when the pass is valid
#     all       the K passes one after the other; the word is a superpermutation exactly when every pass is valid
#               and all passes report the same length and tree hash
#     sha       the plain SHA-256 of the letters (genBt --count: one thread, spelled on the CPU, nothing stored;
#               several hours)
#   THREADS = host threads (default 5), K = number of group shards (default 4).
#   Needs gcc, xz, sha256sum; for pass/core/all an NVIDIA card with its driver (libcuda.so.1 or nvcuda.dll, no CUDA
#   toolkit: gcheck17.ptx is loaded at run time) and about 9 GB of memory with K = 4. The word is never stored.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
MODE=${1:?usage: check.sh predict|pass I|core|all|sha [THREADS] [K]}
if [ "$MODE" = pass ]; then I=${2:?pass needs a number}; shift; fi
TH=${2:-5}; K=${3:-4}
PLAN=nB16a_22320795912621.uplan.xz
EXP_LEN=22320795912621
EXP_SHA=e16a7e7f92119f4713e0255cd2856a66dc63efd8e8f9c3c2b89dbd129cf4a61f
EXP_TREE=51e40627c9c9e378cc13256b71e2d730327b7f6e325a87decb4cf5727a32dd91
SEL_SHA=4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a
BLOCK_SHA=6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618
PLAN_SHA=999219c8513c45f0   # first 16 hex digits of the SHA-256 of the unpacked plan
W=${WORK:-$(mktemp -d)}; mkdir -p "$W"
BLOCK="$D/../../proofs/lean/constant305989/data/s103_old2_0.txt"   # the block of the Lean proof
SELXZ="$D/../../arrange/data/n12t-selection.txt.xz"   # the selection of the repository
[ -f "$SELXZ" ] || SELXZ="$D/n12t-selection.txt.xz"
xz -dc "$SELXZ" > "$W/sel.txt"
echo "$SEL_SHA  $W/sel.txt" | sha256sum -c - >&2
echo "$BLOCK_SHA  $BLOCK" | sha256sum -c - >&2
xz -dc "$D/$PLAN" > "$W/plan.uplan"
[ "$(sha256sum "$W/plan.uplan" | cut -c1-16)" = "$PLAN_SHA" ] || { echo "plan differs from the expected one"; exit 1; }
echo "plan OK (unpacked SHA-256 starts $PLAN_SHA)"
export GENB_BLOCK="$BLOCK"
gcc -O3 -march=native -o "$W/genBt" "$D/genBt.c"
if [ "$MODE" = sha ]; then
  "$W/genBt" plan 4 "$W/sel.txt" "$W/plan.uplan" --count 2> "$W/sha.json"; cat "$W/sha.json"
  grep -q "\"length\":$EXP_LEN," "$W/sha.json" || { echo "MISMATCH (length)"; exit 1; }
  grep -q "\"sha256\":\"$EXP_SHA\"" "$W/sha.json" && echo "OK: length and SHA-256 as expected" || { echo "MISMATCH (SHA-256)"; exit 1; }
  exit 0
fi
if [ "$MODE" = core ]; then
  N17="$D/../n17"
  gcc -O3 -march=native -pthread -o "$W/coreBp" "$N17/coreBp.c" -ldl 2>/dev/null || gcc -O3 -march=native -pthread -o "$W/coreBp" "$N17/coreBp.c"
  cp "$N17/gcheckc.ptx" "$W/"
  "$W/coreBp" 4 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --seg 29 --table 22 > "$W/core.json" 2> "$W/core.err" || true
  cat "$W/core.json"
  grep -q "\"length\":$EXP_LEN," "$W/core.json" && grep -q "\"tree_sha256\":\"$EXP_TREE\"" "$W/core.json" \
    && grep -q '"cores":6227020800,' "$W/core.json" && grep -q '"core_bits":6227020800,' "$W/core.json" \
    && grep -q '"missing_permutations":0' "$W/core.json" && grep -q '"shard_complete":true' "$W/core.json" \
    && grep -q '"overflow":0' "$W/core.json" && grep -q '"valid":true' "$W/core.json" \
    && echo "OK: core pass valid, length $EXP_LEN, tree hash $EXP_TREE: every permutation of 16 symbols occurs" \
    || { echo "core pass: MISMATCH or invalid"; exit 1; }
  exit 0
fi
gcc -O3 -march=native -pthread -o "$W/genBp" "$D/genBp.c" -ldl 2>/dev/null || gcc -O3 -march=native -pthread -o "$W/genBp" "$D/genBp.c"
cp "$D/gcheck17.ptx" "$W/"
if [ "$MODE" = predict ]; then
  "$W/genBp" 4 "$W/sel.txt" "$W/plan.uplan" --predict 2> "$W/pred.err" | tee "$W/pred.json"
  grep -q "\"predicted_length\":$EXP_LEN," "$W/pred.json" && echo "OK: the plan gives $EXP_LEN letters" || { echo "MISMATCH"; exit 1; }
  exit 0
fi
if [ "$MODE" = pass ]; then LIST=$I; else LIST=$(seq 0 $((K - 1))); fi
for J in $LIST; do
  echo "pass $J/$K ..."
  "$W/genBp" 4 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --seg 29 --table 22 --gshard "$J/$K" > "$W/p$J.json" 2> "$W/p$J.err" || true
  cat "$W/p$J.json"
  grep -q "\"length\":$EXP_LEN," "$W/p$J.json" && grep -q "\"tree_sha256\":\"$EXP_TREE\"" "$W/p$J.json" \
    && grep -q '"missing_permutations":0' "$W/p$J.json" && grep -q '"shard_complete":true' "$W/p$J.json" \
    && grep -q '"overflow":0' "$W/p$J.json" && grep -q '"valid":true' "$W/p$J.json" \
    && echo "pass $J/$K OK" || { echo "pass $J/$K: MISMATCH or invalid"; exit 1; }
done
[ "$MODE" = all ] && echo "OK: all $K passes valid, length $EXP_LEN, tree hash $EXP_TREE: every permutation of 16 symbols occurs"
exit 0
