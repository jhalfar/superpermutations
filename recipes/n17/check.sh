#!/bin/bash
# check.sh MODE [THREADS] [K]
#   Builds the programs from the sources next to this file (and ../n16 for pass/all), checks the SHA-256 of the
#   selection, the block and the unpacked plan, and then runs MODE:
#     predict   the length of the word from the construction and the plan (no card, 4 threads, about 35 minutes);
#               it trusts the construction, so it is a consistency check, not a proof
#     core      ONE pass of the core-table check on the card: (n-3)! = 87,178,291,200 core bits instead of the
#               (n-2)! group bits, so the word is spelled and scanned once (about 3.8 hours on an RTX 5090 with
#               12 host threads); the word is a superpermutation exactly when the pass is valid. The same pass
#               computes the BLAKE3 hash of the letters on the card (blake3.h) and compares it with EXP_BLAKE3
#     pass I    pass I (0 <= I < K) of the older group check: only the groups g with g mod K = I are recorded
#               (K = 8: 21.7 GB on the card, about 3 hours per pass with 12 host threads)
#     all       the K passes one after the other; valid exactly when every pass is valid and all report the same
#               length and tree hash
#     sha       the plain SHA-256 of the letters (genBt --count: one thread, spelled on the CPU, nothing stored;
#               about 4.4 days)
#   THREADS = host threads (default 12; 4 for predict), K = number of group shards (default 8).
#   Needs gcc, xz, sha256sum; for core/pass/all an NVIDIA card with its driver (libcuda.so.1 or nvcuda.dll, no CUDA
#   toolkit: the .ptx files are loaded at run time) with 13.3 GB free for core or 22.5 GB for a pass with K = 8,
#   and 6.3 GB (core) or about 10 GB (pass) of host memory. The word is never stored.
set -eu
D=$(cd "$(dirname "$0")" && pwd)
MODE=${1:?usage: check.sh predict|core|pass I|all|sha [THREADS] [K]}
if [ "$MODE" = pass ]; then I=${2:?pass needs a number}; shift; fi
TH=${2:-12}; K=${3:-8}
[ "$MODE" = predict ] && TH=${2:-4}
PLAN=nB17a_377961971839096.uplan.xz
EXP_LEN=377961971839096
EXP_SHA=                  # the plain SHA-256 of the letters: not known yet (the run takes days); sha mode prints it
EXP_TREE=a17d292c31673102f3c18fa152317e81119320fb89d11815f9be6a59bdf425b2
EXP_BLAKE3=5d64909d4fd6420e9e5549367e2907ea13fc15d6e2fd1ea419e0b4caa48d8555   # BLAKE3 of the letters, as b3sum prints it
SEL_SHA=4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a
BLOCK_SHA=6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618
PLAN_SHA=5253c2c6877bea60        # first 16 hex digits of the SHA-256 of the unpacked plan
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
if [ "$MODE" = sha ]; then
  gcc -O3 -march=native -o "$W/genBt" "$D/genBt.c"
  "$W/genBt" plan 5 "$W/sel.txt" "$W/plan.uplan" --count 2> "$W/sha.json"; cat "$W/sha.json"
  grep -q "\"length\":$EXP_LEN," "$W/sha.json" || { echo "MISMATCH (length)"; exit 1; }
  if [ -z "$EXP_SHA" ]; then echo "length as expected; the SHA-256 above is the plain SHA-256 of the word (no value recorded to compare with)"; exit 0; fi
  grep -q "\"sha256\":\"$EXP_SHA\"" "$W/sha.json" && echo "OK: length and SHA-256 as expected" || { echo "MISMATCH (SHA-256)"; exit 1; }
  exit 0
fi
if [ "$MODE" = predict ] || [ "$MODE" = core ]; then
  # the same host code as ../n16/genBp.c with the card check of gcardc.h
  gcc -O3 -march=native -pthread -o "$W/coreBp" "$D/coreBp.c" -ldl 2>/dev/null || gcc -O3 -march=native -pthread -o "$W/coreBp" "$D/coreBp.c"
  cp "$D/gcheckc.ptx" "$W/"
  if [ "$MODE" = predict ]; then
    "$W/coreBp" 5 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --predict --job 28 2> "$W/pred.err" | tee "$W/pred.json"
    grep -q "\"predicted_length\":$EXP_LEN," "$W/pred.json" && echo "OK: the plan gives $EXP_LEN letters" || { echo "MISMATCH"; exit 1; }
    exit 0
  fi
  echo "core pass ..."
  "$W/coreBp" 5 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --seg 29 --table 22 --blake3 > "$W/core.json" 2> "$W/core.err" || true
  cat "$W/core.json"
  grep -q "\"length\":$EXP_LEN," "$W/core.json" && grep -q "\"tree_sha256\":\"$EXP_TREE\"" "$W/core.json" \
    && grep -q "\"blake3\":\"$EXP_BLAKE3\"" "$W/core.json" \
    && grep -q '"cores":87178291200,' "$W/core.json" && grep -q '"core_bits":87178291200,' "$W/core.json" \
    && grep -q '"missing_permutations":0' "$W/core.json" && grep -q '"shard_complete":true' "$W/core.json" \
    && grep -q '"overflow":0' "$W/core.json" && grep -q '"valid":true' "$W/core.json" \
    && echo "OK: core pass valid, length $EXP_LEN, tree hash $EXP_TREE, BLAKE3 $EXP_BLAKE3: every permutation of 17 symbols occurs" \
    || { echo "core pass: MISMATCH or invalid"; exit 1; }
  exit 0
fi
# pass / all: the group check of ../n16 (genBp.c, gcard17.h, gcheck17.ptx)
N16="$D/../n16"
gcc -O3 -march=native -pthread -o "$W/genBp" "$N16/genBp.c" -ldl 2>/dev/null || gcc -O3 -march=native -pthread -o "$W/genBp" "$N16/genBp.c"
cp "$N16/gcheck17.ptx" "$W/"
if [ "$MODE" = pass ]; then LIST=$I; else LIST=$(seq 0 $((K - 1))); fi
for J in $LIST; do
  echo "pass $J/$K ..."
  "$W/genBp" 5 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --seg 29 --table 22 --gshard "$J/$K" > "$W/p$J.json" 2> "$W/p$J.err" || true
  cat "$W/p$J.json"
  grep -q "\"length\":$EXP_LEN," "$W/p$J.json" && grep -q "\"tree_sha256\":\"$EXP_TREE\"" "$W/p$J.json" \
    && grep -q '"missing_permutations":0' "$W/p$J.json" && grep -q '"shard_complete":true' "$W/p$J.json" \
    && grep -q '"overflow":0' "$W/p$J.json" && grep -q '"valid":true' "$W/p$J.json" \
    && echo "pass $J/$K OK" || { echo "pass $J/$K: MISMATCH or invalid"; exit 1; }
done
[ "$MODE" = all ] && echo "OK: all $K passes valid, length $EXP_LEN, tree hash $EXP_TREE: every permutation of 17 symbols occurs"
exit 0
