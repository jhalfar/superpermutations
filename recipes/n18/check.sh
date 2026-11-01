#!/bin/bash
# check.sh MODE [THREADS]
#   Rebuilds the unit plan of the 18-symbol word from the n = 17 plan of ../n17 and checks it against the plan hash
#   fixed in COMMITMENT.md, then runs MODE:
#     plan      only the plan: lift (gen/liftB6.c, chunked exact DP in RAM; about 6.5 hours with 12 threads,
#               about 19 GB of memory, 15.6 GB of disk) and the SHA-256 against COMMITMENT.md
#     keys      the four hash keys from the drand round of COMMITMENT.md and the plan hash (drand_keys.py), compared
#               with the keys of the recorded run; needs no plan
#     predict   the length of the word from the construction and the plan (no card, about 2.7 hours with 16
#               threads); it trusts the construction, so it is a consistency check, not a proof
#     card      the probabilistic check on the card (ck/mh6.c, mode hash): the word is spelled on the card from the
#               plan and never stored, every completed group goes into four hash sums mod 2^61 - 1 with the keys
#               above, and the tree hash and BLAKE3 of the letters are computed in the same pass (about 3.3 days on
#               an RTX 5090 with 12 host threads, 2.8 GB on the card, about 28 GB of host memory)
#     all       plan, keys and card
#   THREADS = host threads (default 12). WORK = work directory (default a new temporary one); a plan already built
#   and checked there (plan.uplan with plan.ok) is used again, so plan and card can run on different days.
#   Needs gcc, xz, sha256sum, python3; for card an NVIDIA card with its driver (libcuda.so.1 or nvcuda.dll, no CUDA
#   toolkit: the .ptx file is loaded at run time).
set -eu
D=$(cd "$(dirname "$0")" && pwd)
MODE=${1:?usage: check.sh plan|keys|predict|card|all [THREADS]}
TH=${2:-12}
EXP_PLAN=725d7a39d348237c18684a1b537005973e0303203b45fdacefa5aa57ba568094   # COMMITMENT.md
EXP_LEN=6779644944870572
EXP_TREE=4c14e9947531131c91b58d2f0dfc9a68c06667a61fb5a91b14bfe83d6323b2c1
EXP_BLAKE3=8a5344098c97b5d6f34a66b56afafbf2f9928e95690b4604210fc7db12122af6   # BLAKE3 of the letters, as b3sum prints it
EXP_MHR=270019678532581369,412816273071405168,1993030073443076200,237075717758712977
SEL_SHA=4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a
BLOCK_SHA=6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618
LOWER=nB17a_377961971839096.uplan.xz
LOWER_SHA=5253c2c6877bea60       # first 16 hex digits of the SHA-256 of the unpacked n = 17 plan (as ../n17/check.sh)
# The committed plan was written on Windows: CRLF line ends, and line 2 names the path of the n = 17 plan on that
# machine. The hash is taken of the plan in that form; nothing else in the file depends on the path.
LINE2='# units in the order of the trails of D:/Studia/Superpermutations/bigtmp/constB/nB17a.uplan, openings by liftB6 dp (23697 chunks of 32768 units)'

if [ "$MODE" = keys ] || [ "$MODE" = all ]; then
  R=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["randomness"])' "$D/drand/round33475799.json")
  K=$(python3 "$D/drand_keys.py" "$R" "$EXP_PLAN")
  echo "$K"
  [ "$K" = "MHR=$EXP_MHR" ] && echo "keys OK (drand round 33475799, plan $EXP_PLAN)" || { echo "keys MISMATCH"; exit 1; }
  [ "$MODE" = keys ] && exit 0
fi

W=${WORK:-$(mktemp -d)}; mkdir -p "$W"
BLOCK="$D/../../proofs/lean/constant305989/data/s103_old2_0.txt"   # the block of the Lean proof
SELXZ="$D/../../arrange/data/n12t-selection.txt.xz"               # the selection of the repository
xz -dc "$SELXZ" > "$W/sel.txt"
echo "$SEL_SHA  $W/sel.txt" | sha256sum -c - >&2
echo "$BLOCK_SHA  $BLOCK" | sha256sum -c - >&2
export GENB_BLOCK="$BLOCK"

if [ ! -f "$W/plan.ok" ]; then
  xz -dc "$D/../n17/$LOWER" > "$W/lower.uplan"
  [ "$(sha256sum "$W/lower.uplan" | cut -c1-16)" = "$LOWER_SHA" ] || { echo "the n = 17 plan differs from the expected one"; exit 1; }
  gcc -O3 -march=native -pthread -o "$W/liftB6" "$D/gen/liftB6.c" -lm
  echo "lift (n = 17 plan -> n = 18 plan), $TH threads ..."
  "$W/liftB6" lift 6 "$W/sel.txt" "$W/lower.uplan" "$W/plan.uplan" --threads "$TH" --chunk 32768 > "$W/lift.log" 2>&1
  tail -5 "$W/lift.log"
  rm -f "$W/lower.uplan"
  grep -q "^LENGTH $EXP_LEN" "$W/lift.log" || { echo "lift: unexpected length"; exit 1; }
  # the plan in the committed form: line 2 as above, every line ended by CR LF
  S=$( { head -n 1 "$W/plan.uplan" | tr -d '\r'; printf '%s\n' "$LINE2"; tail -n +3 "$W/plan.uplan" | tr -d '\r'; } \
       | sed 's/$/\r/' | sha256sum | cut -d' ' -f1 )
  echo "plan SHA-256 (committed form) $S"
  [ "$S" = "$EXP_PLAN" ] || { echo "plan MISMATCH: not the plan of COMMITMENT.md"; exit 1; }
  touch "$W/plan.ok"
fi
echo "plan OK: it is the plan of COMMITMENT.md ($EXP_PLAN)"
[ "$MODE" = plan ] && exit 0

mkdir -p "$W/gen" "$W/ck"
cp "$D/gen/genB6.c" "$W/gen/"; cp "$D/ck/mh6.c" "$D/ck/gcard6.h" "$D/ck/blake3.h" "$D/ck/gcheck6.ptx" "$W/ck/"
gcc -O3 -march=native -pthread -o "$W/ck/mh6" "$W/ck/mh6.c" -ldl -lm 2>/dev/null || gcc -O3 -march=native -pthread -o "$W/ck/mh6" "$W/ck/mh6.c" -lm

if [ "$MODE" = predict ]; then
  "$W/ck/mh6" 6 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --predict --job 28 2> "$W/pred.err" | tee "$W/pred.json"
  grep -q "\"predicted_length\":$EXP_LEN," "$W/pred.json" && echo "OK: the plan gives $EXP_LEN letters" || { echo "MISMATCH"; exit 1; }
  exit 0
fi

echo "card pass (hash mode) ..."
"$W/ck/mh6" 6 "$W/sel.txt" "$W/plan.uplan" --threads "$TH" --mode hash --blake3 --seg 30 --table 24 --mhr "$EXP_MHR" \
  > "$W/card.json" 2> "$W/card.err" || true
cat "$W/card.json"
grep -q "\"length\":$EXP_LEN," "$W/card.json" && grep -q "\"tree_sha256\":\"$EXP_TREE\"" "$W/card.json" \
  && grep -q "\"blake3\":\"$EXP_BLAKE3\"" "$W/card.json" \
  && grep -q '"mh_events":20922789888000,' "$W/card.json" && grep -q '"mh_N":20922789888000,' "$W/card.json" \
  && grep -q '"hash_valid":true' "$W/card.json" && grep -q '"overflow":0,' "$W/card.json" \
  && grep -q '"shard_complete":true' "$W/card.json" && grep -q '"valid":true' "$W/card.json" \
  && echo "OK: card pass valid, length $EXP_LEN, tree hash $EXP_TREE, BLAKE3 $EXP_BLAKE3: every permutation of 18 symbols occurs, up to a false pass probability of at most 6.8e-21" \
  || { echo "card pass: MISMATCH or invalid"; exit 1; }
exit 0
