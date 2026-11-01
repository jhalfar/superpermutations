# A superpermutation on 18 symbols from selection C and a block (a recipe)

A word of 6,779,644,944,870,572 letters on the alphabet `0123456789ABCDEFGH` that contains all
6,402,373,705,728,000 permutations of 18 symbols, checked on a graphics card in one pass by a probabilistic check
whose keys were fixed after the plan (below). Tree hash of the word (the SHA-256 of the SHA-256 digests of its
64 KiB leaves): `4c14e9947531131c91b58d2f0dfc9a68c06667a61fb5a91b14bfe83d6323b2c1`. BLAKE3 of the letters (the value
`b3sum` prints for the word with no line feed), computed on the card in the same pass:
`8a5344098c97b5d6f34a66b56afafbf2f9928e95690b4604210fc7db12122af6`. I have no plain SHA-256 of this word: it is
sequential and would take about 80 days on one thread (the n = 17 run, 4.6 days, scaled by length), so the BLAKE3 is the name
of the word.

It is 7,683,011,380 letters below the value of the Lean theorem `hasWord_eighteen_B : HasWord 18 6779652627881952`
(`proofs/lean/constant305989/SuperpermutationUpperBound305989/CorollariesB.lean`, described in
[`proofs/lean/constant305989/`](../../proofs/lean/constant305989/README.md)).

The word would take 6.8 PB, so it is not stored, and neither is its plan: the plan is 15.6 GB of text (630 MB as xz,
above the file limit of GitHub). `check.sh` rebuilds the plan from the n = 17 plan of [`recipes/n17/`](../n17/README.md)
and checks it against the hash in [`COMMITMENT.md`](COMMITMENT.md). The word is then written by `gen/genB6.c` from:

* the selection C on 11 symbols, the same file as for n = 14 to 17 (`arrange/data/n12t-selection.txt.xz`; SHA-256 of its
  text `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`);
* `proofs/lean/constant305989/data/s103_old2_0.txt`, the block of the Lean proof (SHA-256
  `6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618`);
* the unit plan: 776,490,624 units (484,323,840 small units and 292,166,784 walk units), 15,602,710,590 bytes,
  SHA-256 `725d7a39d348237c18684a1b537005973e0303203b45fdacefa5aa57ba568094`, with 2,019,950,237 letters in joins;
* `gen/genB6.c`, the generator for L <= 6 (C, standard library only), the n = 17 generator extended by one level.

The construction (slices, transport, completion, closed trails) is Jay Pantone's. The block step on top of it is
mine, proved in Lean in `proofs/lean/constant305989/`. The plan is the n = 17 plan lifted once more by `gen/liftB6.c`:
every closed trail of that word is one unit here, in the same order, and the openings are chosen again by an exact
dynamic programme, cut into 23,697 chunks of 32,768 units (at most 164,070 letters above the optimum of one programme
over the whole plan, by the bound the program prints).

## Checking

```sh
bash check.sh keys         # the four hash keys from the drand round and the plan hash; seconds
bash check.sh plan         # rebuild the plan and compare it with COMMITMENT.md; about 6.5 hours, 19 GB of memory
bash check.sh predict      # the length from the plan and the construction, no card; about 2.7 hours on 16 threads
bash check.sh card         # the check on the card: about 3.3 days
bash check.sh all          # keys, plan and card
```

With `WORK=DIR` the plan stays in DIR (15.6 GB) and a later `predict` or `card` uses it again. `card` needs an
NVIDIA card with its driver (no CUDA toolkit: `ck/gcheck6.ptx` is built for sm_75, so an RTX 20xx or newer, and is
loaded through the driver library at run time), 2.8 GB of card memory, about 28 GB of host memory and 12 host
threads; all modes need gcc, xz, sha256sum and python3.

**The plan.** The lift is deterministic: my first run (Windows, MinGW gcc, 16 threads, 2026-10-28) and a second one
(the same build, 12 threads, 2026-11-01) wrote the same file. That file was written on Windows, so its lines end in
CR LF, and its second line, a comment, names the path of the n = 17 plan on my machine. `check.sh plan` puts that
comment line and the CR LF line ends back before it takes the SHA-256; the program reads plans with either line end.
`check.sh plan 12` under Linux (Ubuntu 24.04 in WSL, gcc 13.3, 2026-11-01, 5.5 hours) rebuilt the plan from the
repository's n = 17 plan and printed `plan OK` with the hash of `COMMITMENT.md`.

**The check.** The exact group check of `recipes/n17/` keeps one bit per core, (n-3)! bits; for n = 18 that is 15!
bits, 163 GB, more than a card holds. Here the card keeps no set at all. A group (a 2-loop of the construction with a
fixed satellite letter; there are N = 16! = 20,922,789,888,000) is complete once all 18 * 17 of its members have been
seen among the windows of the word, and every completion of a group g adds r_k^g modulo p = 2^61 - 1 to four sums
k = 1..4. The word passes when there are exactly N completions and every sum equals 1 + r_k + ... + r_k^(N-1). If
some group is never completed, the N completions repeat other groups, and a sum still matches only if r_k is a root
of a nonzero polynomial of degree below N, which happens for at most N - 1 of the p - 3 possible keys (2 to p - 2). With four
independent keys a word that misses a group passes with probability at most ((N - 1)/(p - 3))^4 = 6.8e-21, provided
the keys are not known when the word is fixed.

So the keys come after the plan. [`COMMITMENT.md`](COMMITMENT.md) (commit 58ca221) fixes the SHA-256 of the plan and of the checker sources,
and names drand quicknet round 33475799, released at 2026-10-28 23:39:21 UTC, after that commit. The keys are
SHA-256 of the round's randomness, the plan hash and a counter (`drand_keys.py`); `drand/round33475799.json` is the
round as the drand API serves it (its signature can be checked against the quicknet public key, and anyone can fetch
the round again from any drand relay).

My run (2026-10-29 00:43 to 11-01 09:04, Windows, 12 host threads, RTX 5090, 289,217 seconds; `ck/mh6.c` built with
MinGW gcc 13.2, binary SHA-256 in `COMMITMENT.md`): valid, length 6,779,644,944,870,572,
6,403,021,543,900,800 permutation windows, 20,922,789,888,000 group completions, every sum equal to its expected
value, no overflow, tree hash and BLAKE3 as above. `check.sh card` compares all of these. The hash check agreed with
the exact check on the words for n = 16 and 17, and reported an n = 16 word with one group missing as incomplete.

Limits: this word is checked by one probabilistic run of one program. I have no exact check of it and no second
checker. The length also comes out of the lift and of `check.sh predict` (both from the construction, not from the
letters).

| file | what |
|---|---|
| `check.sh` | builds, checks the hashes, and runs `keys`, `plan`, `predict`, `card` or `all` |
| `COMMITMENT.md` | the hashes fixed before the drand round, and how the keys are made |
| `gen/liftB6.c` | the lift (`liftB6 lift 6 SEL PLAN17 OUT --threads T --chunk 32768`, env `GENB_BLOCK`) |
| `gen/genB6.c` | the generator with the block, L <= 6 (included by the two programs) |
| `ck/mh6.c`, `ck/gcard6.h` | the host threads and the card check (`mh6 6 SEL PLAN --threads T --mode hash --blake3 --seg 30 --table 24 --mhr R1,R2,R3,R4`, or `--predict`) |
| `ck/blake3.h` | BLAKE3 in C, the same file as `recipes/n17/blake3.h` |
| `ck/gcheck6.cu`, `ck/gcheck6.ptx` | the kernels and their PTX; `nvcc -arch=compute_75 -O3 -ptx -o gcheck6.ptx gcheck6.cu` |
| `drand_keys.py`, `drand/round33475799.json` | the keys from the drand round |
| `SHA256SUMS` | hashes of the files above |

The construction is Jay Pantone's (github.com/jaypantone/superperm-upper-43-80, Apache License 2.0). The code was
written with Claude in Claude Code.
