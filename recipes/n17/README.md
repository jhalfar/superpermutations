# A superpermutation on 17 symbols from selection C and a block (a recipe)

A word of 377,961,971,839,096 letters on the alphabet `0123456789ABCDEFG` that contains all
355,687,428,096,000 permutations of 17 symbols, checked on a graphics card in one pass. Tree hash of the word (the
SHA-256 of the SHA-256 digests of its 64 KiB leaves):
`a17d292c31673102f3c18fa152317e81119320fb89d11815f9be6a59bdf425b2`. The plain SHA-256 of the letters is not known
yet: the run that computes it takes about 4.4 days, and I will add it here when it has finished.

It is 520,219,328 letters below the value of the Lean theorem `hasWord_seventeen_B : HasWord 17 377962492058424`
(`proofs/lean/constant305989/SuperpermutationUpperBound305989/CorollariesB.lean`, described in
[`proofs/lean/constant305989/`](../../proofs/lean/constant305989/README.md)). The theorem says that a word of that
length exists, from a general formula; this recipe gives an explicit word that is shorter.

The word would take 378 TB, so it is not stored. `genBt.c` writes it from four things, as for n = 16
([`recipes/n16/`](../n16/README.md)), with L = 5 instead of L = 4:

* the selection C on 11 symbols, the same file as for n = 14 (`arrange/data/n12t-selection.txt.xz` of this
  repository; `check.sh` checks the SHA-256 of its text,
  `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`);
* `proofs/lean/constant305989/data/s103_old2_0.txt`, the block of the Lean proof (SHA-256
  `6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618`);
* `nB17a_377961971839096.uplan.xz`, the unit plan (47.9 MB; 1,010,845,328 bytes unpacked, SHA-256 starting
  `5253c2c6877bea60`): 55,463,616 lines, 34,594,560 small units and 20,869,056 walk units (line format as for n = 16);
* `genBt.c`, the generator (C, standard library only). It is the same file as `recipes/n16/genBt.c`. The 3-lift is
  stored and the 4-lift and 5-lift are made walk by walk.

The construction (slices, transport, completion, closed trails) is Jay Pantone's. The block step on top of it is
mine, proved in Lean in `proofs/lean/constant305989/`. The plan is the n = 16 plan of `recipes/n16/` lifted once more:
every closed trail of that word is one unit here, in the same order, and the openings are chosen again by an exact
dynamic programme. The plan has 148,379,498 letters in joins.

## Checking

```sh
bash check.sh predict      # the length from the plan and the construction, no card; 4 threads, about 35 minutes
bash check.sh core         # one pass of the check on the card: about 3.8 hours
bash check.sh pass 0       # one of the eight passes of the older group check
bash check.sh all          # all eight passes one after the other
bash check.sh sha          # the plain SHA-256 of the letters: one thread, about 4.4 days, no card
```

`core`, `pass` and `all` need an NVIDIA card with its driver (no CUDA toolkit: the `.ptx` files are built for sm_75, so
an RTX 20xx or newer, and are loaded through the driver library at run time), gcc, xz and 12 host threads.

The check is the group check of `recipes/n16/`: every permutation belongs to one group (a 2-loop of the
construction with a fixed satellite letter), there are 15! = 1,307,674,368,000 groups, and a group is complete after
all 17 * 16 of its members have been seen among the windows of the word. In `core` mode the card keeps one bit per
core instead of one per group. A core is the group with its largest letter taken out; it has 14! = 87,178,291,200 values, and each core has 15
groups, one for every place of that letter. A core bit is set only when all 15 of its groups are complete. The map
from a group to its (core, place) is computed from the permutation alone, so the check does not depend on the plan or
on the construction. All 14! core bits set means all 15! groups are complete, so all 17! permutations occur. This needs
12.25 GB on the card in one pass (13.3 GB free before the start) and 6.3 GB of host memory, instead of 21.7 GB for each
of eight shard passes. The card spells the word from short descriptors made by the host threads, so the 378 TB
never exist anywhere. The tree hash is the same for every thread count, so it names the word that was checked.

My run (2026-10-26, WSL, 12 host threads, RTX 5090, 13,701 seconds): valid, length 377,961,971,839,096,
355,730,617,307,520 permutation windows, 1,307,674,368,000 groups complete, 87,178,291,200 cores done, no
overflow, no missing permutation, tree hash as above. `check.sh core` compares these. The same program gave for the
n = 16 word of `recipes/n16/`, in one pass, the same length and tree hash as the four shard passes there. I tested the core check against the older one on the words for n = 13 to 16, and with words
that miss permutations on purpose; both gave the same missing counts.

The `pass` and `all` modes build `../n16/genBp.c` with L = 5. I ran that code on the n = 17 word from the default
plan of the construction (eight passes, 2.7 to 3.3 hours each), not on this word.

Limits: I have checked this word with one program only (the group check on the card, in its core form, tested on
smaller words). I have no second checker for it, and no plain SHA-256 yet.

| file | what |
|---|---|
| `check.sh` | builds, checks the hashes, and runs `predict`, `core`, `pass`, `all` or `sha` |
| `nB17a_377961971839096.uplan.xz` | the unit plan |
| `genBt.c` | the streaming generator with the block (`genBt plan 5 SEL PLAN --block FILE [--count]`) |
| `coreBp.c`, `gcardc.h` | the host threads and the card check with the core table (`coreBp 5 SEL PLAN --threads T --seg 29 --table 22`) |
| `gcheckc.cu`, `gcheckc.ptx` | the kernels and their PTX; `nvcc -arch=compute_75 -O3 -ptx -o gcheckc.ptx gcheckc.cu` |
| `SHA256SUMS` | hashes of the files above |

How the plan was made from the plan for n = 16 is in [`tools/plans/`](../../tools/plans/README.md). The construction is Jay
Pantone's (github.com/jaypantone/superperm-upper-43-80, Apache License 2.0). The code was written with Claude in
Claude Code.
