# A superpermutation on 16 symbols from selection C and a block (a recipe)

A word of 22,320,795,912,621 letters on the alphabet `0123456789ABCDEF` that contains all 20,922,789,888,000
permutations of 16 symbols, checked on a graphics card. SHA-256 of the word (no line feed):
`e16a7e7f92119f4713e0255cd2856a66dc63efd8e8f9c3c2b89dbd129cf4a61f`.

It is 34,178,619 letters below the value of the Lean theorem `hasWord_sixteen_B : HasWord 16 22320830091240`
(`proofs/lean/constant305989/SuperpermutationUpperBound305989/CorollariesB.lean`, described in
[`proofs/lean/constant305989/`](../../proofs/lean/constant305989/README.md)). The theorem says that a word of that
length exists, from a general formula; this recipe gives an explicit word that is shorter.

The word would take 22 TB, so it is not stored. `genBt.c` writes it from four things:

* the selection C on 11 symbols, the same file as for n = 14 (`arrange/data/n12t-selection.txt.xz` of this
  repository; `check.sh` checks the SHA-256 of its text,
  `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`);
* `proofs/lean/constant305989/data/s103_old2_0.txt`, the block of the Lean proof (SHA-256
  `6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618`): 6 closed walks of 880 rows and 440 loops
  without a row, solved once on 14 symbols;
* `nB16a_22320795912621.uplan.xz`, the unit plan (4.0 MB; 69,878,726 bytes unpacked, SHA-256 starting
  `999219c8513c45f0`): 4,266,432 lines, 2,661,120 small units and 1,605,312 walk units (line format below);
* `genBt.c`, the generator (C, standard library only). It is my generator for n = 12 + L (the one of `recipes/n14/`
  made general in L) for L = 4, with one change: the loops above each of the 6,048 loops without a row of C are not the transported selection but
  the block, relabelled onto that loop (letters A, B, C of the block become 10, 11, 12). This gives 36,288 stored
  walks after C's 3-lift; the next lift is made per walk. Small units exist only for the 440 loops of the block
  without a row.

The construction (slices, transport, completion, closed trails) is Jay Pantone's. The block step on top of it is
mine, proved in Lean in `proofs/lean/constant305989/`. The plan comes from my plan for n = 15 (lifted from the n = 14
plan of `recipes/n14/`; it is the plan of `recipes/n15/`, see [`tools/plans/`](../../tools/plans/README.md)): for each of the 6,048 positions, its 110 small units are replaced by the 440 small and 14 walk units of the block, in one fixed order, and
the openings are chosen again by an exact dynamic programme. The same plan lifted without the block has
22,320,835,819,119 letters, so the block saves 39,906,498. The plan has 15,619,232 letters in joins.

Plan lines: `D d g1 g2 g3 j` is a small unit (loop d without a row of C, in file order; letters 10, 11 and 12
inserted at g1, g2 and g3, which must be one of the block's 440 loops without a row; its 13 small trails cut at the
rotations j to j+12). `W w i0 way` is a walk unit (walk w, either a walk of C transported three times or a block
walk; cut at its full row i0, way 0 or 1).

## Checking

```sh
bash check.sh predict      # the length from the plan and the construction, no card; 4 threads, about 7 minutes
bash check.sh pass 0       # one of the four passes of the check on the card
bash check.sh core         # the whole check in one pass (builds coreBp from ../n17); about 25 minutes
bash check.sh all          # all four passes one after the other; about 80 minutes
bash check.sh sha          # the plain SHA-256 of the letters: one thread, several hours, no card
```

`pass` and `all` need an NVIDIA card with its driver (no CUDA toolkit: `gcheck17.ptx`, built for sm_75, so an RTX 20xx
or newer, is loaded through the driver library at run time), gcc, xz, 5 host threads and about 9 GB of memory (the
card's share included; the peak committed memory in my runs was 8.9 GB). One pass took 1,114 to 1,151 seconds on an
RTX 5090.

`genBp` does not keep a table of all 16! permutations. Every permutation belongs to one group (a 2-loop of the
construction with a fixed satellite letter), there are 14! = 87,178,291,200 groups, and a group's bit is set only
after all 16 * 15 of its members have been seen among the windows of the word. The word contains every permutation
exactly when all 14! bits are set. In a pass only the groups g with g mod 4 = I are recorded (21,794,572,800 bits,
2.7 GB), and the card scans every window of the word. The card spells the word from short descriptors made by the host
threads, so the 22 TB never exist anywhere. Its identity is a tree hash: the SHA-256 of the SHA-256 digests of its
64 KiB leaves. It is the same for every thread count and every shard, so the passes check the same word.

The word is a superpermutation exactly when all four passes are valid, complete in their shard (the four shards sum
to 14! groups), and report the same length and tree hash. My run (2026-10-26, RTX 5090, 5 host threads) gave for
all four passes: valid, length 22,320,795,912,621, 20,925,874,831,680 permutation windows, no overflow, no missing
permutation, tree hash `51e40627c9c9e378cc13256b71e2d730327b7f6e325a87decb4cf5727a32dd91`. `check.sh` compares these.

`check.sh core` runs the core-table check of [`recipes/n17/`](../n17/README.md) on the same word in one pass: valid, the same
length and tree hash, 6,227,020,800 cores complete, 1,477 seconds on the RTX 5090 with 5 host threads while another job used the card, 2.5 GB on the card.

As a negative test I removed one walk unit of the block from the plan (`W 1591470 143 1`) and ran pass 0 of 4: the
pass reported the word invalid, with 509,520 permutations missing. `genBp` also checks that the plan contains every
unit of the construction exactly once.

Limits: I have checked this word with one program only (the group check above, on the card, tested on smaller
words). The plain SHA-256 above comes from a separate run of `genBt plan 4 ... --count` (one thread, 25,962 seconds,
the same length), not from the card passes. I have no second checker for it yet.

| file | what |
|---|---|
| `check.sh` | builds, checks the hashes, and runs `predict`, `pass`, `all` or `sha` |
| `nB16a_22320795912621.uplan.xz` | the unit plan |
| `genBt.c` | the streaming generator with the block (`genBt plan 4 SEL PLAN --block FILE [--count]`) |
| `genBp.c`, `gcard17.h` | the host threads and the card check (`genBp 4 SEL PLAN --threads T --gshard I/K`) |
| `gcheck17.cu`, `gcheck17.ptx` | the kernels (spell, scan, harvest, leaf SHA-256) and their PTX; `nvcc -arch=compute_75 -O3 -ptx -o gcheck17.ptx gcheck17.cu` |
| `SHA256SUMS` | hashes of the files above |

The construction is Jay Pantone's (github.com/jaypantone/superperm-upper-43-80, Apache License 2.0). The code was
written with Claude in Claude Code.
