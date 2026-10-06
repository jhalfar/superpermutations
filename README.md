# Shorter superpermutations on 10, 11, 12 and 13 symbols

A superpermutation on n symbols is a word that contains every permutation of the symbols as a substring. This
repository holds four such words, for n = 10, 11, 12 and 13, that are shorter than any other I know of. It also
holds the inputs from which each word can be rebuilt and the programs that made them.

All of it is built with Jay Pantone's
[43/80 construction](https://github.com/jaypantone/superperm-upper-43-80). Until October 5 I kept the closed
trails of his words and changed where each one is cut and the order in which the pieces are joined. The four words
here use other selections inside his construction, and so other closed trails. The construction is Pantone's.

I work on this with Claude (Opus 5.5) in Claude Code. I chose the problem and direct the work; Claude designs and
runs the searches and writes the code and this text.

## The words

| n | length now | length before | previous record by | change |
|---|---:|---:|---|---:|
| 10 | 4,034,855 | 4,034,873 | rumstd | -18 |
| 11 | 43,930,578 | 43,930,624 | Theo H. | -46 |
| 12 | 522,737,175 | 522,745,531 | Theo H. | -8,356 |
| 13 | 6,747,802,562 | 6,747,918,066 | Jay Pantone | -115,504 |

"Before" is the best word of someone else. Theo H.'s two words were made from earlier words of mine. Against
Pantone's own words of 4,034,889, 43,930,680, 522,745,581 and 6,747,918,066 letters the four words are 34,
102, 8,406 and 115,504 letters shorter. My own best words on Pantone's closed trails, before the change
of selection, had 43,930,614, 522,745,350 and 6,747,916,657 letters.

The files are `words/superpermutation-N-LENGTH.txt.xz`, XZ archives with a delta filter of distance n that `xz -d`
unpacks: 65 KB, 0.4 MB, 3.9 MB and 45 MB. They use the alphabet `0123456789ABC`, one line plus a line feed, as in
Pantone's repository. [`SHA256SUMS`](SHA256SUMS) lists the hashes of the archives and of the words inside. In each
word every permutation occurs and no single letter can be deleted.

## Checking a word

Three programs that share no code check the words:

* [`reproduce/tools/check_min.py`](reproduce/tools/check_min.py): every permutation occurs. About 60 lines of
  Python with numpy.
* [`tools/delcheck.c`](tools/delcheck.c): every permutation occurs and no single letter can be deleted. 1.6 GB and
  about two minutes on 8 threads at n = 13.
* Pantone's `literal_check --deletions` from his repository: the same two statements. At n = 13 it needs about
  13 GB.

```sh
cc -O2 -mpopcnt -fopenmp -o delcheck tools/delcheck.c
xz -dk words/superpermutation-11-43930578.txt.xz
./delcheck words/superpermutation-11-43930578.txt
```

`delcheck` must print `"missing_permutations":0` and `"coverage_preserving_deletions_count":0`.

All three passed on each of the four words. For n = 13 `literal_check` ran under Linux: 20 minutes and about
13 GB.

SHA-256 of the four words:

    n = 10   09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
    n = 11   65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092
    n = 12   97ab1d7c37f1a19f9c9c10d8109382f501da1982f1b66bfa1ddd2511f9149cde
    n = 13   abe18ff6c25eb7becb05e3009d2245c946fd85e9cb07821baa1d2a7dd7e2f056

## Rebuilding a word

Each word can be rebuilt from two small files: a selection, which says what the closed trails are, and a plan,
which lists the closed trails in order and says where each is cut. [`reproduce/`](reproduce/REPRODUCE.md) holds
both for the four words. With them come a generator, a program that writes the word of a plan and a list of the
hashes to expect. It needs Python 3 and a C compiler and no solver. The n = 10 word takes seconds, the n = 12 word
about four minutes and 0.9 GB, the n = 13 word 40 minutes and 2 GB of memory with 14 GB of disk.

The generator writes a base word, a superpermutation that holds every closed trail once. The tools of this
repository work on base words, so the same plan also rebuilds with the loader of the search programs:

```sh
cc -O2 -mpopcnt -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch BASE.txt rebuilt.txt --plan-in PLAN --time 0
```

The earlier words, on Pantone's closed trails, rebuild the same way from Pantone's words and the plans in
[`plan/`](plan/) and [`plan/history/`](plan/history/README.md).

## How the words were found

[`NOTES.md`](NOTES.md) is the full account: every step in order with the lengths before and after for each n,
what it cost, which program does it, what I tried that gave nothing, and what is known about how much is left.
In short:

Part one, on Pantone's closed trails (October 2 to 5):

1. Reordering runs of pieces by a travelling salesman model: 6 letters at n = 11, 8 at n = 13.
2. Cutting closed trails open between two 2-cycles, as rumstd's n = 10 word does, in a local search over all
   trails and cuts: 46, 44 and 71 letters at n = 11, 12 and 13.
3. All cuts at once for a fixed order, by dynamic programming: 3, 6 and 17 letters. Theo H. found the same pass
   independently. Cuts inside a 1-cycle, his idea, gave one more letter at n = 12.
4. Moves that change the order and are judged with all cuts free: relocation, loop moves and segment insertion,
   which with three cuts is a 3-opt move without reversal. These gave the rest: in all 66, 231 and 1,409 letters
   below Pantone's words.

Part two, other closed trails (October 5 and 6):

5. The closed trails come from a selection. Pantone's selection on 8 symbols leaves 48 loops without a row, and at
   every later level each loop above them gives a small closed trail of its own. These loops form 48 blocks that
   can be solved again on their own. A better solution of the block gives fewer closed trails: 7,200 instead of
   25,200 at n = 12, and with rows of other lengths 3,648, and 23,808 instead of 252,000 at n = 13.
6. The small closed trails have to be written in chains, and the order of the chains comes from integer programmes
   where local search does not find it. The pieces of the final words with such a first plan, before any search,
   were 5,411 letters below my best word of part one at n = 12 and 109,575 at n = 13.
7. Segment insertion with three cuts on these plans: 1,678 and 2,195 letters.
8. On these pieces a round of segment insertion has tens of thousands of moves that keep the length. Taking some
   of them in every round keeps the search going: 866 and 2,325 letters. Local kicks, a small change and its
   repair, then gave 220 more at n = 12.
9. At n = 11 the new pieces pay off only after the same passes: 36 letters below my best word of part one, most
   of the last ones from local kicks.
10. For n = 10 the word is constructed: the pieces of a selection with two closed walks where Pantone's has four,
    in the order of rumstd's word, with every cut chosen exactly. It is 18 letters below his.

## What is in the repository

| path | content |
|---|---|
| `words/` | the four words, and the earlier ones I published |
| `reproduce/` | selection, plan, generator and checker for each of the four words, with [`REPRODUCE.md`](reproduce/REPRODUCE.md) |
| `selection/` | how the selections were found: the block searches and their checkers |
| `arrange/` | how a set of closed trails becomes a first plan: chains, the order of the chains, the lift from n = 12 to n = 13, the n = 10 construction, the bounds |
| `tools/` | the C programs that shorten a plan, with their own [`README`](tools/README.md) and a test script |
| `plan/`, `plan/history/` | plans of the earlier words |
| `proofs/n9/` | two scripts that check that 408,731 cannot be beaten at n = 9 with Pantone's closed trails, in three families of words |
| `NOTES.md` | the account of every step |
| `SHA256SUMS` | hashes of all archives, words and plans |

The programs in `tools/`:

| program | what it does |
|---|---|
| `trailsearch.c` | local search over trails and cuts; rebuilds a word from a base word and a plan |
| `recut.c` | the best cut of every trail at once for the order as it is |
| `relocate.c`, `loopscan.c` | relocation and loop moves |
| `segins.c` | segment insertion on the CPU; made the words on Pantone's closed trails |
| `segins_gpu.c`, `segins_kern.cu` | segment insertion for long words: tables kept between rounds, candidates judged on an NVIDIA card, moves of equal length, bounded memory |
| `segins_ils.c` | local kicks: a small move, a local repair, keep if shorter or equal |
| `trailsearch_gpu.c`, `kern.cu` | the search on a card, with block moves |
| `recut_wide.c`, `kern_wide.cu` | the fixed-order pass with cuts inside a 1-cycle (experimental) |
| `word2plan.c` | writes any word of the same trails as a plan |
| `delcheck.c`, `letter.c`, `verify.c`, `verify_par.c` | checks |
| `polish.sh`, `rounds.sh`, `kick.sh`, `mkptx.sh`, `xzpar.sh`, `test.sh` | scripts that run them, build the kernels, pack words and test everything |
| `pieces.c`, `assemble.c`, `runjoin.py`, `connector_splice.py` | step 1 and the first Python search (`runjoin.py` needs Gurobi with a full licence) |

Rebuilding and checking a word needs a C compiler and Python and nothing else. Finding selections and first plans
uses integer programmes; the scripts in `selection/` and `arrange/` say which of them need a solver.
`bash tools/test.sh` builds everything and runs short end-to-end checks at n = 10 and n = 11 with known lengths and
hashes. The C sources are formatted with clang-format and the [`.clang-format`](.clang-format) file here.

## Credits and licence

The construction is Jay Pantone's, and so are the terms: closed trail, slice, selection, completion, transport.
Cutting a closed trail between two 2-cycles comes from rumstd's n = 10 word, and so does the structure of the
n = 10 word here: groups of seven small trails as paths or loops, in chains of six. Cutting inside a 1-cycle is
Theo H.'s idea. Apache License 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)), the same as the repository
the construction comes from.
