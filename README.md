# Short superpermutations on 8 and 10 to 14 symbols

A superpermutation on n symbols is a word that contains every permutation of the symbols as a substring. This
repository holds such words for n = 10, 11, 12, 13 and 14 that are shorter than any other I know of, and a word
of 46,174 letters for n = 8. The shortest word known for n = 8 is Theo H.'s 46,173, found with a program of
this repository on the same selection. The repository also holds the inputs from which the words can be rebuilt,
the programs that made them, and Lean proofs of upper and lower bounds.

All of it is built with Jay Pantone's
[43/80 construction](https://github.com/jaypantone/superperm-upper-43-80). Until October 5 I kept the closed
trails of his words and changed where each one is cut and the order in which the pieces are joined. The words
here use other selections inside his construction, and so other closed trails. The construction is Pantone's.

I work on this with Claude (Opus 5.5) in Claude Code. I chose the problem and direct the work; Claude designs and
runs the searches and writes the code and this text.

## The words

| n | length now | length before | previous record by | change |
|---|---:|---:|---|---:|
| 8 | 46,174 | 46,178 | William Echols | -4 |
| 10 | 4,034,855 | 4,034,873 | rumstd | -18 |
| 11 | 43,930,578 | 43,930,624 | Theo H. | -46 |
| 12 | 522,736,969 | 522,737,173 | Theo H. | -204 |
| 13 | 6,747,802,319 | 6,747,918,066 | Jay Pantone | -115,747 |
| 14 | 93,904,804,425 | 93,904,804,516 | William Echols | -91 |

"Before" is the best word of someone else when mine was published. For n = 8 Theo H. has since found a word of
46,173 letters on the same selection with `tools/trailsearch.c` ([`words/n8/`](words/n8/README.md)), so for n = 8
mine is no longer the shortest. Theo H.'s words for n = 11 and 12 were made from earlier words of mine. The word
for n = 12 starts from William Echols's 522,737,174, and it and the word for n = 13 use two moves from the group:
his re-opening of a stretch of consecutive trails and Theo H.'s moving of a trail with a new phase.

Against Pantone's own words of 4,034,889, 43,930,680, 522,745,581 and 6,747,918,066 letters the words for n = 10
to 13 are 34, 102, 8,612 and 115,747 letters shorter. My own best words on Pantone's closed trails, before the
change of selection, had 43,930,614, 522,745,350 and 6,747,916,657 letters.

The files are `words/superpermutation-N-LENGTH.txt.xz`, XZ archives with a delta filter of distance n that `xz -d`
unpacks: 2 KB for n = 8, then 65 KB, 0.4 MB, 4.1 MB and 45 MB for n = 10 to 13. They use the first n letters of
`0123456789ABC`, one line plus a line feed, as in Pantone's repository. [`SHA256SUMS`](SHA256SUMS) lists the hashes
of the archives and of the words inside. In each word every permutation occurs and no single letter can be
deleted. The word for n = 8 has its own page, [`words/n8/`](words/n8/README.md).

The word on 14 symbols would take 94 GB, so it is published as a recipe in [`recipes/n14/`](recipes/n14/README.md):
a generator, a plan of 83 KB and a checker, as William Echols did with his words.

SHA-256 of the words (each file is the word and one line feed; for n = 14 the word as `recipes/n14/` writes it,
with no line feed):

    n = 8    66ec57ba428e0ac1affc5503b86821920f0def27380697317033911a6628cddd
    n = 10   09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
    n = 11   65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092
    n = 12   48c00acf991d87a396fb162bc66447d9dba90ddc0ac9dca5ffed89e46597fcba
    n = 13   be150571be3c6dd6b0aeed2c7c394db7c1c0e5cd4e71be2c4ec9d4ec8b8bcf67
    n = 14   3b1470a204854ce09654b9d9a811b8455308212b29585accc29d0263e423ab6f

## The Lean proofs

[`proofs/lean/`](proofs/lean/README.md) holds proofs in Lean 4, stated with the definitions of Pantone's
`Challenge.lean`. In short:

* Upper bounds for every large n. Pantone proved S(n) <= F3(n) + (43/80 + o(1)) (n-3)!, with
  F3(n) = n! + (n-1)! + (n-2)!. The proofs here lower the coefficient, each from the n given:

  | c | decimal | from n | directory |
  |---|---:|---:|---|
  | 43/80, Pantone | 0.537500 | 11 | his repository |
  | 1771/3456 | 0.512442 | 13 | [`constant/`](proofs/lean/constant/README.md) |
  | 61937/120960 | 0.512045 | 13 | [`constant61937/`](proofs/lean/constant61937/README.md) |
  | 305989/604800 | 0.505934 | 16 | [`constant305989/`](proofs/lean/constant305989/README.md) |
  | 43586371/86486400 | 0.503968 | 19 | [`constant43586371/`](proofs/lean/constant43586371/README.md) |
  | 3961457/7862400 | 0.503848 | 19 | same |
  | 8711159/17297280 | 0.503614 | 19 | same |
  | 21751799/43243200 | 0.503011 | 22 | same |
  | 21736511/43243200 | 0.502657 | 22 | same |
  | 629507/1441440 | 0.436721 | 22 | same |
  | 3853/8736 | 0.441049 | 19 | same |
  | 11117297/27675648 | 0.401700 | 22 | same |

  From 61937/120960 on, each step chooses connector cycles again one level up, and from 305989/604800 on it puts a
  block of closed trails, chosen once and carried to every position by a relabelling, above the loops without a
  row. The later rows put a block above the loops of a block, and the last three leave out the selection on 11
  symbols. The construction is Pantone's.
* The coefficient can be made as small as one likes: for every eps > 0 there is an N such that for every n >= N
  a superpermutation on n symbols has at most F3(n) + eps (n-3)! letters (`Uniform.coefficient_tends_to_zero`;
  the N it gives is of the order of 2 * 10^6 / eps^7, so this is a statement about the limit). A finer family
  gives a rate: for every n >= 2^14 a superpermutation of length at most F3(n) + (9/n)(n-3)! (`UniR.rate_R`), and
  an exact bound for every n (`UniR.finite_boundR`) that is 0.110 (n-3)! above F3(n) at n = 100.
* With the lower bound of the Hunter-Raudvere library, [`proofs/lean/asym/`](proofs/lean/asym/README.md) turns this
  into statements about the shortest superpermutation, of length L(n): F3(n) <= L(n) for n >= 6, and
  (L(n) - F3(n)) / (n-3)! tends to 0. For n >= 2^14 the remainder L(n) - F3(n) lies between 2(n-4)! - 2(n-5)! and
  41/5 (n-4)! (`remainder_order8`), and in units of (n-4)! its limit inferior is at least 2 (Theorem B of
  `proofs/lean/lower/`) and its limit superior at most 8 (`remainder_limit8`). The comparator and the nanoda checker
  accepted `coefficient_tends_to_zero` and `shortest_superpermutation_coefficient`; they were not run on the rate
  and remainder theorems. The Hunter-Raudvere library is not copied; that README gives its address, the commit and
  the build steps.
* Words checked by the kernel on the words themselves: my 46,174 for n = 8 and its seven ties, 4,034,855 for
  n = 10, 43,930,578 for n = 11 and 522,737,175 for n = 12. For 522,736,969 the README of `proofs/lean/words12/`
  gives the command; that run has not been made.
* Lower bounds for every n >= 5, on top of Xiaolong Liu's preimage-chain library and the Hunter-Raudvere library.
  Theorem C gives 46,133, 408,469, 4,033,378, 43,917,903, 522,622,378, 6,746,626,957 and 93,891,141,126 letters for
  n = 8 to 14, all checked by the kernel with no `native_decide`. The value for n = 14 comes from a certificate that
  is a recipe of its own (61 hours of Lean time); the build levels of `proofs/lean/lower/` stop at 93,891,141,008.
* For n = 8 there are three proofs of different strength. William Echols's framework, taken further in
  [`proofs/lean/n8/`](proofs/lean/n8/README.md), gives 46,132 with no `native_decide`. Theorem C gives 46,133, also
  with no `native_decide`. [`proofs/lean/n8_46134/`](proofs/lean/n8_46134/README.md) gives 46,134 (Theorem D) with
  three equations evaluated by compiled code (`native_decide`), so that proof also trusts the Lean compiler, the C
  compiler of the toolchain and the runtime. [`proofs/lean/n8struct/`](proofs/lean/n8struct/README.md) proves the
  two facts about the selection of the 46,174 word that `words/n8/` states.
* A superpermutation on 7 symbols has at least 5,899 letters, one more than Justin Lebar's 5,898; the shortest word
  known has 5,905. The proof is in [`proofs/lean/n7/`](proofs/lean/n7/README.md). The kernel checks it down to 22
  equations, each of which says that a finite search finds nothing, and those 22 are evaluated by `native_decide`,
  as in Lebar's proof.

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

All three passed on each of the words for n = 8 and 10 to 13. For n = 13 `literal_check` ran under Linux: 22
minutes and about 13 GB. The word for n = 14 was checked by `recipes/n14/vfast.c` and by a second streaming
checker of mine with several threads; both found all 87,178,291,200 permutations. `decode.sh ... check` in
`recipes/n14/` gives the length and the SHA-256 of the plan's `# expect` line and finds all permutations (56
minutes on one thread, 11 GB).

## Rebuilding a word

Each word can be rebuilt from two small files: a selection, which says what the closed trails are, and a plan,
which lists the closed trails in order and says where each is cut. [`reproduce/`](reproduce/REPRODUCE.md) holds
both for the words of 4,034,855, 43,930,578, 522,737,175 and 6,747,802,393 letters, with a generator, a program
that writes the word of a plan and a list of the hashes to expect. It needs Python 3 and a C compiler and no
solver. The n = 10 word takes seconds, the n = 12 word about four minutes and 0.9 GB, the n = 13 word 40 minutes
and 2 GB of memory with 14 GB of disk.

The generator writes a base word, a superpermutation that holds every closed trail once. The tools of this
repository work on base words, so the same plan also rebuilds with the loader of the search programs:

```sh
cc -O2 -mpopcnt -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch BASE.txt rebuilt.txt --plan-in PLAN --time 0
```

The newest words for n = 12 and 13 are on the same base words as the ones in `reproduce/` (the base word of
`REPRODUCE.md` has the same SHA-256). Their plans are `plan/trailsearch-12-522736969.plan` and
`plan/trailsearch-13-6747802319.plan`, and they rebuild with the command above. The earlier words, on Pantone's
closed trails, rebuild the same way from Pantone's words and the plans in [`plan/`](plan/) and
[`plan/history/`](plan/history/README.md).

The word for n = 8 is rebuilt from its selection by [`words/n8/tools/n8.py`](words/n8/tools/README.md), which
finds the best order of its pieces with an integer programme. It needs Python 3 with numpy and scipy, whose solver
HiGHS takes about 3 seconds:

```sh
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt
```

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

Part two, other closed trails (October 5 to 7):

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

Part three, moves of William Echols and Theo H. (October 17 to 20):

11. Cut a block of consecutive closed trails again (Echols), or move one closed trail to another place in the
    order and choose its cut there (Theo H.), with all the cuts around the change chosen again by dynamic
    programming. For n = 12 I started from Echols's word and alternated these moves with the local search of part
    two: 522,736,969 letters, 206 below my 522,737,175. For n = 13 I started from my 6,747,802,393 word and added
    segment insertion with five cuts on the card: 6,747,802,319 letters, 74 below it. The programs for these
    moves are not in the repository yet; the plans are, and they rebuild with `tools/trailsearch.c`.
12. For n = 14 the word is written by a generator from the selection and a plan of 72,000 units, one per closed
    trail on 13 symbols, in the order that my n = 12 and n = 13 plans give: 93,904,804,425 letters, 91 below
    Echols's 93,904,804,516.

Part four, n = 8 (October 20):

13. A set partition over closed walk types packed the 120 loops with four copies of one walk of 27 loops. Priced
    with joins of every overlap, that packing gives 46,174 letters, four below Echols's 46,178. Theo H. then ran
    `tools/trailsearch.c` on the same selection and found 46,173, by opening three trails at steps of weight 2.

## What is in the repository

| path | content |
|---|---|
| `words/` | the words, and the earlier ones I published |
| `words/n8/` | the word on 8 symbols: how it is built, its selection and slice order, seven ties, what is known about it, and in [`tools/`](words/n8/tools/README.md) one program that rebuilds it, prices any selection and runs the search that found it |
| `recipes/n14/` | the word on 14 symbols as a recipe: generator, plan, checker, with its own [`README`](recipes/n14/README.md) |
| `ties/` | the words of the shortest known length for n = 7, 9 and 10 that I know, and the 46,181 words of the earlier record length for n = 8, with their own [`README`](ties/README.md): 85 new words of 5,905 letters, which published words are the same word, and the 1,223 words of 46,181 letters that rotating three closed paths gives |
| `reproduce/` | selection, plan, generator and checker for the words of 4,034,855, 43,930,578, 522,737,175 and 6,747,802,393 letters, with [`REPRODUCE.md`](reproduce/REPRODUCE.md) |
| `selection/` | how the selections were found: the block searches and their checkers |
| `arrange/` | how a set of closed trails becomes a first plan: chains, the order of the chains, the lift from n = 12 to n = 13, the n = 10 construction, the bounds |
| `tools/` | the C programs that shorten a plan, with their own [`README`](tools/README.md) (one line per program) and a test script |
| `plan/`, `plan/history/` | plans of the words: the newest for n = 12 and 13, and the earlier words |
| `proofs/n9/` | two scripts that check that 408,731 cannot be beaten at n = 9 with Pantone's closed trails, in three families of words |
| `proofs/lean/` | the Lean proofs above, with their own [`README`](proofs/lean/README.md), and one command that checks a word of your own |
| `NOTES.md` | the account of every step |
| `SHA256SUMS` | hashes of all archives, words and plans |
| `test.sh` | runs the small tests of every part (needs a clone of Pantone's repository; about 15 minutes on one thread) |

Rebuilding and checking a word needs a C compiler and Python and nothing else. Finding selections and first plans
uses integer programmes; the scripts in `selection/` and `arrange/` say which of them need a solver.
`bash tools/test.sh` builds the tools and runs short end-to-end checks at n = 10 and n = 11 with known lengths and
hashes. The C sources are formatted with clang-format and the [`.clang-format`](.clang-format) file here.

## Credits and licence

The construction is Jay Pantone's, and so are the terms: closed trail, slice, selection, completion, transport.
Cutting a closed trail between two 2-cycles comes from rumstd's n = 10 word, and so does the structure of the
n = 10 word here: groups of seven small trails as paths or loops, in chains of six. Cutting inside a 1-cycle is
Theo H.'s idea. The newest words for n = 12 and 13 start from William Echols's 522,737,174 for n = 12
(https://github.com/WilliamEchols/superpermutations, commit 3ba3bca) and from my word for n = 13, and use the move
types of Echols (cutting a block of closed trails again) and Theo H. (moving one closed trail and choosing its cut;
https://github.com/Tholsh/superpermutation_study, commit 2d1965f). The recipe form of the word for n = 14 is
Echols's. The shortest word for n = 8, 46,173, is Theo H.'s. In the Lean developments for the coefficients below
1771/3456 the cycle re-choice and the block step are mine. The lower bounds stand on Xiaolong Liu's preimage-chain
library and the Hunter-Raudvere library. Apache License 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)), the
same as the repository the construction comes from.
