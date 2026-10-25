# Short superpermutations on 8 and 10 to 14 symbols

[![check words](https://github.com/jhalfar/superpermutations/actions/workflows/check.yml/badge.svg)](https://github.com/jhalfar/superpermutations/actions/workflows/check.yml)

A superpermutation on n symbols is a word that contains every permutation of the symbols as a substring. This
repository holds such words for n = 10 to 14 that are shorter than any other I know of, and a word of 46,174
letters for n = 8. It also holds the inputs that rebuild them, the programs that made them, and Lean proofs of
upper and lower bounds.

All of it is built with Jay Pantone's [43/80 construction](https://github.com/jaypantone/superperm-upper-43-80).
Until October 5 I kept the closed trails of his words and changed where each one is cut and the order of the
pieces; the words here use other selections inside his construction, and so other closed trails.

I work on this with Claude (Opus 5.5) in Claude Code. I chose the problem and direct the work; Claude designs and
runs the searches and writes the code and this text.

## The words

| n | length now | length before | previous record by | change |
|---|---:|---:|---|---:|
| 8 | 46,174 | 46,178 | William Echols | -4 |
| 10 | 4,034,855 | 4,034,873 | rumstd | -18 |
| 11 | 43,930,578 | 43,930,624 | Theo H. | -46 |
| 12 | 522,736,969 | 522,737,173 | Theo H. | -204 |
| 13 | 6,747,801,798 | 6,747,918,066 | Jay Pantone | -116,268 |
| 14 | 93,904,804,425 | 93,904,804,516 | William Echols | -91 |

"Before" is the best word of someone else when mine was published. For n = 8 the shortest word known is now
Theo H.'s 46,173, which he found with `tools/trailsearch.c` of this repository on the same selection
([`words/n8/`](words/n8/README.md)). Theo H.'s words for n = 11 and 12 were made from earlier words of mine. The
word for n = 12 starts from William Echols's 522,737,174, and it and the word for n = 13 use two moves from the
group: his re-opening of a stretch of consecutive trails and Theo H.'s moving of a trail with a new phase.
Against Pantone's own words of 4,034,889, 43,930,680, 522,745,581 and 6,747,918,066 letters the words for n = 10 to
13 are 34, 102, 8,612 and 116,268 letters shorter. My own best words on Pantone's closed trails, before the change
of selection, had 43,930,614, 522,745,350 and 6,747,916,657 letters.

The files are `words/superpermutation-N-LENGTH.txt.xz`: XZ archives with a delta filter of distance n that `xz -d`
unpacks (2 KB for n = 8, then 65 KB, 0.4 MB, 4.1 MB and 45 MB for n = 10 to 13), on the first n letters of
`0123456789ABC`, one line plus a line feed, as in Pantone's repository. New words for n >= 13 are stored in Theo
H.'s [SPRA format](https://github.com/Tholsh/SPRA) (version 0.2, fields of 6 bits) and packed with `xz`:
`words/superpermutation-13-6747801798.spra.xz`, 1.26 MB. Its decoder is `tools/reduced_codec.cpp` of that
repository (`g++ -std=c++20 -O2 tools/reduced_codec.cpp -o reduced-codec`), which writes the letters `0`-`9`,
`A`-`C` with no line feed; I checked the file with it and with an independent decoder of mine. The word of
6,747,801,835 letters before it is stored the same way, and the earlier words for n = 13 stay as `.txt.xz`
files. The word on 14 symbols would take 94 GB, so it is a recipe in
[`recipes/n14/`](recipes/n14/README.md): a generator, a plan of 83 KB and a checker, as William Echols did with his
words.

```sh
xz -dk words/superpermutation-13-6747801798.spra.xz
./reduced-codec decode words/superpermutation-13-6747801798.spra > superpermutation-13-6747801798.txt
```

SHA-256 of the words (for n = 8 to 12 the file, which is the word and one line feed; for n = 13 the letters as the
decoder writes them and for n = 14 as `recipes/n14/` writes them, both with no line feed). [`SHA256SUMS`](SHA256SUMS)
has the hashes of every archive, word and plan.

    n = 8    66ec57ba428e0ac1affc5503b86821920f0def27380697317033911a6628cddd
    n = 10   09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
    n = 11   65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092
    n = 12   48c00acf991d87a396fb162bc66447d9dba90ddc0ac9dca5ffed89e46597fcba
    n = 13   272680a7668ae245a16a9b0e6bd8e4bdd90cb7bf67922a2d534deeff70c68232
    n = 14   3b1470a204854ce09654b9d9a811b8455308212b29585accc29d0263e423ab6f

How the words were found, step by step, is in [`NOTES.md`](NOTES.md).

## The Lean proofs

[`proofs/lean/`](proofs/lean/README.md) holds proofs in Lean 4, stated with the definitions of Pantone's
`Challenge.lean`. With F3(n) = n! + (n-1)! + (n-2)! and L(n) the length of the shortest superpermutation:

| result | checked by | directory |
|---|---|---|
| L(n) <= F3(n) + (c + o(1)) (n-3)! with c from 1771/3456 (n >= 13) down to 11117297/27675648 (n >= 22); Pantone's c is 43/80 | kernel | [`constant/`](proofs/lean/constant/README.md), [`constant61937/`](proofs/lean/constant61937/README.md), [`constant305989/`](proofs/lean/constant305989/README.md), [`constant43586371/`](proofs/lean/constant43586371/README.md) |
| the coefficient tends to 0; L(n) - F3(n) lies between 2(n-4)! - 2(n-5)! and 41/5 (n-4)! for n >= 2^14 | kernel | [`constant43586371/`](proofs/lean/constant43586371/README.md), [`asym/`](proofs/lean/asym/README.md) |
| my words of 46,174 (and its seven ties), 4,034,855, 43,930,578 and 522,737,175 letters are superpermutations | kernel | [`words/`](proofs/lean/words/README.md), [`words12/`](proofs/lean/words12/README.md) |
| L(n) >= 46,133, 408,469, 4,033,378, 43,917,903, 522,622,378, 6,746,626,957, 93,891,141,126 for n = 8 to 14 (Theorem C) | kernel | [`lower/`](proofs/lean/lower/README.md) |
| L(n) exact for n <= 6: 1, 3, 9, 33, 153, 872; L(6) = 872 kernel-only, as far as I know the first such proof | kernel | [`small/`](proofs/lean/small/README.md) |
| L(8) >= 46,132 in William Echols's framework, without his `native_decide` | kernel | [`n8/`](proofs/lean/n8/README.md) |
| L(8) >= 46,134 (Theorem D) | kernel and 3 equations by `native_decide` | [`n8_46134/`](proofs/lean/n8_46134/README.md) |
| L(7) >= 5,899, one more than Justin Lebar's 5,898 | kernel and 22 equations by `native_decide` | [`n7/`](proofs/lean/n7/README.md) |
| L(7) >= 5,900 | kernel and 99 equations by `native_decide` | [`n7_5900/`](proofs/lean/n7_5900/README.md) |
| L(7) >= 5,901: the reduction to 30 search equations, 6 of them evaluated | kernel, and 6 equations by `native_decide` | [`n7_5901/`](proofs/lean/n7_5901/README.md) |
| the 27-walk and the packing of four copies behind the 46,174 word | kernel | [`n8struct/`](proofs/lean/n8struct/README.md) |

"Kernel" means checked by the Lean kernel to the end with the axioms `propext`, `Classical.choice` and `Quot.sound`
only. Where equations are evaluated by `native_decide`, the Lean compiler, the C compiler of the toolchain and the
runtime are trusted for them, as in Lebar's proof. L(7) >= 5,901 as a whole is a computer-assisted proof, not a
Lean theorem: the 24 search equations that Lean has not evaluated rest on C, C++ and CUDA programs, most of them
run by one program only. [`proofs/n7_5901/`](proofs/n7_5901/README.md) has the written proof, the programs and
a table that gives the trust level of each of the 30 searches. [`proofs/lean/README.md`](proofs/lean/README.md) has the
statements, the trust levels, the builds and what they cost.

## Checking a word

```sh
cc -O2 -mpopcnt -fopenmp -o delcheck tools/delcheck.c
xz -dk words/superpermutation-11-43930578.txt.xz && ./delcheck words/superpermutation-11-43930578.txt
```

[`tools/delcheck.c`](tools/delcheck.c) must print `"missing_permutations":0` and
`"coverage_preserving_deletions_count":0`: every permutation occurs and no single letter can be deleted (1.6 GB and
about two minutes on 8 threads at n = 13). Two more programs that share no code with it check the same:
[`reproduce/tools/check_min.py`](reproduce/tools/check_min.py) (every permutation occurs; about 60 lines of Python
with numpy) and Pantone's `literal_check --deletions` (about 13 GB at n = 13). All three passed on each word for
n = 8 and 10 to 13; for n = 13 `literal_check` ran under Linux in 15 minutes. Before I publish a word,
`tools/trailsearch.c` runs on its plan with six settings (20 minutes each at n = 13) and the fixed-order pass; the
word goes out only if neither shortens it. The word for n = 14 is checked by `recipes/n14/decode.sh ... check`
(56 minutes on one thread, 11 GB) and was checked by a second streaming checker of mine with several threads;
both found all 87,178,291,200 permutations.

## Rebuilding a word

Each word rebuilds from a selection (what the closed trails are) and a plan (their order and cuts).
[`reproduce/`](reproduce/REPRODUCE.md) holds both for the words of 4,034,855, 43,930,578, 522,737,175 and
6,747,802,393 letters, with a generator and the hashes to expect: Python 3 and a C compiler, no solver. The newest
words for n = 12 and 13 are on the same base words; their plans are `plan/trailsearch-12-522736969.plan` and
`plan/trailsearch-13-6747801798.plan` (and `plan/trailsearch-13-6747801835.plan` and
`plan/trailsearch-13-6747802319.plan` for the words before), and the
earlier words on Pantone's closed trails rebuild from his words and the plans in [`plan/`](plan/) and
[`plan/history/`](plan/history/README.md):

```sh
cc -O2 -mpopcnt -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch BASE.txt rebuilt.txt --plan-in PLAN --time 0
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt    # n = 8, HiGHS, about 3 s
```

## Where things are

| path | content |
|---|---|
| [`words/`](words/) | the words, and the earlier ones I published |
| [`words/n8/`](words/n8/README.md) | the word on 8 symbols: construction, selection, slice order, seven ties, and in [`tools/`](words/n8/tools/README.md) the program that rebuilds, prices and searches |
| [`recipes/n14/`](recipes/n14/README.md) | the word on 14 symbols as a recipe: generator, plan, checker |
| [`reproduce/`](reproduce/REPRODUCE.md) | selection, plan, generator and checker for four words |
| [`plan/`](plan/), [`plan/history/`](plan/history/README.md) | plans of the newest and of the earlier words |
| [`selection/`](selection/README.md) | how the selections were found: block searches and their checkers |
| [`arrange/`](arrange/README.md) | how closed trails become a first plan: chains, their order, the lift from 12 to 13, the n = 10 construction, bounds |
| [`tools/`](tools/README.md) | the C programs that shorten a plan, one line per program, and their tests |
| [`ties/`](ties/README.md) | the words of the shortest known length for n = 7, 9 and 10 and of the earlier record length 46,181 for n = 8: 85 new words of 5,905 letters, which published words are the same, 1,223 rotations at n = 8 |
| [`proofs/n7_5901/`](proofs/n7_5901/README.md) | L(7) >= 5,901: the written proof, the search programs, Table C, the trust level of every search |
| [`proofs/n9/`](proofs/n9/README.md) | 408,731 cannot be beaten at n = 9 with Pantone's closed trails, in three families of words |
| [`proofs/lean/`](proofs/lean/README.md) | the Lean proofs, and one command that checks a word of your own |
| [`catalogue/`](catalogue/CATALOGUE.md) | every result with its status, evidence and the command that reruns it ([`schema.md`](catalogue/schema.md)) |
| [`NOTES.md`](NOTES.md) | the account of every step |
| [`SHA256SUMS`](SHA256SUMS) | hashes of all archives, words and plans |
| [`.github/workflows/`](.github/workflows/) | `check.yml`: the checker of [superpermutations-bot](https://github.com/jhalfar/superpermutations-bot) on every changed word and recipe, and on all of them once a week; `release.yml`: on a tag `words-*`, every word as a checked `.spra.xz` in a GitHub release |
| `test.sh` | the small tests of every part, catalogue included: `bash test.sh PANTONE_REPO` (about 15 minutes on one thread) |

Rebuilding and checking a word needs a C compiler and Python and nothing else. Finding selections and first plans
uses integer programmes; `selection/` and `arrange/` say which need a solver. The C sources follow
[`.clang-format`](.clang-format).

## Credits and licence

The construction is Jay Pantone's, and so are the terms closed trail, slice, selection, completion and transport.
Cutting a closed trail between two 2-cycles and the structure of the n = 10 word come from rumstd's n = 10 word.
Cutting inside a 1-cycle is Theo H.'s idea, and so are the shortest word for n = 8 and the SPRA format. The moves
behind the words for n = 12 and 13 are William Echols's and Theo H.'s, and the recipe form for n = 14 is Echols's.
The lower bounds stand on Xiaolong Liu's preimage-chain library and the Hunter-Raudvere library.
[`NOTICE`](NOTICE) has the details and the commits. Apache License 2.0 (see [`LICENSE`](LICENSE)), the same as the
repository the construction comes from.
