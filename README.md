# Short superpermutations on 8 and 10 to 18 symbols

[![check words](https://github.com/jhalfar/superpermutations/actions/workflows/check.yml/badge.svg)](https://github.com/jhalfar/superpermutations/actions/workflows/check.yml)

A superpermutation on n symbols is a word that contains every permutation of the symbols as a substring. This
repository holds superpermutations for n = 8 and 10 to 18, built with Jay Pantone's construction, and the list of
all 45,116 minimal superpermutations for n = 6 ([`words/n6/`](words/n6/README.md)). On 14 November 2026 the words
for n = 10 to 14 were the shortest known, and for n = 8 a shorter word has been found since, on the selection of
the word here. The current records are on the [Superpermutation Almanac](https://superpermutations.com). The
Almanac stops at n = 14; for n = 15 to 18 these were the shortest words I knew of on 14 November 2026. The repository also holds the inputs that rebuild the
words, the programs that made them, and Lean proofs of upper and lower bounds.

All of it is built with Jay Pantone's [43/80 construction](https://github.com/jaypantone/superperm-upper-43-80).
Until October 5 I kept the closed trails of his words and changed where each one is cut and the order of the
pieces; the words here use other selections inside his construction, and so other closed trails.

I work on this with Claude (Opus 5.5) in Claude Code. I chose the problem and direct the work; Claude designs and
runs the searches and writes the code and this text.

## Records, bounds and proofs today

The records and bounds for n up to 14 are kept on Jay Pantone's
[Superpermutation Almanac](https://superpermutations.com), which checks every word and Lean proof submitted to it.
Its front page has the current records, and its [bounds page](https://superpermutations.com/bounds) every listed
bound. My words there are listed in the table below with their Almanac numbers. This repository keeps what the
Almanac does not hold: the words for n = 15 to 18 (as recipes), the list of all minimal words for n = 6, the older
words and their plans, the programs that made them, the full Lean development, the written proofs of
$`L(7) \ge 5{,}900`$ and $`5{,}901`$, and the account in [`NOTES.md`](NOTES.md).

My Lean proofs on the Almanac are in
[jhalfar/superpermutation-almanac-lean](https://github.com/jhalfar/superpermutation-almanac-lean), one commit per
batch, each a cut-down copy of a part of [`proofs/lean/`](proofs/lean/README.md):

| commit | statement | Almanac |
|---|---|---|
| `af99e83` | the coefficient of $`(n-3)!`$ tends to 0, and the coefficient of $`(n-4)!`$ is at most 8, kernel only | [b/35](https://superpermutations.com/b/35), [b/36](https://superpermutations.com/b/36) |
| `7e6664d` | $`L(8) \ge 46{,}134`$, three searches by `native_decide` | [b/39](https://superpermutations.com/b/39) |
| `7b7b96d` | $`L(6) \ge 872`$, kernel only | [b/37](https://superpermutations.com/b/37) |
| `a09f9ef` | $`L(7) \ge 5{,}899`$, twelve searches by `native_decide` | [b/40](https://superpermutations.com/b/40) |
| `5cc0ac3` | $`L(7) \ge 5{,}898`$, kernel only | [b/43](https://superpermutations.com/b/43) |
| `7ed009a` | $`L(12) \ge 522{,}622{,}401`$ and $`L(13) \ge 6{,}746{,}627{,}048`$, kernel only (constants tuned as William Echols did for n = 11) | [b/46](https://superpermutations.com/b/46), [b/47](https://superpermutations.com/b/47) |

## The words

| n | my word here | on the Almanac | shortest known on 18 November 2026 |
|---|---:|---|---|
| 8 | 46,174 | [W-0077](https://superpermutations.com/w/W-0077) | 46,173, Theo H. ([W-0078](https://superpermutations.com/w/W-0078)), found with `tools/trailsearch.c` on the selection of this word; Jay Pantone found another word of that length ([W-0080](https://superpermutations.com/w/W-0080)) |
| 9 | not here | [W-0103](https://superpermutations.com/w/W-0103), 408,717 | 408,717, mine ([W-0103](https://superpermutations.com/w/W-0103)), from Jay Pantone's construction of [W-0099](https://superpermutations.com/w/W-0099) |
| 10 | 4,034,855 | [W-0062](https://superpermutations.com/w/W-0062) | the same; Jay Pantone's [W-0082](https://superpermutations.com/w/W-0082) has the same length |
| 11 | 43,930,534 | [W-0086](https://superpermutations.com/w/W-0086) | the same |
| 12 | 522,736,428 | [W-0113](https://superpermutations.com/w/W-0113) | this one, from William Echols's [W-0091](https://superpermutations.com/w/W-0091) |
| 12 | 522,736,431 | [W-0112](https://superpermutations.com/w/W-0112) | 522,736,428 (row above); this one is from Derek Mahoney's [W-0102](https://superpermutations.com/w/W-0102) |
| 13 | 6,747,800,155 | [W-0114](https://superpermutations.com/w/W-0114) | this one, from Jay Pantone's [W-0100](https://superpermutations.com/w/W-0100) with his reorder of [W-0107](https://superpermutations.com/w/W-0107) |
| 14 | 93,904,778,043 | [W-0115](https://superpermutations.com/w/W-0115) | this one, from Jay Pantone's [W-0108](https://superpermutations.com/w/W-0108) |
| 15 | 1,401,325,411,491 | the Almanac stops at n = 14 | 1,401,325,411,389, Derek Mahoney ([his repository](https://github.com/dmahoney1213/superperm-words)), from this word's plan with `uopt15` |
| 16 | 22,320,795,912,621 | | 22,320,795,905,601, Derek Mahoney ([his repository](https://github.com/dmahoney1213/superperm-words)), the same construction run again from an n = 15 plan |
| 17 | 377,961,971,839,096 | | this one, as far as I know |
| 18 | 6,779,644,944,870,572 | | this one, as far as I know |

The word for n = 14 is stored in the Almanac's Detour format and the words for n = 15 to 18 as recipes (below).
My earlier words for n = 12 to 14 stay in the repository: 522,736,969
([W-0074](https://superpermutations.com/w/W-0074)), 6,747,801,798 ([W-0084](https://superpermutations.com/w/W-0084))
and 93,904,804,405 ([W-0085](https://superpermutations.com/w/W-0085), the recipe in
[`recipes/n14/`](recipes/n14/README.md)). Three of my words on the Almanac are not in this repository: 408,717 for
n = 9 ([W-0103](https://superpermutations.com/w/W-0103)), 522,736,440 for n = 12
([W-0098](https://superpermutations.com/w/W-0098)) and 6,747,800,688 for n = 13
([W-0105](https://superpermutations.com/w/W-0105)); for n = 12 and 13 the words here are shorter. The Almanac's
front page is the current table; the lengths these words beat when they were published are in
[`NOTES.md`](NOTES.md#the-words-and-the-records-they-beat).

The word for n = 11 starts from Jay Pantone's 43,930,548 ([W-0079](https://superpermutations.com/w/W-0079)), which
he made from my selection X by changing the images of its blocks; I recovered his images, changed two of them and
repaired the order with local kicks ([`plan/images-11-43930534.txt`](plan/images-11-43930534.txt)).

The words of November for n = 12 to 14 start from words of others on the Almanac. Three of them use Jay Pantone's
cut-opening reorder, which he described with W-0107: cut the word at its heavy steps, open the light cuts around a
few joins at a time and solve the best order of the pieces exactly. My rebuild of it is
[`tools/reorder/`](tools/reorder/README.md).

* 522,736,431 for n = 12 starts from Derek Mahoney's W-0102 (522,736,437). The reorder gave 434, `tools/trailsearch.c`
  433, and segment insertion on the card ([`tools/gpucuts/`](tools/gpucuts/README.md)) 431.
* 522,736,428 for n = 12 starts from William Echols's W-0091 (522,736,503) and does not use the reorder. The
  scheduler in [`foreman/`](foreman/README.md) ran trailsearch, segment insertion on the card and local search on
  it in turns until 522,736,429 ([`foreman/recipe/RECIPE.md`](foreman/recipe/RECIPE.md) lists every step), and one
  more trailsearch in the check before publication gave 428.
* 6,747,800,155 for n = 13 starts from my 6,747,800,734, which I made from Jay Pantone's W-0100. The reorder alternated with
  segment insertion on the card (three cuts, slack 0 and 1), trailsearch and long runs of `tools/loopscan.c` down to
  6,747,800,301; then four and five cuts on the card gave 297 and 268. Two more rounds of the reorder, each followed by
  the same steps with four and five cuts added, gave 230, 221, 190, 174, 170 and 163, and one more reorder gave 155.
* 93,904,778,043 for n = 14 starts from Jay Pantone's W-0108 (93,904,780,410). The reorder on a contracted model
  (`--chain 1`) gave 93,904,778,044, and `gdelcheck` ([`tools/gpucheck/`](tools/gpucheck/README.md)) found one
  letter that could be deleted.

The earlier words for n = 12 and 13 start from William Echols's 522,737,174 and my 6,747,802,393, and use two moves
from the group: his re-opening of a stretch of consecutive trails and Theo H.'s moving of a trail with a new phase.

The files are `words/superpermutation-N-LENGTH.txt.xz`: XZ archives with a delta filter of distance n that `xz -d`
unpacks (2 KB for n = 8, then 65 KB, 1.1 MB, 4.1 MB and 45 MB for n = 10 to 13), on the first n letters of
`0123456789ABC`, one line plus a line feed, as in Pantone's repository. New words for n = 13 are stored in Theo
H.'s [SPRA format](https://github.com/Tholsh/SPRA) (version 0.2, fields of 6 bits) and packed with `xz`:
`words/superpermutation-13-6747800155.spra.xz`, about 1.3 MB. Its decoder is `tools/reduced_codec.cpp` of that
repository (`g++ -std=c++20 -O2 tools/reduced_codec.cpp -o reduced-codec`), which writes the letters `0`-`9`,
`A`-`C` with no line feed; I checked the file with it and with an independent decoder of mine. The words of
6,747,801,798 and 6,747,801,835 letters before it are stored the same way, and the earlier words for n = 13 stay
as `.txt.xz` files.

The word on 14 symbols would take 94 GB as text. It is stored in the Detour format of the Superpermutation Almanac
([format](https://superpermutations.com/format.txt)): `words/superpermutation-14-93904778043.detour`, 418 KB. Its
decoder is the Almanac's `detour` program (Rust, MIT licence; source at
`https://superpermutations.com/tools/detour-source.tar.gz`, built with `cargo install --path . --locked`), which
writes the letters `0`-`9`, `A`-`D` with no line feed; the word is best streamed into a checker rather than written
out. The earlier word on 14 symbols is a recipe in [`recipes/n14/`](recipes/n14/README.md): a generator, a plan of
94 KB and a checker, as William Echols did with his words. The words of the table that are on the Almanac can also
be downloaded from their Almanac pages in the Detour format (for example
`https://superpermutations.com/w/W-0085/download`).

The words of November for n = 13 and 14 have their letters renamed so that each word starts with `0123456789ABC`
or `0123456789ABCD`, as the Almanac requires, and they are stored that way. The two words for n = 12 are stored in the letters of their base word, which is what
their plans write (522,736,428 starts with `1590647328AB`, 522,736,431 with `3026789145AB`); on the Almanac they
are renamed in the same way, so the SHA-256 there is that of the renamed letters. The words for n = 15 and n = 16 are recipes too, in [`recipes/n15/`](recipes/n15/README.md) and
[`recipes/n16/`](recipes/n16/README.md). Theo H. published the first recipe for n = 15 by lifting my n = 14 plan;
mine lifts the same plan with more choices for the openings. The word for n = 16 is the first word I know of that is
below the value of my Lean theorem `hasWord_sixteen_B`, 22,320,830,091,240, by 34,178,619; for n = 16 there
is no earlier word in the table to compare with.
The word for n = 17 is a recipe as well, in [`recipes/n17/`](recipes/n17/README.md): 377,961,971,839,096 letters,
520,219,328 below the value of `hasWord_seventeen_B`, checked on the card in one pass of 3.6 to 3.8 hours. The recipe
prints a tree hash of the word (the SHA-256 of the SHA-256 digests of its 64 KiB leaves) and the BLAKE3 of the
letters, both computed on the card in the same pass; its plain SHA-256 (below) took a separate CPU run of 4.6 days.
The word for n = 18, in [`recipes/n18/`](recipes/n18/README.md), has 6,779,644,944,870,572 letters, 7,683,011,380
below `hasWord_eighteen_B`. Its plan (15.6 GB) is too big for the repository, so `recipes/n18/check.sh` rebuilds it
from the n = 17 plan and compares its hash with one fixed in advance. The exact check would need 163 GB of card
memory, so this word is checked by sums of hashes over the groups, with keys taken from a public random beacon
after the plan was fixed: one pass of 3.3 days on an RTX 5090, false pass probability at most 6.8e-21. That is a
probabilistic check, not an exact one. The plans of the recipes are made by the programs in [`tools/plans/`](tools/plans/README.md).

```sh
xz -dk words/superpermutation-13-6747800155.spra.xz
./reduced-codec decode words/superpermutation-13-6747800155.spra > superpermutation-13-6747800155.txt
gcc -O3 -o vfast recipes/n14/vfast.c -lpthread
./detour decode words/superpermutation-14-93904778043.detour | ./vfast 14 0123456789ABCD     # 10.9 GB of memory
```

SHA-256 of the words (for n = 8 to 12 the file, which is the word and one line feed; for n = 13 and 14 the letters
as the decoders write them and for n = 15 to 17 as the recipes write them, all with no line feed; for n = 18 I have
only the BLAKE3). The list has the newest word for each n; [`SHA256SUMS`](SHA256SUMS) has the hashes of every
archive, word and plan, the earlier words included.

    n = 8    66ec57ba428e0ac1affc5503b86821920f0def27380697317033911a6628cddd
    n = 10   09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
    n = 11   fea642b8f56e7ab7259a0852fd6cb8ae6f76fffeb407b709ac330726b0a131f2
    n = 12   3c13d84304dd43c53859ed19ef995ae52cee69cb5faa361efa236dca94ef72a3   (522,736,428)
    n = 12   f8f240eb269def562bbb1e4bd3b90dc5f7aab0b3d3c9cea6def4b3e97b5af347   (522,736,431)
    n = 13   ef1b0a9215396a52e56c9f33ba8ca8836151e01acc750105e4df7b97e60840ab
    n = 14   3b026b0adae45976a153f60461f06db5a82cd2189220b4970c2a3ffbd2c87568
    n = 15   d91b875a151480dbac864005bf7bdcd1d9aaeab2d5f5a0bffabfdb1e18cbe21c
    n = 16   e16a7e7f92119f4713e0255cd2856a66dc63efd8e8f9c3c2b89dbd129cf4a61f
    n = 17   c10aee326806d932118a21d5819540101079d5acff9a5cab0e727ba29eb6ab2d

BLAKE3 of the same letters (the value `b3sum` prints, no line feed), from the card checks of
[`recipes/n17/`](recipes/n17/README.md) and [`recipes/n18/`](recipes/n18/README.md):

    n = 15   1cd0698e832bf3d35173e89f092932667f1f27667d6dc6e673946c3d95955fa4
    n = 16   e576707ec1f5bff740a3528dbc35160be1d41035e871f32c8d3d00f2f8c1d504
    n = 17   5d64909d4fd6420e9e5549367e2907ea13fc15d6e2fd1ea419e0b4caa48d8555
    n = 18   8a5344098c97b5d6f34a66b56afafbf2f9928e95690b4604210fc7db12122af6

How the words were found, step by step, is in [`NOTES.md`](NOTES.md).

## The Lean proofs

[`proofs/lean/`](proofs/lean/README.md) holds proofs in Lean 4, stated with the definitions of Pantone's
`Challenge.lean`. With $`F_3(n) = n! + (n-1)! + (n-2)!`$ and $`L(n)`$ the length of the shortest superpermutation:

| result | checked by | directory | Almanac |
|---|---|---|---|
| $`L(n) \le F_3(n) + (c+o(1))\,(n-3)!`$ with $`c`$ from $`\tfrac{1771}{3456}`$ ($`n \ge 13`$) down to $`\tfrac{11117297}{27675648}`$ ($`n \ge 22`$); Pantone's $`c`$ is $`\tfrac{43}{80}`$ | kernel | [`constant/`](proofs/lean/constant/README.md), [`constant61937/`](proofs/lean/constant61937/README.md), [`constant305989/`](proofs/lean/constant305989/README.md), [`constant43586371/`](proofs/lean/constant43586371/README.md) | [b/28](https://superpermutations.com/b/28) for $`\tfrac{1771}{3456}`$ |
| the coefficient tends to 0; $`L(n) - F_3(n)`$ lies between $`2(n-4)! - 2(n-5)!`$ and $`\tfrac{41}{5}(n-4)!`$ for $`n \ge 2^{14}`$ | kernel | [`constant43586371/`](proofs/lean/constant43586371/README.md), [`asym/`](proofs/lean/asym/README.md) | [b/35](https://superpermutations.com/b/35), [b/36](https://superpermutations.com/b/36) |
| my words of 46,174 (and its seven ties), 4,034,855, 43,930,578 and 522,737,175 letters are superpermutations | kernel | [`words/`](proofs/lean/words/README.md), [`words12/`](proofs/lean/words12/README.md) | |
| $`L(n) \ge`$ 46,133, 408,469, 4,033,378, 43,917,903, 522,622,378, 6,746,626,957, 93,891,141,126 for $`n = 8`$ to $`14`$ (Theorem C) | kernel | [`lower/`](proofs/lean/lower/README.md) | [b/14](https://superpermutations.com/b/14) to [b/20](https://superpermutations.com/b/20) (with 93,891,141,008 for n = 14), all superseded |
| $`L(n)`$ exact for $`n \le 6`$: 1, 3, 9, 33, 153, 872; $`L(6) = 872`$ kernel-only, as far as I know the first such proof | kernel | [`small/`](proofs/lean/small/README.md) | [b/37](https://superpermutations.com/b/37) (a version cut into 319 pieces) |
| $`L(8) \ge 46{,}132`$ in William Echols's framework, without his `native_decide` | kernel | [`n8/`](proofs/lean/n8/README.md) | |
| $`L(8) \ge 46{,}134`$ (Theorem D) | kernel and 3 equations by `native_decide` | [`n8_46134/`](proofs/lean/n8_46134/README.md) | [b/39](https://superpermutations.com/b/39) |
| $`L(7) \ge 5{,}899`$, one more than Justin Lebar's 5,898 | kernel and 22 equations by `native_decide` | [`n7/`](proofs/lean/n7/README.md) | [b/40](https://superpermutations.com/b/40) (a shorter proof with 12 equations); 5,898 kernel only: [b/43](https://superpermutations.com/b/43) |
| $`L(7) \ge 5{,}900`$ | kernel and 99 equations by `native_decide` | [`n7_5900/`](proofs/lean/n7_5900/README.md) | |
| $`L(7) \ge 5{,}901`$: the reduction to 30 search equations, 7 of them evaluated | kernel, and 7 equations by `native_decide` | [`n7_5901/`](proofs/lean/n7_5901/README.md) | |
| the 27-walk and the packing of four copies behind the 46,174 word | kernel | [`n8struct/`](proofs/lean/n8struct/README.md) | |

Jay Pantone has since shown that the coefficient of $`(n-4)!`$ is exactly 2 ([b/33](https://superpermutations.com/b/33),
[b/41](https://superpermutations.com/b/41), [b/42](https://superpermutations.com/b/42) on the Almanac). The lower
side $`2(n-4)! - 2(n-5)!`$ is the theorem `lower2_L` of [`asym/`](proofs/lean/asym/README.md).

With tuned constants, William Echols's idea for n = 11, the same Theorem C gives 522,622,401 for n = 12 and
6,746,627,048 for n = 13 ([b/46](https://superpermutations.com/b/46), [b/47](https://superpermutations.com/b/47);
the Lean files are in superpermutation-almanac-lean, commit `7ed009a`). The best lower bounds for every n up to 14
are on the Almanac's [bounds page](https://superpermutations.com/bounds); at n = 9 and 11 they are William
Echols's, at n = 10 and 14 Jay Pantone's.

"Kernel" means checked by the Lean kernel to the end with the axioms `propext`, `Classical.choice` and `Quot.sound`
only. Where equations are evaluated by `native_decide`, the Lean compiler, the C compiler of the toolchain and the
runtime are trusted for them, as in Lebar's proof. $`L(7) \ge 5{,}901`$ as a whole is a computer-assisted proof, not a
Lean theorem: the 23 search equations that Lean has not evaluated rest on C, C++ and CUDA programs, most of them
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
n = 8 and 10 to 13; for n = 13 `literal_check` ran under Linux in 15 minutes. Before I publish a word it goes
through [`tools/prepub/`](tools/prepub/README.md): the three checkers, `tools/trailsearch.c` from the word's plan with
six settings and the fixed-order pass; from n = 11 on also segment insertion with three to five cuts on the card
([`tools/gpucuts/`](tools/gpucuts/README.md)). The word goes out only if none of them shortens it, with one exception:
the word of November for n = 13 passed the checkers, but each round of these steps and the reorder still gave a
shorter word (327, 302, 301, 268, 190, 163, 155), so I published 155 while the search goes on. At n = 14 the
coverage and deletion checks run on the card ([`tools/gpucheck/`](tools/gpucheck/README.md)); `gdelcheck` is the
only deletion check I have there. The word for n = 14 is also checked by `vfast` on the processor, from the Detour
file as above (about an hour on one thread, 11 GB); the earlier word for n = 14 is checked by
`recipes/n14/decode.sh ... check` in the same way. Both found all 87,178,291,200 permutations. The word for n = 15 is checked by
`recipes/n15/check.sh` (a group check, 15 to 22 minutes on 4 threads) and the word for n = 16 by
`recipes/n16/check.sh` on a graphics card (four passes of 19 minutes, or one pass with `core` in 13 minutes); the word for
n = 17 by `recipes/n17/check.sh core` (3.6 to 3.8 hours on an RTX 5090), and the word for n = 18 by the
probabilistic `recipes/n18/check.sh card` (3.3 days).

## Rebuilding a word

Each word rebuilds from a selection (what the closed trails are) and a plan (their order and cuts).
[`reproduce/`](reproduce/REPRODUCE.md) holds both for the words of 4,034,855, 43,930,578, 522,737,175 and
6,747,802,393 letters, with a generator and the hashes to expect: Python 3 and a C compiler, no solver. The two
words of November for n = 12 are on the n = 12 base word of `reproduce/` too (`work/n12-base.txt`, SHA-256
`0d36cdd0...`, which [`foreman/recipe/RECIPE.md`](foreman/recipe/RECIPE.md) calls `base12_hybrid_e.txt`), even though
they start from W-0102 and W-0091: their plans `plan/trailsearch-12-522736428.plan` and
`plan/trailsearch-12-522736431.plan` rebuild them letter for letter. The earlier words for n = 12 and 13 are on the
same base words; their plans are `plan/trailsearch-12-522736969.plan` and `plan/trailsearch-13-6747801798.plan`
(and `plan/trailsearch-13-6747801835.plan` and `plan/trailsearch-13-6747802319.plan` for the words before).

The word of November for n = 13 is on a hybrid base word made from the word itself
([`tools/pipeline/`](tools/pipeline/README.md)): `base.sh` puts the word back into the letters of selection N and
runs `hyb13 --no-rotate` on it and on the n = 13 base word of `reproduce/` (`work/n13-base.txt`, SHA-256
`39491951...`). Then its plan rebuilds the word in the letters of selection N, and renaming the letters gives the
stored word:

```sh
MAP=1293468057ABC BASEN=work/n13-base.txt TOOLS=bin bash tools/pipeline/base.sh superpermutation-13-6747800155.txt hyb
./trailsearch hyb/base.txt rebuilt.txt --plan-in plan/trailsearch-13-6747800155.plan --time 0
tr -d '\n' < rebuilt.txt | tr 1293468057ABC 0123456789ABC | sha256sum    # ef1b0a9215396a52e56c9f33ba8ca8836151e01acc750105e4df7b97e60840ab
```

The word for n = 14 of November has no plan here; the Detour file is the word. The word for n = 11 rebuilds from its own base, the 800
closed trails of selection X with the block images of `plan/images-11-43930534.txt`
(`plan/base-11-43930534.txt.xz`, unpack first), and `plan/trailsearch-11-43930534.plan`. The
earlier words on Pantone's closed trails rebuild from his words and the plans in [`plan/`](plan/) and
[`plan/history/`](plan/history/README.md):

```sh
cc -O2 -mpopcnt -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch BASE.txt rebuilt.txt --plan-in PLAN --time 0
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt    # n = 8, HiGHS, about 3 s
```

## Where the files are

| path | content |
|---|---|
| [`words/`](words/) | the words, and the earlier ones I published (the word on 14 symbols as a Detour file) |
| [`words/n6/`](words/n6/README.md) | all 45,116 minimal superpermutations on 6 symbols, with a checker of the list |
| [`words/n8/`](words/n8/README.md) | the word on 8 symbols: construction, selection, slice order, seven ties, and in [`tools/`](words/n8/tools/README.md) the program that rebuilds, prices and searches |
| [`recipes/n14/`](recipes/n14/README.md) | the earlier word on 14 symbols (93,904,804,405) as a recipe: generator, plan, checker |
| [`recipes/n15/`](recipes/n15/README.md) | the word on 15 symbols as a recipe: generator, plan, group check |
| [`recipes/n16/`](recipes/n16/README.md) | the word on 16 symbols as a recipe: generator with the block, plan, card check |
| [`recipes/n17/`](recipes/n17/README.md) | the word on 17 symbols as a recipe: generator with the block, plan, one-pass card check |
| [`recipes/n18/`](recipes/n18/README.md) | the word on 18 symbols as a recipe: plan rebuilt from n = 17, hash commitment, probabilistic card check |
| [`tools/plans/`](tools/plans/README.md) | the programs that make the plans of the recipes |
| [`reproduce/`](reproduce/REPRODUCE.md) | selection, plan, generator and checker for four words |
| [`plan/`](plan/), [`plan/history/`](plan/history/README.md) | plans of the newest and of the earlier words |
| [`selection/`](selection/README.md) | how the selections were found: block searches and their checkers |
| [`arrange/`](arrange/README.md) | how closed trails become a first plan: chains, their order, the lift from 12 to 13, the n = 10 construction, bounds |
| [`tools/`](tools/README.md) | the C programs that shorten a plan, one line per program, and their tests; in its subfolders the tools of November (card passes, reorder, pipeline, check before publication, card checks) |
| [`foreman/`](foreman/README.md) | a scheduler that runs the search tools on a word in turns, and the recipe of the n = 12 word of 522,736,429 letters |
| [`ties/`](ties/README.md) | the words of the record length of 9 October 2026 for n = 7, 9 and 10 (for n = 9 there are shorter words since November) and of the earlier record length 46,181 for n = 8: 85 new words of 5,905 letters, which published words are the same, 1,223 rotations at n = 8 |
| [`proofs/n7_5901/`](proofs/n7_5901/README.md) | $`L(7) \ge 5{,}901`$: the written proof, the search programs, Table C, the trust level of every search |
| [`proofs/n9/`](proofs/n9/README.md) | 408,731 cannot be beaten at n = 9 with Pantone's closed trails, in three families of words (shorter words on other closed trails exist since November: [W-0099](https://superpermutations.com/w/W-0099), [W-0103](https://superpermutations.com/w/W-0103)) |
| [`proofs/lean/`](proofs/lean/README.md) | the Lean proofs, and one command that checks a word of your own |
| [`catalogue/`](catalogue/CATALOGUE.md) | every result with its status, evidence and the command that reruns it ([`schema.md`](catalogue/schema.md)) |
| [`NOTES.md`](NOTES.md) | the account of every step |
| [`SHA256SUMS`](SHA256SUMS) | hashes of all archives, words and plans |
| [`.github/workflows/`](.github/workflows/) | `check.yml`: the checker of [superpermutations-bot](https://github.com/jhalfar/superpermutations-bot) on every changed word and recipe, and on all of them once a week (`.detour` files are not checked there); `release.yml`: on a tag `words-*`, every word as a checked `.spra.xz` in a GitHub release |
| `test.sh` | the small tests of every part, catalogue included: `bash test.sh PANTONE_REPO` (about 15 minutes on one thread) |

Rebuilding and checking a word needs a C compiler and Python and nothing else. Finding selections and first plans
uses integer programmes; `selection/` and `arrange/` say which need a solver. The C sources follow
[`.clang-format`](.clang-format).

## Credits and licence

The construction is Jay Pantone's, and so are the terms closed trail, slice, selection, completion and transport.
Cutting a closed trail between two 2-cycles and the structure of the n = 10 word come from rumstd's n = 10 word.
Cutting inside a 1-cycle is Theo H.'s idea, and so are the shortest word for n = 8 and the SPRA format. The moves
behind the words for n = 12 and 13 are William Echols's and Theo H.'s, and the recipe form for n = 14 is Echols's.
The cut-opening reorder behind my November words for n = 12, 13 and 14 is Jay Pantone's (W-0107). The words for
n = 12 start from Derek Mahoney's W-0102 and William Echols's W-0091, the word for n = 13 from Jay Pantone's W-0100
and the word for n = 14 from his W-0108; the Almanac's data are under CC BY 4.0.
The lower bounds stand on Xiaolong Liu's preimage-chain library and the Hunter-Raudvere library.
[`NOTICE`](NOTICE) has the details and the commits. Apache License 2.0 (see [`LICENSE`](LICENSE)), the same as the
repository the construction comes from.
