# A superpermutation on 8 symbols with 46,174 letters

[`words/superpermutation-8-46174.txt.xz`](../superpermutation-8-46174.txt.xz) holds a word on the symbols
`01234567` that contains all 40,320 permutations and has 46,174 letters. The shortest word I knew of before had
46,178 letters, by William Echols (October 2026).

SHA-256 of the word without the line feed: `50d9bb150ffcf28482e4663f9d8a5ff449fae2de2ef09643eefd922fe1b224aa`
(with it, as in the file: `66ec57ba428e0ac1affc5503b86821920f0def27380697317033911a6628cddd`).

## Checking it

The three checkers of the main [`README`](../../README.md#checking-a-word) all accept it: every permutation occurs
(40,377 permutation windows, 57 of them repeats) and no single letter can be deleted.

```sh
xz -dk words/superpermutation-8-46174.txt.xz
python3 reproduce/tools/check_min.py 8 words/superpermutation-8-46174.txt
```

## How it is built

The word is built like the completion step of Pantone's construction, with the letters 6 and 7 fixed. The 120
cyclic orders of `012345` are the loops. Each loop either gets a row of length v (v from 1 to 6), which costs
6 - v extra letters, or gets no row. The rows lead from loop to loop and form closed walks. A walk is read as one or
more closed trails, and a loop without a row is a trail of its own. The trails are then put in an order and joined,
and a join between two trails costs 5 minus the overlap of the two pieces. The length is

    46,085 + Q + J

with Q the cost of the rows and J the cost of the joins. Echols's word is 46,085 + 92 + 1: expensive rows and two
trails that join almost for free. This word is 46,085 + 64 + 25: cheap rows and expensive joins.

The rows come from one closed walk of 27 loops with row lengths `266646664666466466646664666`. It costs Q = 16 and
is a single trail. Four copies of it fit into the 120 loops without meeting and cover 108 of them, and up to the
symmetries of the problem there is exactly one way to do this. Both statements are proved in Lean, with the kernel
checking every step, in [`proofs/lean/n8struct/`](../../proofs/lean/n8struct/README.md). The Klein four-group
{id, (25)(34), (01)(34), (01)(25)} swaps the four walks in pairs and maps the 12 loops left without a row onto
themselves, in three orbits of four (every element other than the identity moves all 12). That gives
Q = 4 x 16 = 64 and 16 trails: the four walks and the twelve single loops.

The word takes them in the order [6 single loops] W W [6 single loops] W W. Its 15 joins have overlaps 4 (eight
times), 3 (four times) and 2 (three times), so J = 8 + 8 + 9 = 25. The element (01)(25) maps the first half onto
the second: the first 2,316 letters of the second half are the image of the start of the word.

[`selection-46174.txt`](selection-46174.txt) lists the 120 loops with their row lengths (0 = no row).
[`order-46174.txt`](order-46174.txt) lists the 784 slices of the word in order. With the selection it gives the
word back letter for letter, without a solver ([`tools/`](tools/README.md#rebuilding-the-46174-word)).

[`ties/`](ties/) holds seven more words of 46,174 letters, in the same format. With the main word they are eight
words that are different even up to renaming the symbols and reading backwards. All come from this selection, up
to symmetry, and all pass `literal_check --deletions`. The file names end with the first 12 hex digits of the
SHA-256 of the word without the line feed.

## How it was found

A set partition over the closed walk types with the fewest letters per loop packed the loops with four copies of
the 27-walk. For each selection an integer program found the best order of the trails and the best joins. My join
program of that time allowed only joins of overlap 3 or more and priced this packing at 46,182, so the search went
on from it with parallel tempering and found other selections of 46,178 letters. When I allowed joins of every
overlap, the packing itself gave 46,174.

The programs are in [`tools/`](tools/README.md), behind one command, `n8.py`. It rebuilds this word from its
selection in a few seconds with the free solver HiGHS. It prices any selection with a proven lower bound within its
model (by default every trail in one run, opened between two slices). It also reads the selection out of any word
of this framework and runs the search: walk types, packing, parallel tempering. From the top of the repository:

```sh
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt
python3 words/n8/tools/n8.py price words/n8/selection-46174.txt --model slices --min-overlap 3    # the 46,182
```

## What is known about it

* My integer program finds no shorter order of the pieces of this selection, but it keeps the place where each
  trail is opened as my join program chose it. With other openings the same selection gives a shorter word.
  Theo H. found one of 46,173 letters by running [`tools/trailsearch.c`](../../tools/trailsearch.c) on this
  selection, which changes the order of the trails and where they are opened (three trails open at a weight-2
  step: openings cost 3 letters more, joins 4 less). His word and the steps to repeat it are in
  [his repository](https://github.com/Tholsh/superpermutation_study/tree/main/data/n8/46173).
* In 115 regions of 50 to 70 loops around it, no change of the rows inside one region gives a shorter word, with
  the same restriction on the openings.
* These are local statements. They do not say that 46,174 is the shortest possible. The best lower bound I know
  with a proof that the Lean kernel checks alone is 46,133 (Theorem C, [`proofs/lean/lower/`](../../proofs/lean/lower/README.md)).
  With three equations evaluated by compiled code it is 46,134 ([`proofs/lean/n8_46134/`](../../proofs/lean/n8_46134/README.md)).
  So the shortest superpermutation on 8 symbols has between 46,134 and 46,173 letters, or between 46,133 and
  46,173 if one accepts only the kernel. The kernel checks the word of 46,174 and its seven ties in
  [`proofs/lean/words/`](../../proofs/lean/words/README.md) (`hasWord_eight_k`).

Echols's word is not copied here.
