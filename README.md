# Shorter superpermutations on 11, 12 and 13 symbols

A superpermutation on n symbols is a word that contains every permutation of the symbols as a substring. This
repository holds three such words that are shorter than any I know of, for n = 11, 12 and 13.

They are built from the pieces of Jay Pantone's
[43/80 construction](https://github.com/jaypantone/superperm-upper-43-80). I change where each piece is cut open and
the order in which the pieces are joined. The construction itself is Pantone's.

I work on this with Claude (Opus 5.5) in Claude Code. I chose the problem and direct the work; Claude designs and
runs the searches and writes the code and this text.

## The words

| n | length | Pantone's word | shorter by | file |
|---|---|---|---|---|
| 11 | **43,930,614** | 43,930,680 | 66 | [`words/superpermutation-11-43930614.txt.xz`](words/superpermutation-11-43930614.txt.xz) |
| 12 | **522,745,356** | 522,745,581 | 225 | [`words/superpermutation-12-522745356.txt.xz`](words/superpermutation-12-522745356.txt.xz) |
| 13 | **6,747,917,421** | 6,747,918,066 | 645 | [`words/superpermutation-13-6747917421.txt.xz`](words/superpermutation-13-6747917421.txt.xz) |

In each of them every permutation occurs and no single letter can be deleted.

n = 12 and n = 13 are still getting shorter, and I update the table when a shorter word has passed the checks. The
words in between are in [`plan/history/`](plan/history/README.md) as plans.

Other recent words for comparison: Theo H. has 43,930,624 and 522,745,531 (PRs #6 and #7 to Pantone's repository),
both made from earlier words of mine. rumstd has 43,930,668 (PR #4).

The files use the alphabet `0123456789ABC`, one line plus a line feed, as in Pantone's repository. They are XZ files
with a delta filter of distance n, and `xz -d` unpacks them. [`SHA256SUMS`](SHA256SUMS) lists the hashes of the
archives and of the words inside.

## Checking a word

Pantone's checker works for n = 11 and n = 12:

```sh
git clone https://github.com/jaypantone/superperm-upper-43-80
c++ -O3 -std=c++17 superperm-upper-43-80/tools/literal_check.cpp -o literal_check
xz -dk words/superpermutation-11-43930614.txt.xz words/superpermutation-12-522745356.txt.xz
./literal_check 11 0123456789A  words/superpermutation-11-43930614.txt --deletions
./literal_check 12 0123456789AB words/superpermutation-12-522745356.txt --deletions
```

For n = 13 it needs about 13 GB of RAM and close to an hour. [`tools/delcheck.c`](tools/delcheck.c) runs the same
test (all permutations present, no deletable letter) in 1.6 GB and about a minute on 16 threads:

```sh
cc -O2 -fopenmp -o delcheck tools/delcheck.c
xz -dk words/superpermutation-13-6747917421.txt.xz
./delcheck words/superpermutation-13-6747917421.txt
```

On seven test words with known deletable letters `delcheck` returns the same list as `literal_check`. What the
checks print for the three words:

* n=11: `"length":43930614, "distinct_permutations":39916800, "missing_permutations":0, "extra_occurrences":18816, "coverage_preserving_deletions":[]`
* n=12: `"length":522745356, "distinct_permutations":479001600, "missing_permutations":0, "extra_occurrences":169347, "coverage_preserving_deletions":[]`
* n=13: `"length":6747917421, "distinct_permutations":6227020800, "missing_permutations":0, "extra_occurrences":1693434, "coverage_preserving_deletions":[]`

I ran `literal_check --deletions` on the n=11 and n=12 words and `delcheck` on all three.

## Rebuilding a word from its plan

A plan is a text file that lists the pieces of a word in order: which trail of a base word, where it is cut open,
and with which gap. [`tools/trailsearch.c`](tools/trailsearch.c) turns a base word and a plan back into the word, so
you can reproduce every word here without running a search.

```sh
cc -O2 -fopenmp -o trailsearch tools/trailsearch.c -lm

# n=11, from my 43,930,674 word (seconds)
xz -dk words/superpermutation-11-43930674.txt.xz
./trailsearch words/superpermutation-11-43930674.txt rebuilt-11.txt --plan-in plan/trailsearch-11-43930614.plan --time 0
sha256sum rebuilt-11.txt    # 388ec7d60116acfac039b45533589f45afa85b13d83ae740a916d3a477ca44ab

# n=12, from Pantone's 522,745,581 word (about 2 minutes, 1.3 GB)
xz -dkc superperm-upper-43-80/words/12/superpermutation-12-522745581.txt.xz > pantone-12.txt
./trailsearch pantone-12.txt rebuilt-12.txt --plan-in plan/trailsearch-12-522745356.plan --time 0
sha256sum rebuilt-12.txt    # cfe09d18369578c7ad619d570d701d01c400963e5848d1ddfa737bb04593bfc6
```

n=13 takes two steps, because its plans refer to my 6,747,918,058 word, which itself is Pantone's word with the
pieces reordered:

```sh
cc -O2 -o pieces tools/pieces.c
cc -O2 -o assemble tools/assemble.c
xz -dkc superperm-upper-43-80/words/13/superpermutation-13-6747918066.txt.xz > pantone-13.txt
./pieces pantone-13.txt pieces-13.txt
./assemble pantone-13.txt pieces-13.txt plan/plan-13-6747918058.txt step1-13.txt   # about 1 minute
sha256sum step1-13.txt      # fc9be56c413d125924e43241e8774c1ae922b963e7c0a65b50d16887579f381e
./trailsearch step1-13.txt rebuilt-13.txt --plan-in plan/trailsearch-13-6747917421.plan --time 0 --threads 1   # about 10 minutes, 11 GB
sha256sum rebuilt-13.txt    # 6799742ec56bb8a2f2e3c5dcbac2b805be39d552f03ed6a52ffd4fc03883ccd3
```

[`plan/`](plan/) also has the plans of the earlier published words, and
[`plan/history/`](plan/history/README.md) has plans for the words found in between, each with the hash of its word.
If you want to start from a different word than my best one, take one of those.

## How the words were found

Pantone's words are made of closed trails, each written out once and joined to the next with as much overlap as
possible. I keep the trails and change two things: where each trail is cut open, and the order of the pieces.

1. Reordering runs. Pieces that overlap as much as possible form runs. Ordering the runs is a travelling
   salesman problem, which Gurobi improves a little: n=13 went from 6,747,918,066 to 6,747,918,058 and n=11 from
   43,930,680 to 43,930,674.
2. Cutting trails open in other places. rumstd's n=10 word cuts some trails between two 2-cycles. Such a piece
   is one letter longer, but pieces cut this way chain with no cost at the joins. A local search over all trails and
   all cuts (take a few trails out, put each back at its best place) gave 43,930,628, 522,745,537 and 6,747,917,987.
3. Choosing all cuts at once. For a fixed order, the best cut of every trail can be found for all trails
   together by dynamic programming. One pass gave 43,930,625, 522,745,531 and 6,747,917,970. Theo H. found the same
   idea independently and applied it to my earlier words (PRs #6 and #7). My 522,745,531 was in this repository a few
   hours before PR #7, and it is a different word from Theo's.
4. Moves that change the order, judged by step 3. After step 3 the search of step 2 stalls, because it never
   moves a trail and re-cuts its neighbours at the same time. Four kinds of moves do that:
   * whole blocks of trails moved inside the search, with the pass of step 3 repeated as the search runs (this
     search uses a GPU);
   * a few neighbouring trails moved somewhere else, with the trails around both places re-cut. This took n=13 from
     6,747,917,824 to 6,747,917,498 without any random search;
   * the sequence cut at three to six joins and put together in another order. This found n=11 (43,930,623 to
     43,930,614) and most of the recent gain at n=12 (522,745,445 to 522,745,383, and with up to five cuts
     522,745,374 to 522,745,366);
   * a trail written in two segments with a closed block of other trails hung between them. This gives a few letters
     at n=12 and 34 at n=13.

   When these moves find nothing more, a short search at a high temperature ends on a different sequence a few
   letters longer, and the same moves start again from there. At n=12 that gave 522,745,376 to 522,745,374 and
   522,745,366 to 522,745,356. At n=13 loop moves and relocation in turn went from 6,747,917,498 to 6,747,917,421.
5. Cuts inside a 1-cycle. This is Theo H.'s idea, from the 43,930,624 word. It costs two letters per trail but
   lets neighbouring trails overlap in n−2 letters. With it step 3 gives 522,745,530 instead of 522,745,531, and my
   n=12 word descends from that one.

[`NOTES.md`](NOTES.md) has the details: the model, the commands of the search runs, and tables of what each step
changed.

## What is in the repository

| path | content |
|---|---|
| `words/` | the three words, and the earlier ones I published (43,930,674 to 43,930,623; 522,745,538 to 522,745,376; 6,747,918,058 to 6,747,917,498) |
| `plan/` | plans of the published words |
| `plan/history/` | plans of the words found in between, with a table of lengths and hashes |
| `tools/trailsearch.c` | the search of step 2; also rebuilds a word from a plan |
| `tools/delcheck.c` | coverage and single-deletion check with little memory |
| `tools/verify_par.c`, `tools/verify.c` | faster checks of coverage only |
| `tools/pieces.c`, `tools/assemble.c`, `tools/runjoin.py` | step 1 (`runjoin.py` needs `gurobipy`) |
| `tools/connector_splice.py` | an earlier Python version of step 2 (needs `numpy`) |
| `SHA256SUMS` | hashes of all archives, words and plans |

The programs for steps 3 to 5 and the GPU search are not here yet. I will add them once they are in a state worth
reading. Nothing above depends on them: every word can be rebuilt from its plan and checked with the tools listed.

## Credits and licence

The construction is Jay Pantone's. Cutting a trail between two 2-cycles comes from rumstd's n=10 word, and cutting
inside a 1-cycle from Theo H.'s n=11 word. Apache License 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)),
the same as the repository the input words come from.
