# Shorter superpermutations on 11, 12 and 13 symbols

**Jakub Halfar, with Claude (Opus 5.5) in Claude Code.** I chose the problem and directed the work; Claude designed
and ran the searches and wrote the code and this write-up.

Three superpermutations that are shorter than the best known ones (as of 2026-10-04). All re-join the component
words of Jay Pantone's [43/80 construction](https://github.com/jaypantone/superperm-upper-43-80): they use the same
closed trails, opened at different places and joined in a different order. No new construction is involved.

| n | length | previous best | word | verified |
|---|---|---|---|---|
| 11 | **43,930,628** | 43,930,668 (rumstd, PR #4 to Pantone's repo), 43,930,678 (Theo H., PR #2), 43,930,680 (Pantone) | [`words/superpermutation-11-43930628.txt.xz`](words/superpermutation-11-43930628.txt.xz) | all 39,916,800 permutations; no single letter can be deleted |
| 12 | **522,745,538** | 522,745,581 (Pantone) | [`words/superpermutation-12-522745538.txt.xz`](words/superpermutation-12-522745538.txt.xz) | all 479,001,600 permutations; no single letter can be deleted |
| 13 | **6,747,918,058** | 6,747,918,066 (Pantone) | [`words/superpermutation-13-6747918058.txt.xz`](words/superpermutation-13-6747918058.txt.xz) | all 6,227,020,800 permutations; no single letter can be deleted |

Words use the alphabet `0123456789A…`, one line plus LF, as in Pantone's repository. The files are compressed with
Pantone's `tools/compress_word.py` (XZ with a delta filter of distance n); plain `xz -d` restores them. SHA-256 values
are in [`SHA256SUMS`](SHA256SUMS).

`words/` also keeps our two earlier n=11 words: 43,930,649 (2026-10-03, found from Pantone's word alone with the
Python search) and 43,930,644 (found from rumstd's 43,930,668). The 43,930,628 word was again found from Pantone's
word alone.

## Verify

With Pantone's independent checker:

```sh
git clone https://github.com/jaypantone/superperm-upper-43-80
c++ -O3 -std=c++17 superperm-upper-43-80/tools/literal_check.cpp -o literal_check
xz -dk words/superpermutation-11-43930628.txt.xz words/superpermutation-12-522745538.txt.xz words/superpermutation-13-6747918058.txt.xz
./literal_check 11 0123456789A   words/superpermutation-11-43930628.txt --deletions
./literal_check 12 0123456789AB  words/superpermutation-12-522745538.txt --deletions
./literal_check 13 0123456789ABC words/superpermutation-13-6747918058.txt --deletions
```

The n=13 check needs about 13 GB of RAM and took 49 minutes here (WSL 2, word read from a Windows disk). Our results:

* n=11: `"length":43930628, "distinct_permutations":39916800, "missing_permutations":0, "extra_occurrences":18814, "coverage_preserving_deletions":[]`
* n=12: `"length":522745538, "distinct_permutations":479001600, "missing_permutations":0, "extra_occurrences":169343, "coverage_preserving_deletions":[]`
* n=13: `"length":6747918058, "distinct_permutations":6227020800, "missing_permutations":0, "extra_occurrences":1693436, "coverage_preserving_deletions":[]`

A lighter check, `tools/verify_par.c`, uses one bit per permutation (778 MB at n=13) and OpenMP threads. It checks
n=13 in about 30 s on 16 threads:

```sh
cc -O2 -fopenmp -o verify_par tools/verify_par.c
./verify_par words/superpermutation-13-6747918058.txt
```

`tools/delcheck.c` runs the same single-deletion test as `literal_check --deletions` with two bits per permutation
and the word read from disk in blocks, so n=13 needs 1.6 GB of RAM instead of about 13 GB (2.5 minutes on 8
threads). On test words with known deletable letters it returns the same list as `literal_check`, and on the n=11
n=12 and n=13 words the same numbers:

```sh
cc -O2 -fopenmp -o delcheck tools/delcheck.c
./delcheck words/superpermutation-13-6747918058.txt
```

## Rebuild the n=12 and n=13 words from Pantone's words (no search needed)

n=13: [`plan/plan-13-6747918058.txt`](plan/plan-13-6747918058.txt) lists, in output order, one line `piece offset`
for each of the 252,120 pieces of Pantone's 6,747,918,066 word. The offset says where that piece's closed trail is
opened (-1 means the piece is written as it is).

```sh
cc -O2 -o pieces tools/pieces.c
cc -O2 -o assemble tools/assemble.c
xz -dkc superperm-upper-43-80/words/13/superpermutation-13-6747918066.txt.xz > pantone-13.txt
./pieces pantone-13.txt pieces-13.txt
./assemble pantone-13.txt pieces-13.txt plan/plan-13-6747918058.txt rebuilt-13.txt   # ~1 min
sha256sum rebuilt-13.txt    # fc9be56c413d125924e43241e8774c1ae922b963e7c0a65b50d16887579f381e
```

n=12: [`plan/trailsearch-12-522745538.plan`](plan/trailsearch-12-522745538.plan) lists the 25,206 pieces of our word
in order: which trail of Pantone's 522,745,581 word, where it is opened, and with which gap.

```sh
cc -O2 -fopenmp -o trailsearch tools/trailsearch.c -lm
xz -dkc superperm-upper-43-80/words/12/superpermutation-12-522745581.txt.xz > pantone-12.txt
./trailsearch pantone-12.txt rebuilt-12.txt --plan-in plan/trailsearch-12-522745538.plan --time 0   # ~2 min, 1.3 GB
sha256sum rebuilt-12.txt    # e4cd56e55c5ed69a7219ac97d677090075a921fd60718038d5b1e5d36c0b3bcb
```

## How they were found

**Pieces and runs.** Pantone's words split into *pieces* at the steps of weight ≥ 4. Almost all pieces are
closed trails, each written out once: piece = cyclic word + its first h = n−3 letters, opened at a row junction
(weight-3 opening). Consecutive pieces overlap by at most h−1 letters, and joins with this maximal overlap chain the
pieces into *runs*. The length is

    L = h + Σ(cyclic lengths) + Σ(opening costs) + Σ_joins (h − overlap).

**Step 1 (n=13, and n=11 down to 43,930,674): run-level ATSP.**
* The first and last piece of each run may be re-opened at any weight-3 opening that keeps the run intact.
* A single-piece run may be opened anywhere.
* Ordering the runs then becomes an asymmetric TSP with a choice of opening at each end. It is solved with Gurobi
  (lazy subtour cuts), starting from Pantone's order (`tools/runjoin.py`).
* For n=13 (252,120 pieces, 25,946 runs, arcs restricted to cost ≤ 4), the join cost between runs dropped from 59,241 to
  59,233 letters in 2 hours (Gurobi 14.0 beta, 12 threads). The solver's lower bound was 58,998.
* For n=11 (2,804 pieces, 373 runs) it dropped from 945 to 939, giving 43,930,674.

**Step 2 (n=11 and n=12): trail-level re-joining with gap-2 openings.** This idea comes from the n=10 word of
length 4,034,873 that rumstd submitted as PR #3 to Pantone's repository. That word uses exactly the same trails as
Pantone's 4,034,889, but it also opens some trails *between two 2-cycles of a row* (a gap-2 opening):
* Such a piece is one letter longer and goes from an h-word u to u shifted by one letter.
* For one letter it therefore acts as a connector step that also absorbs the trail.
* These pieces chain with zero-cost joins (overlap h).

The search models the whole word as a generalised TSP over trails, with all openings of every trail (weight 3:
cost 0; weight 2: cost 1; skipped duplicate windows). It improves the word by destroy/repair local search with
simulated-annealing acceptance: remove a few trails, then reinsert each at its best position with its best opening.

There are two implementations. `tools/connector_splice.py` (numpy) found our first two n=11 words:

```sh
python tools/connector_splice.py superpermutation-11-43930674.txt out.txt --time 2400 --seed 2 --kmax 12 --T0 0.2     # 43,930,649
python tools/connector_splice.py superpermutation-11-43930668.txt out.txt --time 7200 --seed 31 --kmax 12 --T0 0.3    # 43,930,644
```

(The 43,930,674 starting word can be rebuilt from Pantone's 43,930,680 with step 1; 43,930,668 is rumstd's word.)

`tools/trailsearch.c` is the same search in C. An opening is stored in a few bytes and its words are read from the
trail when needed, so n=12 (25,200 trails, 40 million openings) fits in 1.3 GB. The sequence is a linked list with a
hash index from words to pieces, and several threads search independently on the shared model. It found the current
words:

```sh
# n=11: 43,930,674 -> 43,930,632 -> 43,930,628
./trailsearch superpermutation-11-43930674.txt a.txt --time 12600 --seed 51 --kmax 12 --T0 0.3 --threads 8 --sync 120
./trailsearch superpermutation-11-43930674.txt b.txt --plan-in a.txt.plan --time 10800 --seed 52 --kmax 12 --T0 0.3 --threads 8 --sync 120
# n=12: 522,745,581 -> 522,745,570 -> 522,745,548 -> 522,745,538
./trailsearch pantone-12.txt c.txt --time 10800 --seed 11 --kmax 8 --T0 0.3
./trailsearch pantone-12.txt d.txt --plan-in c.txt.plan --time 12600 --seed 41 --kmax 10 --T0 0.3 --threads 18 --sync 120 --focus 0.9
./trailsearch pantone-12.txt e.txt --plan-in d.txt.plan --time 10800 --seed 42 --kmax 10 --T0 0.3 --threads 18 --sync 120 --focus 0.9
```

Runs are limited by time and the threads exchange results, so the same command gives a different word each time.
(The 522,745,570 run used an earlier single-threaded version of the tool.) Compared with Pantone's words:

| | n=11: 43,930,680 → 43,930,628 | n=12: 522,745,581 → 522,745,538 |
|---|---|---|
| runs | 373 → 350 | 2,941 → 2,918 |
| join cost between runs | 945 → 858 (−87) | 6,753 → 6,615 (−138) |
| gap-2 openings | 92 (+92) | 234 (+234) |
| joins inside runs | 2,431 → 2,374 (76 cost nothing; −57) | 22,275 → 22,136 (152 cost nothing; −139) |
| total | −52 | −43 |

At n=12 the word has about 1,000 trails with tens of thousands of openings each and 24,000 short ones. Every
improvement logged in the 18-thread runs moved only long trails; `--focus 0.9` skips most iterations that would move
none.

n=13 has not been run with this search yet: it needs about 14 GB of RAM.

## Tools

| file | purpose |
|---|---|
| `tools/pieces.c` | pieces, runs and candidate openings of a word |
| `tools/runjoin.py` | step 1: run-level ATSP (needs `gurobipy`), writes a plan |
| `tools/assemble.c` | writes the word described by a step-1 plan |
| `tools/connector_splice.py` | step 2: trail-level re-joining with gap-2 openings (needs `numpy`) |
| `tools/trailsearch.c` | step 2 in C: multi-threaded, low memory; also rebuilds a word from its plan |
| `tools/verify.c`, `tools/verify_par.c` | streaming / multi-threaded permutation-coverage checks |
| `tools/delcheck.c` | coverage and single-deletion test with little memory (multi-threaded) |

## Credits and license

The construction is Jay Pantone's; the gap-2 opening was found in rumstd's n=10 word. Apache License 2.0 (see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)), the same as the repository the input words come from.
