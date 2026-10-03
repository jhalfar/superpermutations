# Shorter superpermutations on 11 and 13 symbols

**Jakub Halfar, with Claude (Opus 5.5) in Claude Code.** I chose the problem and directed the work; Claude designed
and ran the searches and wrote the code and this write-up.

Two superpermutations that are shorter than the best known ones (as of 2026-10-03). Both re-join the component words
of Jay Pantone's [43/80 construction](https://github.com/jaypantone/superperm-upper-43-80): they use the same closed
trails, opened at different places and joined in a different order. No new construction is involved.

| n | length | previous best | word | verified |
|---|---|---|---|---|
| 11 | **43,930,649** | 43,930,668 (rumstd, PR #4 to Pantone's repo), 43,930,678 (Theo H., PR #2), 43,930,680 (Pantone) | [`words/superpermutation-11-43930649.txt.xz`](words/superpermutation-11-43930649.txt.xz) | all 39,916,800 permutations; no single letter can be deleted |
| 13 | **6,747,918,058** | 6,747,918,066 (Pantone) | [`words/superpermutation-13-6747918058.txt.xz`](words/superpermutation-13-6747918058.txt.xz) | all 6,227,020,800 permutations |

Words use the alphabet `0123456789A…`, one line plus LF, as in Pantone's repository. Both files are compressed with
his `tools/compress_word.py` (XZ with a delta filter of distance n); plain `xz -d` restores them. SHA-256 values are
in [`SHA256SUMS`](SHA256SUMS).

## Verify

With Pantone's independent checker:

```sh
git clone https://github.com/jaypantone/superperm-upper-43-80
c++ -O3 -std=c++17 superperm-upper-43-80/tools/literal_check.cpp -o literal_check
xz -dk words/superpermutation-11-43930649.txt.xz words/superpermutation-13-6747918058.txt.xz
./literal_check 11 0123456789A   words/superpermutation-11-43930649.txt --deletions
./literal_check 13 0123456789ABC words/superpermutation-13-6747918058.txt
```

The n=13 check needs about 13 GB of RAM and took about 10 minutes here (64-bit Linux). Our results:

* n=11: `"length":43930649, "distinct_permutations":39916800, "missing_permutations":0, "extra_occurrences":18816, "coverage_preserving_deletions":[]`
* n=13: `"length":6747918058, "distinct_permutations":6227020800, "missing_permutations":0, "extra_occurrences":1693436`

A lighter check, `tools/verify_par.c`, uses one bit per permutation (778 MB at n=13) and OpenMP threads. It checks
n=13 in about 30 s on 16 threads:

```sh
cc -O2 -fopenmp -o verify_par tools/verify_par.c
./verify_par words/superpermutation-13-6747918058.txt
```

## Rebuild the n=13 word from Pantone's word (no solver needed)

[`plan/plan-13-6747918058.txt`](plan/plan-13-6747918058.txt) lists, in output order, one line `piece offset` for
each of the 252,120 pieces of Pantone's 6,747,918,066 word. The offset says where that piece's closed trail is
opened (-1 means the piece is written as it is).

```sh
cc -O2 -o pieces tools/pieces.c
cc -O2 -o assemble tools/assemble.c
xz -dkc superperm-upper-43-80/words/13/superpermutation-13-6747918066.txt.xz > pantone-13.txt
./pieces pantone-13.txt pieces-13.txt
./assemble pantone-13.txt pieces-13.txt plan/plan-13-6747918058.txt rebuilt-13.txt   # ~1 min
sha256sum rebuilt-13.txt    # fc9be56c413d125924e43241e8774c1ae922b963e7c0a65b50d16887579f381e
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

**Step 2 (n=11 → 43,930,649): trail-level re-joining with gap-2 openings.** This idea comes from the n=10 word of
length 4,034,873 that rumstd submitted as PR #3 to Pantone's repository. That word uses exactly the same trails as
Pantone's 4,034,889, but it also opens some trails *between two 2-cycles of a row* (a gap-2 opening):
* Such a piece is one letter longer and goes from an h-word u to u shifted by one letter.
* For one letter it therefore acts as a connector step that also absorbs the trail.
* These pieces chain with zero-cost joins (overlap h).

`tools/connector_splice.py` models the whole word as a generalised TSP over trails, with all openings of every trail
(weight 3: cost 0; weight 2: cost 1; skipped duplicate windows). It improves the word by destroy/repair local search.
Starting from 43,930,674 it found 43,930,649. The 25 letters come from three changes:

* the 373 runs regroup into 365, and the join cost between runs drops from 939 to 896 (−43);
* 39 trails get a gap-2 opening (+39);
* 25 joins inside runs now overlap by h letters and cost nothing, so the joins inside runs cost 2,410 instead of
  2,431 (−21).

Results depend on the seed (649–660 in our runs), and further runs from 649 found nothing better:

```sh
python tools/connector_splice.py superpermutation-11-43930674.txt out.txt --time 2400 --seed 2 --kmax 12 --T0 0.2
python tools/connector_splice.py superpermutation-11-43930674.txt out2.txt --start out.txt --time 3000 --seed 7 --kmax 14 --T0 0.5
```

(The 43,930,674 starting word can be rebuilt from Pantone's 43,930,680 with step 1.) The same search found nothing
on 45-million-letter chunks of the n=12 and n=13 words, so we have no improvement there yet.

## Tools

| file | purpose |
|---|---|
| `tools/pieces.c` | pieces, runs and candidate openings of a word |
| `tools/runjoin.py` | step 1: run-level ATSP (needs `gurobipy`), writes a plan |
| `tools/assemble.c` | writes the word described by a plan |
| `tools/connector_splice.py` | step 2: trail-level re-joining with gap-2 openings (needs `numpy`) |
| `tools/verify.c`, `tools/verify_par.c` | streaming / multi-threaded permutation-coverage checks |

## Credits and license

The construction is Jay Pantone's; the gap-2 opening was found in rumstd's n=10 word. Apache License 2.0 (see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)), the same as the repository the input words come from.
