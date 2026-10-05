# Shorter superpermutations on 11, 12 and 13 symbols

**Jakub Halfar, with Claude (Opus 5.5) in Claude Code.** I chose the problem and directed the work; Claude designed
and ran the searches and wrote the code and this write-up.

Three superpermutations that are shorter than the best known ones (as of 2026-10-05). All re-join the component
words of Jay Pantone's [43/80 construction](https://github.com/jaypantone/superperm-upper-43-80): they use the same
closed trails, opened at different places and joined in a different order (a few trails are written in two
segments). No new construction is involved.

| n | length | previous best | word | verified |
|---|---|---|---|---|
| 11 | **43,930,614** | 43,930,624 (Theo H., PR #6 to Pantone's repo, derived from our 43,930,628), 43,930,668 (rumstd, PR #4), 43,930,680 (Pantone) | [`words/superpermutation-11-43930614.txt.xz`](words/superpermutation-11-43930614.txt.xz) | all 39,916,800 permutations; no single letter can be deleted |
| 12 | **522,745,383** | 522,745,531 (ours, 2026-10-05 01:45 CEST; Theo H. reached the same length independently a few hours later with a different word, derived from our 522,745,538), 522,745,581 (Pantone) | [`words/superpermutation-12-522745383.txt.xz`](words/superpermutation-12-522745383.txt.xz) | all 479,001,600 permutations; no single letter can be deleted |
| 13 | **6,747,917,970** | 6,747,918,066 (Pantone) | [`words/superpermutation-13-6747917970.txt.xz`](words/superpermutation-13-6747917970.txt.xz) | all 6,227,020,800 permutations; no single letter can be deleted |

n=13 is being worked on. A later word of length **6,747,917,498** exists as a plan,
[`plan/trailsearch-13-6747917498.plan`](plan/trailsearch-13-6747917498.plan) (relative to our 6,747,918,058 word, like
the other n=13 plans); the word has SHA-256 `685bbc4db886f8f226f22341d6e8fbc127216f39135e9d83e65a6af94bd8e7ce` and passes
`tools/delcheck.c`; `tools/trailsearch.c` rebuilds it from the plan. The compressed word is being
made (about 100 minutes) and will be added.

Words use the alphabet `0123456789A…`, one line plus LF, as in Pantone's repository. The files are compressed with
Pantone's `tools/compress_word.py` (XZ with a delta filter of distance n); plain `xz -d` restores them. SHA-256 values
are in [`SHA256SUMS`](SHA256SUMS).

`words/` also keeps our earlier words: for n=11, 43,930,674 (2026-10-02, run-level step only; it is the base
word of the n=11 plan), 43,930,649 and 43,930,644 (2026-10-03/04) and 43,930,628 (2026-10-04, the word Theo H.'s
43,930,624 was derived from); for n=11 also 43,930,623 and for n=12 522,745,538 (2026-10-04) and 522,745,531 (both 2026-10-05 01:45 CEST) and 522,745,464 (07:48); for n=13, 6,747,918,058 (2026-10-03, run-level
step only; the base word of the n=13 plans) and 6,747,917,987 (2026-10-04, before step 3 below). Plans of the other
words found on the way are in [`plan/history/`](plan/history/README.md).

## Verify

With Pantone's independent checker:

```sh
git clone https://github.com/jaypantone/superperm-upper-43-80
c++ -O3 -std=c++17 superperm-upper-43-80/tools/literal_check.cpp -o literal_check
xz -dk words/superpermutation-11-43930614.txt.xz words/superpermutation-12-522745383.txt.xz words/superpermutation-13-6747917970.txt.xz
./literal_check 11 0123456789A   words/superpermutation-11-43930614.txt --deletions
./literal_check 12 0123456789AB  words/superpermutation-12-522745383.txt --deletions
./literal_check 13 0123456789ABC words/superpermutation-13-6747917970.txt --deletions
```

The n=13 check needs about 13 GB of RAM and took 49 minutes here (WSL 2, word read from a Windows disk). We ran it on
the n=11 and n=12 words and on our two earlier n=13 words (6,747,918,058 and 6,747,917,995). The current n=13 word
was checked with `tools/delcheck.c` (below), which runs the same test in 1.6 GB. Results:

* n=11: `"length":43930614, "distinct_permutations":39916800, "missing_permutations":0, "extra_occurrences":18816, "coverage_preserving_deletions":[]`
* n=12: `"length":522745383, "distinct_permutations":479001600, "missing_permutations":0, "extra_occurrences":169350, "coverage_preserving_deletions":[]`
* n=13 (`delcheck`): `"length":6747917970, "distinct_permutations":6227020800, "missing_permutations":0, "extra_occurrences":1693436, "coverage_preserving_deletions":[]`

A lighter check, `tools/verify_par.c`, uses one bit per permutation (778 MB at n=13) and OpenMP threads. It checks
n=13 in about 30 s on 16 threads:

```sh
cc -O2 -fopenmp -o verify_par tools/verify_par.c
./verify_par words/superpermutation-13-6747917970.txt
```

`tools/delcheck.c` runs the same single-deletion test as `literal_check --deletions` with two bits per permutation
and the word read from disk in blocks, so n=13 needs 1.6 GB of RAM instead of about 13 GB (about one minute on 16
threads). On seven test words with known deletable letters it returns the same list as `literal_check`, and on
the n=11 and n=12 words and the two earlier n=13 words the same numbers:

```sh
cc -O2 -fopenmp -o delcheck tools/delcheck.c
./delcheck words/superpermutation-13-6747917970.txt
```

## Rebuild the words from their plans (no search needed)

A plan lists the pieces of a word in order: which trail of the base word, where it is opened, and with which gap.

n=11: [`plan/trailsearch-11-43930614.plan`](plan/trailsearch-11-43930614.plan) is relative to our 43,930,674 word
([`plan/trailsearch-11-43930623.plan`](plan/trailsearch-11-43930623.plan) gives the earlier 43,930,623 word).

```sh
cc -O2 -fopenmp -o trailsearch tools/trailsearch.c -lm
xz -dk words/superpermutation-11-43930674.txt.xz
./trailsearch words/superpermutation-11-43930674.txt rebuilt-11.txt --plan-in plan/trailsearch-11-43930614.plan --time 0   # seconds
sha256sum rebuilt-11.txt    # 388ec7d60116acfac039b45533589f45afa85b13d83ae740a916d3a477ca44ab
```

n=12: [`plan/trailsearch-12-522745383.plan`](plan/trailsearch-12-522745383.plan) is relative to Pantone's 522,745,581
word. It was written from the finished word by a converter (the search itself worked on a re-based copy), so a few
of its lines are segments of trails. [`plan/trailsearch-12-522745464.plan`](plan/trailsearch-12-522745464.plan) and
[`plan/trailsearch-12-522745531.plan`](plan/trailsearch-12-522745531.plan) give the earlier 522,745,464 and 522,745,531
words in the same way.

```sh
xz -dkc superperm-upper-43-80/words/12/superpermutation-12-522745581.txt.xz > pantone-12.txt
./trailsearch pantone-12.txt rebuilt-12.txt --plan-in plan/trailsearch-12-522745383.plan --time 0   # ~2 min, 1.3 GB
sha256sum rebuilt-12.txt    # 6d787880b4b660f36428715f11a178af816bd1a936f95cfb518217685d99382e
```

n=13 takes two steps. [`plan/plan-13-6747918058.txt`](plan/plan-13-6747918058.txt) lists, in output order, one line
`piece offset` for each of the 252,120 pieces of Pantone's 6,747,918,066 word. The offset says where that piece's
closed trail is opened (-1 means the piece is written as it is). This gives our 6,747,918,058 word.
[`plan/trailsearch-13-6747917970.plan`](plan/trailsearch-13-6747917970.plan) then lists the 252,081 pieces of the
final word in terms of the trails of that word ([`plan/trailsearch-13-6747917987.plan`](plan/trailsearch-13-6747917987.plan) does the same for
the earlier 6,747,917,987 word).

```sh
cc -O2 -o pieces tools/pieces.c
cc -O2 -o assemble tools/assemble.c
xz -dkc superperm-upper-43-80/words/13/superpermutation-13-6747918066.txt.xz > pantone-13.txt
./pieces pantone-13.txt pieces-13.txt
./assemble pantone-13.txt pieces-13.txt plan/plan-13-6747918058.txt step1-13.txt   # ~1 min
sha256sum step1-13.txt      # fc9be56c413d125924e43241e8774c1ae922b963e7c0a65b50d16887579f381e
./trailsearch step1-13.txt rebuilt-13.txt --plan-in plan/trailsearch-13-6747917970.plan --time 0 --threads 1   # ~10 min, 11 GB
sha256sum rebuilt-13.txt    # 45166bd621d76a6ada538e05d62776019227048b08e79a660dbd4a018654c385
```

## How they were found

**Pieces and runs.** Pantone's words split into *pieces* at the steps of weight ≥ 4. Almost all pieces are
closed trails, each written out once: piece = cyclic word + its first h = n−3 letters, opened at a row junction
(weight-3 opening). Consecutive pieces overlap by at most h−1 letters, and joins with this maximal overlap chain the
pieces into *runs*. The length is

    L = h + Σ(cyclic lengths) + Σ(opening costs) + Σ_joins (h − overlap).

**Step 1 (n=13 down to 6,747,918,058, and n=11 down to 43,930,674): run-level ATSP.**
* The first and last piece of each run may be re-opened at any weight-3 opening that keeps the run intact.
* A single-piece run may be opened anywhere.
* Ordering the runs then becomes an asymmetric TSP with a choice of opening at each end. It is solved with Gurobi
  (lazy subtour cuts), starting from Pantone's order (`tools/runjoin.py`).
* For n=13 (252,120 pieces, 25,946 runs, arcs restricted to cost ≤ 4), the join cost between runs dropped from 59,241 to
  59,233 letters in 2 hours (Gurobi 14.0 beta, 12 threads). The solver's lower bound was 58,998.
* For n=11 (2,804 pieces, 373 runs) it dropped from 945 to 939, giving 43,930,674.

**Step 2 (all three): trail-level re-joining with gap-2 openings.** This idea comes from the n=10 word of
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
trail when needed, so n=12 (25,200 trails, 40 million openings) fits in 1.3 GB and n=13 (252,000 trails, 482 million openings) in about
12 GB with 8 threads. The sequence is a linked list with a
hash index from words to pieces, and several threads search independently on the shared model. It found the current
words:

```sh
# n=11: 43,930,674 -> 43,930,632 -> 43,930,628
./trailsearch superpermutation-11-43930674.txt a.txt --time 12600 --seed 51 --kmax 12 --T0 0.3 --threads 8 --sync 120
./trailsearch superpermutation-11-43930674.txt b.txt --plan-in a.txt.plan --time 10800 --seed 52 --kmax 12 --T0 0.3 --threads 8 --sync 120
# n=12: 522,745,581 -> 522,745,570 -> 522,745,548 -> 522,745,538 -> 522,745,537 (then step 3)
./trailsearch pantone-12.txt c.txt --time 10800 --seed 11 --kmax 8 --T0 0.3
./trailsearch pantone-12.txt d.txt --plan-in c.txt.plan --time 12600 --seed 41 --kmax 10 --T0 0.3 --threads 18 --sync 120 --focus 0.9
./trailsearch pantone-12.txt e.txt --plan-in d.txt.plan --time 10800 --seed 42 --kmax 10 --T0 0.3 --threads 18 --sync 120 --focus 0.9
./trailsearch pantone-12.txt f.txt --plan-in e.txt.plan --time 10800 --seed 43 --kmax 10 --T0 0.3 --threads 18 --sync 120 --focus 0.9
# n=13, from our 6,747,918,058 word: -> 6,747,918,034 -> 6,747,917,995 -> 6,747,917,987
./trailsearch step1-13.txt g.txt --time 600 --seed 61 --kmax 10 --T0 0.3 --threads 6 --sync 300 --focus 0.8
./trailsearch step1-13.txt h.txt --plan-in g.txt.plan --time 10800 --seed 62 --kmax 10 --T0 0.3 --threads 10 --sync 300 --focus 0.8
./trailsearch step1-13.txt i.txt --plan-in h.txt.plan --time 10800 --seed 64 --kmax 12 --T0 0.4 --threads 8 --sync 300 --focus 0.8
```

Runs are limited by time and the threads exchange results, so the same command gives a different word each time.
(The 522,745,570 run used an earlier single-threaded version of the tool.) The words after steps 2 and 3, compared
with Pantone's words:

| | n=11: 43,930,680 → 43,930,623 | n=12: 522,745,581 → 522,745,531 | n=13: 6,747,918,066 → 6,747,917,987 |
|---|---|---|---|
| runs | 373 → 346 | 2,941 → 2,921 | 25,946 → 26,019 |
| join cost between runs | 945 → 844 (−101) | 6,753 → 6,615 (−138) | 59,241 → 59,020 (−221) |
| gap-2 openings | 81 (+81) | 222 (+222) | 623 (+623) |
| joins inside runs | 2,431 → 2,394 (61 cost nothing; −37) | 22,275 → 22,141 (144 cost nothing; −134) | 226,174 → 225,693 (369 cost nothing; −481) |
| total | −57 | −50 | −79 |

At n=12 the word has about 1,000 trails with tens of thousands of openings each and 24,000 short ones. Every
improvement logged in the 18-thread runs moved only long trails; `--focus 0.9` skips most iterations that would move
none.

n=13 behaves the same way with ten times as many trails. Pantone's n=13 word contains one open path of two pieces that
is not a closed trail; the tool leaves it where it is. The word was still getting shorter when the last run ended.

**Step 3 (2026-10-05): all openings at once.** The search re-inserts a few trails at a time, each with its best
opening next to fixed neighbours. For a fixed order of the pieces, the best opening of *every* trail can be chosen
simultaneously by dynamic programming over the sequence (one layer per piece; because a join costs h minus a
suffix-prefix overlap, a layer is handled with hash tables in time proportional to its number of openings). This
is the "cluster optimisation" of the generalised-TSP literature. One pass over our previous words gave

* n=11: 43,930,628 → 43,930,625, and a further search run from there (random tie-breaking, moves of whole blocks,
  the pass repeated every 500 iterations) 43,930,623;
* n=12: 522,745,537 → 522,745,531;
* n=13: 6,747,917,987 → 6,747,917,970.

**Step 4 (2026-10-05): moves that change the order together with the openings.** After step 3 the plain search
stalls: it re-inserts trails next to neighbours whose openings stay fixed, and the pass of step 3 never changes the
order. Four additions got it moving again. In each of them the pass of step 3 (or its tables) is what judges a move.

* *Blocks, with the pass inside the search.* A whole run of trails (or part of one) is moved to another place without
  being re-opened, and the pass is repeated every few hundred iterations in an incremental form that only recomputes
  the layers that changed. Neither helps alone; together they took n=12 from 522,745,497 to 522,745,482 in one
  20-minute round. This search runs on a GPU: the card evaluates the openings of the long trails (thousands each)
  against the whole sequence.
* *Relocation with re-opening.* From forward and backward tables of the pass one gets, exactly, what is saved by
  taking a window of consecutive trails out when all other openings may change, and what it costs to insert a trail
  elsewhere when its new neighbours may re-open. Windows whose saving exceeds the cost are moved and confirmed by the
  pass. No random search is involved: 522,745,482 → 522,745,466 and 522,745,464 → 522,745,445 in four minutes each,
  and at n=13 6,747,917,824 → 6,747,917,498 in under two hours.
* *Segment insertion.* The sequence is cut at three to six joins and its stretches, of any length, are reassembled in
  another order; each candidate is judged with the best openings of the whole new sequence. This found n=11:
  43,930,623 → 621 → 619 → 615 → 43,930,614, where every other move had stalled (no reordering inside windows of up
  to 9 consecutive pieces shortens the 43,930,623 word). At n=12 it took 522,745,445 to 522,745,383 in 23 minutes.
* *Loops.* The trails and joins of a word form a balanced directed graph, and any connected balanced graph spells a
  word (Pantone's summary, section 5), so a trail may be written in two segments with a closed block of other trails
  hung between them. This pays when a join already passes through a cut of another trail: never at n=11, a few
  letters at n=12, more on our n=13 plans (not applied there yet).

A fifth idea is not ours. Theo H.'s 43,930,624 word (derived from our 43,930,628) opens four trails inside a 1-cycle,
which costs two letters per trail but lets consecutive trails overlap in n−2 letters. With such openings allowed, the
pass of step 3 took our 522,745,537 word to 522,745,530 instead of 522,745,531, and the n=12 word above descends from
that one. On later words (43,930,623 and 522,745,498) these openings gained nothing more.

The words in the table: n=11 comes from segment insertion on the 43,930,623 word; n=12 from the 522,745,530 word by
rounds of GPU search (the later ones with block moves), each followed by the pass and the loop moves, down to
522,745,464, then the relocation (522,745,445) and segment insertion; the n=13 plan
from the 6,747,917,970 word by GPU search (one 90-minute round without block moves, ten minutes with them), the
pass, and the relocation.

The tools of steps 3 and 4 and the GPU version of the search are not in `tools/` yet; they will be added once
cleaned up. The words above can be rebuilt from their plans with the published tool, and checked without any of our
code.

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

The construction is Jay Pantone's; the gap-2 opening was found in rumstd's n=10 word, and the opening inside a
1-cycle in Theo H.'s n=11 word. Apache License 2.0 (see
[`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)), the same as the repository the input words come from.
