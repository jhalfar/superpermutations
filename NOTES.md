# Notes: how the words were found, step by step

The front page is [`README.md`](README.md). This file keeps the details: the model, the exact commands of the
search runs, and what each step changed. Earlier words are in [`plan/history/`](plan/history/README.md).

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

There are two implementations. `tools/connector_splice.py` (numpy) found my first two n=11 words:

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
# n=13, from my 6,747,918,058 word: -> 6,747,918,034 -> 6,747,917,995 -> 6,747,917,987
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
is the "cluster optimisation" of the generalised-TSP literature. One pass over my previous words gave

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
  letters at n=12, and 34 at n=13 (6,747,917,498 → 6,747,917,464).

A fifth idea is not mine. Theo H.'s 43,930,624 word (derived from my 43,930,628) opens four trails inside a 1-cycle,
which costs two letters per trail but lets consecutive trails overlap in n−2 letters. With such openings allowed, the
pass of step 3 took my 522,745,537 word to 522,745,530 instead of 522,745,531, and the n=12 word above descends from
that one. On later words (43,930,623 and 522,745,498) these openings gained nothing more.

The words in the table: n=11 comes from segment insertion on the 43,930,623 word; n=12 from the 522,745,530 word by
rounds of GPU search (the later ones with block moves), each followed by the pass and the loop moves, down to
522,745,464, then the relocation (522,745,445), segment insertion (522,745,383), one more search round (522,745,379) and segment
insertion again; the n=13 word
from the 6,747,917,970 word by GPU search (one 90-minute round without block moves, ten minutes with them), the
pass, and the relocation; loop moves on it give the 6,747,917,464 of the plan mentioned at the top.

The tools of steps 3 and 4 and the GPU version of the search are not in `tools/` yet; they will be added once
cleaned up. The words above can be rebuilt from their plans with the published tool, and checked without any of my
code.
