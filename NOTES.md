# Notes: what I did, step by step, and what each step was worth

The front page is [`README.md`](README.md). This file is the full account, in the order in which things happened:
what each step did to each n, what it cost and which tool does it.

It has two parts. Part one keeps the closed trails of Jay Pantone's words and changes where each one is cut and the
order of the pieces. That took four days and gave 66 letters at n = 11, 231 at n = 12 and 1,409 at n = 13 below his
words. Part two changes the closed trails themselves, by other selections inside his construction. That took one
day and gave 36 more letters at n = 11, 8,051 at n = 12 and 113,782 at n = 13, and at n = 10 a word of
4,034,855 letters, 18 below rumstd's. Part one is how I got to part two: every pass that polishes the new words
was written for the old ones.

After the two parts come the things I tried that gave nothing, with the numbers, so that nobody has to try them
again, then what is known about how much is left and how the words were checked.

The tools are in [`tools/`](tools/README.md). The machine was one desktop: a Ryzen 9 5950X with 16 cores, 32 GB of
RAM and an RTX 5090. Everything here happened between October 2 and October 6, 2026.

## The model

A word of Pantone's construction splits into pieces at the steps of weight 4 or more. Almost every piece is a
closed trail written out once: the cyclic word of the trail followed by its first h = n - 3 letters. Consecutive
pieces overlap in at most h - 1 letters, and pieces joined with that overlap form runs. In part one I keep the
trails and change where each one is cut and the order of the pieces. The length of a word is

    L = h + sum of the cyclic lengths + sum of the cut costs + sum over the joins of (h - overlap).

A cut at a step of weight 3 is free. A cut between two 2-cycles, at a step of weight 2, costs one letter. A cut
inside a 1-cycle costs two letters.

| Pantone's words | n = 11 | n = 12 | n = 13 |
|---|---:|---:|---:|
| closed trails | 2,800 | 25,200 | 252,000 |
| of these big (more than 3,000 cuts) | 112 | 1,008 | 10,080 |
| cuts | 3.7 million | 40 million | 482 million |

Pantone's n = 13 word also has one open path of two pieces that is not a closed trail. The tools leave it where it
is.

# Part one: Pantone's closed trails

## Step 1: reordering runs

The first and last piece of a run may be cut at another step of weight 3 without breaking the run. Ordering the runs
is then an asymmetric travelling salesman problem with a choice at each end. I solved it with Gurobi, with lazy
subtour cuts, starting from Pantone's order.

| n | before | after | cost |
|---|---:|---:|---|
| 11 | 43,930,680 | 43,930,674 | 50 minutes; 373 runs; join cost between runs 945 to 939, bound 937 |
| 13 | 6,747,918,066 | 6,747,918,058 | 2 hours on 12 threads; 25,946 runs; 59,241 to 59,233, bound 58,998 |
| 12 | 522,745,581 | no gain | with joins of cost up to 3 Pantone's order is provably optimal; with cost up to 6 nothing in 2 hours, bound 28 letters below |
| 10 | 4,034,889 | no gain | Pantone's order is the optimum at this level |

Tools: `pieces.c`, `runjoin.py`, `assemble.c`. It needs a full Gurobi licence.

What it was worth: 6 and 8 letters. Every later step changes the runs themselves, so this level stops mattering. I
would skip it today. It stays here because the 43,930,674 and 6,747,918,058 words are the base words of the later
plans.

## Step 2: a search over trails and cuts

rumstd's n = 10 word of 4,034,873 letters uses the same trails as Pantone's but cuts some of them between two
2-cycles. Such a piece is one letter longer and goes from an h-word to the same word shifted by one letter, so
pieces cut this way chain with joins that cost nothing.

The search treats the word as a travelling salesman problem over trails in which every trail has all its cuts as
alternatives. One iteration removes a few trails and puts each back at its best place with its best cut. Simulated
annealing decides whether to keep the result.

| n | before | after | cost |
|---|---:|---:|---|
| 11 | 43,930,674 | 43,930,649 | Python version, 40 minutes on one thread |
| 11 | 43,930,674 | 43,930,632 | C version, 3.5 hours on 8 threads |
| 11 | 43,930,632 | 43,930,628 | 3 hours on 8 threads, all of it in the first 33 minutes |
| 12 | 522,745,581 | 522,745,570 | 3 hours on one thread |
| 12 | 522,745,570 | 522,745,548 | 3.5 hours on 18 threads |
| 12 | 522,745,548 | 522,745,538 | 3 hours on 18 threads |
| 12 | 522,745,538 | 522,745,537 | 3 hours on 18 threads, for one letter |
| 13 | 6,747,918,058 | 6,747,918,034 | 10 minutes on 6 threads |
| 13 | 6,747,918,034 | 6,747,917,995 | 3 hours on 10 threads |
| 13 | 6,747,917,995 | 6,747,917,987 | 3 hours on 8 threads, 12 GB |

A second n = 11 line started from rumstd's 43,930,668 word and reached 43,930,644 in 2 hours of the Python version.

Tools: `connector_splice.py` (Python, the first version) and `trailsearch.c`. The present `trailsearch.c` is four
times faster than the one that made these runs. With a card, `trailsearch_gpu.c` makes about 40 times the
iterations per thread of that first version at n = 12.

What it was worth: 46 letters at n = 11, 44 at n = 12 and 71 at n = 13, for about ten hours of a many-core machine
per n. At n = 12 every improvement in the logs moved only big trails, so `--focus` skips most iterations that would
move none. The search flattens: the last 3 hours at n = 11 gave nothing and at n = 12 one letter. At n = 9 and
n = 10 it found nothing from rumstd's words in several hours.

## Step 3: all cuts at once for a fixed order

The search puts a trail back with its best cut next to neighbours whose cuts stay as they are. For a fixed order
the best cut of every trail can be found for all trails together by dynamic programming, one layer per piece. Theo
H. found the same pass independently and applied it to my earlier words.

| n | before | after | cost |
|---|---:|---:|---|
| 11 | 43,930,628 | 43,930,625 | under a second after 3 seconds of loading |
| 12 | 522,745,537 | 522,745,531 | seconds after half a minute of loading |
| 13 | 6,747,917,987 | 6,747,917,970 | 402 seconds with loading |

Tool: `recut.c`.

What it was worth: 3, 6 and 17 letters for almost no time. Its larger use came later. After a round of search it
gives another 3 to 8 letters on top of the round (529 to 526, 520 to 512 and 521 to 516 at n = 12), and its tables
are what the passes of step 5 judge their moves with. Run it first on any word.

rumstd's n = 9 and n = 10 words are already optimal for their order.

## Step 4: cuts inside a 1-cycle

This is Theo H.'s idea. His 43,930,624 word, made from my 43,930,628, has exactly the order of mine with 101 trails
cut elsewhere. Four of them are cut inside a 1-cycle. Such a piece costs two letters but lets two neighbouring
pieces overlap in n - 2 letters, more than the model above allows.

| n | before | fixed-order pass | the same pass with these cuts |
|---|---:|---:|---:|
| 11 | 43,930,628 | 43,930,625 | 43,930,624 |
| 11 | 43,930,632 | 43,930,631 | 43,930,629 |
| 12 | 522,745,537 | 522,745,531 | 522,745,530 |

Tools: `recut_wide.c`, and `word2plan.c --rebase` to go on from such a word with the other tools.

What it was worth: one letter at n = 12, where my line of words descends from the 522,745,530 word. On every later
word the two passes give the same length. See "What gave nothing" below.

## Step 5: moves that change the order together with the cuts

After step 3 the search stalls. From the 43,930,623 word 18 million iterations found nothing. The search never moves
a trail and re-cuts its neighbours at the same time, and the pass never changes the order. The moves below do both.
In each of them the pass of step 3, or its tables, decides whether a move is kept.

### Block moves, with the pass inside the search

A whole run of pieces, or part of one, goes to another place without being cut again, and the pass runs every few
hundred iterations in a form that recomputes only the layers that changed. Neither helps alone. In a test from the
43,930,625 word, runs with both improved in 16 of 24 cases and runs with only one of them in 0 of 16. This search
runs on a GPU: the card finds the best place of each big trail.

| n | before | after | cost |
|---|---:|---:|---|
| 11 | 43,930,625 | 43,930,623 | 20,000 iterations |
| 12 | 522,745,530 | 522,745,505 | three rounds of 40 minutes on 2 threads, each followed by the pass |
| 12 | 522,745,505 | 522,745,498 | 5 minutes on 2 threads |
| 12 | 522,745,497 | 522,745,482 | one round of 20 minutes |
| 12 | 522,745,482 | 522,745,464 | eight more rounds |
| 13 | 6,747,917,970 | 6,747,917,866 | one round of 90 minutes on 4 threads, without block moves |
| 13 | 6,747,917,866 | 6,747,917,826 | the pass |
| 13 | 6,747,917,826 | 6,747,917,824 | 10 minutes with block moves |

Tools: `trailsearch_gpu.c` with `kern.cu`, driven by `rounds.sh`.

What it was worth: 65 letters at n = 12 in about five hours, between 522,745,530 and 522,745,464, and 146 at
n = 13. Per letter it is the slowest of the moves in this step. After relocation and segment insertion have run it
finds 1 to 4 letters per round or nothing.

### Relocation

From the tables of the pass, run from both ends, I get exactly what is saved by taking a window of neighbouring
trails out when all other cuts may change, and what it costs to put a trail somewhere else when its new neighbours
may be cut again. Windows whose saving is larger than the cost are moved. No random search is involved.

| n | before | after | cost |
|---|---:|---:|---|
| 12 | 522,745,526 | 522,745,483 | 751 seconds on one thread (a test on an earlier word) |
| 12 | 522,745,482 | 522,745,466 | 247 seconds (a side branch) |
| 12 | 522,745,464 | 522,745,445 | 4 minutes |
| 13 | 6,747,917,824 | 6,747,917,498 | 15 sweeps, 6,916 seconds on 8 threads |
| 13 | 6,747,917,464 | 6,747,917,445 | 5 sweeps |
| 13 | 6,747,917,441 | 6,747,917,437 | |
| 13 | 6,747,917,429 | 6,747,917,421 | |
| 13 | 6,747,916,915 | 6,747,916,901 | 5 sweeps, 2,567 seconds |

Tool: `relocate.c`.

What it was worth: 326 letters at n = 13 in under two hours, where the search had needed 90 minutes for 104. At
n = 11 it finds nothing on words that have been through the search and the pass.

### Loop moves

The trails and joins of a word form a balanced directed graph, and any connected balanced graph spells a word
(section 5 of Pantone's summary). So a trail may be written in two parts with a closed block of other pieces hung
between them. This pays when a join already passes through a cut of another trail.

| n | before | after | cost |
|---|---:|---:|---|
| 12 | 522,745,512 | 522,745,510 | 8 seconds |
| 12 | 522,745,505 | 522,745,504 | |
| 12 | 522,745,498 | 522,745,497 | |
| 12 | 522,745,376 | 522,745,375 | after a kick, see below |
| 13 | 6,747,917,498 | 6,747,917,464 | 40 rounds, 27 minutes on 8 threads |
| 13 | 6,747,917,445 | 6,747,917,441 | |
| 13 | 6,747,917,437 | 6,747,917,429 | |
| 13 | 6,747,916,917 | 6,747,916,915 | |

Tool: `loopscan.c`.

What it was worth: 1 to 3 letters at a time at n = 12 and 48 in all at n = 13. At n = 11 an exact scan finds no
such move on any of my words. It is cheap, so it stays in the cycle.

### Segment insertion

The sequence is cut at three to six joins and the blocks of pieces between the cuts are put together in another
order. With three cuts this is a 3-opt move without reversal. Each candidate is judged with the best cuts of the
whole new sequence.

| n | before | after | cost |
|---|---:|---:|---|
| 11 | 43,930,623 | 43,930,614 | four steps (621, 619, 615, 614), minutes each; the last is a move with five cuts |
| 12 | 522,745,445 | 522,745,383 | 23 minutes on 4 threads with the first version, 8 minutes with the second |
| 12 | 522,745,379 | 522,745,376 | 194 seconds |
| 12 | 522,745,374 | 522,745,366 | up to five cuts, 6 minutes on 2 threads |
| 13 | 6,747,917,421 | 6,747,916,917 | 24 rounds, 68 minutes on 8 threads, 12.6 GB |
| 13 | 6,747,916,901 | 6,747,916,888 | three cuts |

Tool: `segins.c`.

What it was worth: more than any other step. It found all of n = 11 after 43,930,623, where every other move had
stalled, and 504 letters at n = 13 in one run. The first version did not finish a single round at n = 13 in 57
minutes because two parts of its candidate search were cubic in the number of expensive joins. The second version
is the one in `tools/`.

### A new starting point when everything has stalled

When the passes find nothing, a short search at a constant high temperature (60,000 iterations) ends on a sequence a
few letters longer than the best. The passes start again from there.

| n | before | after | cost |
|---|---:|---:|---|
| 12 | 522,745,376 | 522,745,374 | one start |
| 12 | 522,745,366 | 522,745,356 | one start, 15 minutes with the passes |
| 12 | 522,745,356 | 522,745,355 | one start, 8 minutes |

Tool: `kick.sh`.

What it was worth: 13 letters at n = 12 from three starts. Nine more starts from 522,745,355 found nothing, and at
n = 11 none of the starts from 43,930,614 did.

### The last words on Pantone's pieces: more of segment insertion

| n | before | after | what | cost |
|---|---:|---:|---|---|
| 12 | 522,745,355 | 522,745,352 | moves that lengthen the word by one letter on purpose | six minutes on one thread for the first letter |
| 12 | 522,745,352 | 522,745,350 | one small change and its repair, many times over | a letter in 3 of 8 runs of nine minutes on one thread |
| 13 | 6,747,916,888 | 6,747,916,747 | five cuts, tables kept between rounds | 90 minutes on 8 threads, 12.5 GB |
| 13 | 6,747,916,747 | 6,747,916,693 | the same with long candidates valued exactly | 13 rounds of one to four minutes |
| 13 | 6,747,916,693 | 6,747,916,657 | five cuts with slack 1, candidates judged on the card | 15 minutes on 8 threads, 6.3 GB on the card |

At n = 12 the first of these are probe moves. In a round that gives no new best, up to ten moves that each add
one letter are made at free places. In the next round the move that takes a probe back is a candidate like any
other, so a probe stays only if something better has appeared next to it. At the level of the record this gave
three letters in 154 rounds. It is not in `tools/`: on the pieces of part two moves of equal length do this work,
and probes add little there. The second accepts one move of equal length and then looks for one move that repairs
it. Every letter it found came that way. It is `segins_ils.c`.

At n = 13 `segins.c` makes its tables again every round, 43 to 57 seconds each time. `segins_gpu.c` keeps them,
and that made five cuts affordable there. Its first round still listed 107,692 candidates, and 107,087 of them were
four-cut moves with an estimate that was too high. Giving the joins of long candidates their exact values took the
rounds from four to seventeen minutes down to one to four. On the plans where I compared them the versions write
the same plans. Judging the candidates on the card gives the same verdicts as the CPU code, and it made slack 1
affordable at n = 13.

Tools: `segins_gpu.c` with `segins_kern.cu`, `segins_ils.c`.

## The lengths in order, on Pantone's pieces

n = 11: 43,930,680 (Pantone), 674, 632, 628, 625, 623, 621, 619, 615, 43,930,614. Theo H.'s 43,930,624 came between
my 628 and 625.

n = 12: 522,745,581 (Pantone), 570, 548, 538, 537, 530, 526, 512, 505, 498, 482, 464, 445, 383, 379, 376, 374, 366,
356, 355, 354, 352, 351, 522,745,350. My 522,745,531 from step 3 is not on this line, which goes on from 530. Theo
H.'s 522,745,531 is a different word of the same length.

n = 13: 6,747,918,066 (Pantone), 058, 034, 6,747,917,995, 987, 970, 866, 826, 824, 498, 464, 445, 441, 437, 429, 421,
6,747,916,917, 915, 901, 888, 747, 693, 6,747,916,657.

Where the letters came from, counted along these lines:

| | n = 11 | n = 12 | n = 13 |
|---|---:|---:|---:|
| step 1, runs | 6 | 0 | 8 |
| step 2, search | 46 | 44 | 71 |
| step 3 and 4, one pass | 3 | 7 | 17 |
| search on the card, with the pass after each round | 2 | 69 | 146 |
| relocation | 0 | 19 | 371 |
| loop moves | 0 | 1 | 48 |
| segment insertion | 9 | 73 | 517 |
| new starts | 0 | 13 | 0 |
| the last words (kept tables, long candidates, the card, probe moves, local kicks) | 0 | 5 | 231 |
| total below Pantone's word | 66 | 231 | 1,409 |

The plans of the words in between are in [`plan/history/`](plan/history/README.md).

# Part two: other pieces

Everything in part one rearranges the closed trails of Pantone's words. On October 5 I changed the closed trails
themselves. The words at n = 10, 11, 12 and 13 got shorter by more than everything in part one together, and
n = 10 fell below rumstd's word for the first time. This part gives the steps in the order in which they were made.

[`reproduce/REPRODUCE.md`](reproduce/REPRODUCE.md) rebuilds each of the four words from its selection, with a
generator and a checker that share no code with the tools of part one. [`selection/`](selection/README.md) holds the
programs that found the selections and [`arrange/`](arrange/README.md) those that turn a set of closed trails into a
first plan.

## Selections

In Pantone's construction a selection decides which slices are taken from the 2-loops. I use his terms with the
shorthand of `reproduce/REPRODUCE.md`. A loop is a 2-loop on the K = n - 2 letters of the selection. A row is the
slice a selection takes from a loop: a full row has all K classes, a short row K - 2. A loop without a row is a loop
from which nothing is taken. Completion adds the last letter: the rows of a closed walk become a few long closed
trails, and every loop without a row becomes one small closed trail of its own. Transport carries a selection from
K to K + 1 letters.

Two numbers describe what a selection costs. Q is the number of classes its rows miss, and the cyclic words of
all closed trails together have F3(n) + Q letters, with F3(n) = n! + (n - 1)! + (n - 2)!. The second number is the
number of closed trails, because every closed trail has to be joined to the next and a join costs at least one
letter. So Q plus the number of closed trails is a floor for what a word pays above F3(n). A real word pays more,
and that payment, the cuts and joins, is what part one worked on for one fixed selection. Here the selection
changes. The trade is always the same: fewer closed trails for a larger Q.

| n | closed trails from | closed trails | Q | cuts and joins in the shortest word | shortest word |
|---|---|---:|---:|---:|---:|
| 10 | Pantone's selection | 364 | 2,352 | 521 | 4,034,873 (rumstd) |
| 10 | two closed walks where Pantone's has four | 350 | 2,352 | 503 | 4,034,855 |
| 11 | Pantone's selection | 2,800 | 18,816 | 3,318 | 43,930,614 |
| 11 | a walk put into every block (X) | 800 | 20,726 | 1,372 | 43,930,578 |
| 12 | Pantone's selection | 25,200 | 169,344 | 28,806 | 522,745,350 |
| 12 | blocks solved with full and short rows (C) | 7,200 | 178,080 | 15,355 | 522,740,635 |
| 12 | blocks solved with rows of other lengths (E) | 3,648 | 182,112 | 7,987 | 522,737,299 |
| 13 | Pantone's selection | 252,000 | 1,693,441 | 284,016 | 6,747,916,657 |
| 13 | C transported once | 72,000 | 1,780,800 | 88,844 | 6,747,808,844 |
| 13 | blocks solved on 12 symbols (N) | 23,808 | 1,818,768 | 44,907 | 6,747,802,875 |

"Cuts and joins" is the length of the word minus F3(n) and minus Q. The letters C, E, X and N are my names for
the selections in this file. Pantone's n = 13 word has one open path besides its closed trails, which is the odd 1 in
its Q.

## Blocks above the left-over loops

Pantone's selection on 8 symbols puts 672 of the 720 loops on two closed walks of full and short rows. 48 loops
are left without a row. At every later level each loop above a left-over loop gives one small closed trail of its
own: 336, 2,688, 24,192 and 241,920 loops for n = 10 to 13, one loop in fifteen. (His file writes these loops as
walks of full rows, which give the same number of closed trails as loops without a row do.) Above one left-over
loop lie 7 loops at n = 10, 56 at n = 11, 504 at n = 12 and 5,040 at n = 13. These are the loops in which the seven
old letters keep the cyclic order of the left-over loop. They give nearly all the closed trails: 24,192 of the
25,200 at n = 12.

The loops above one left-over loop form a closed problem, which I call a block. Closed walks inside a block whose
steps never exchange two old letters can take the place of "no rows", and the selection stays balanced. A block
depends only on the number of added letters, so one solution serves all 48 blocks. What a block solution is
measured by is Q + D, with D the number of its loops without a row, and later by a price that also counts the chains
its small trails fall into (see "Chains" below).

With full and short rows only:

* Two added letters (n = 11): nothing is better than no rows. The optimum of the block of 56 loops is 56.
* Three added letters (n = 12): the block of 504 loops has solutions of 308. This is the optimum among the
  solutions that are invariant under rotation of the seven old letters, by two programs with different models.
  Without the symmetry I know nothing better with full and short rows, and the bound is 270.
* Four added letters (n = 13): a native solution has a lower floor than the transported one but more chains, and
  loses on price.

Selection C uses one of the 308-solutions: per block 91 short rows, three closed walks and 126 loops without a
row. It has 7,200 closed trails at n = 12 where Pantone's has 25,200, for a Q that is 8,736 larger. C has full and
short rows only, so it transports: one transport gives 72,000 closed trails at n = 13 where Pantone's has 252,000.

The first words from C, with no search at all: n = 12 522,745,026 (the small trails written in chains, nothing
else), which was 324 under the best word on Pantone's pieces after everything in part one; n = 13 6,747,820,565,
which was 96,092 under.

## Rows of other lengths

Pantone's rules still work when a row shows any number v of classes, and not only K or K - 2. Such a row costs
K - v, and completion still covers every class exactly once (`reproduce/REPRODUCE.md` gives the rules for general
v). The idea came from my work on n = 7 and n = 8, where it gave no shorter word: the best word of that family at
n = 7 has 5,907 letters against the record of 5,905.

In the blocks it does help, from two added letters on:

* n = 10 (block of 7 loops): the optimum is 7, no rows. Nothing.
* n = 11 (block of 56 loops): the optimum of Q + D is 49 against 56, exact and without any symmetry imposed. The
  solution I use is the optimum when every chain of small trails costs 2 to 3 more: a walk of 42 rows in each
  block and 14 loops without a row, in three chains. With it the first word under 43,930,614 came out, 43,930,605.
  Then, in 10 of the 48 blocks, the block was rebuilt together with the 350 loops around it so that its rows lie on
  one of Pantone's big walks, and that walk then gives 2 closed trails instead of 8. This is selection X: 800
  closed trails.
* n = 12 (block of 504 loops): the optimum of Q + D with all row lengths is 301 against 308, again in the class
  invariant under rotation. The better words came from a solution chosen by price: selection E, 3,648 closed
  trails, whose 2,352 small trails make 1,104 units (768 chains and 336 single trails) where the 6,048 of C make
  2,544.
* n = 13 (block of 5,040 loops): selection N, found by neighbourhood search in the same symmetric class. Its
  first version has 24,000 closed trails where C transported has 72,000. The version of the final word has the
  same Q and the same number of loops without a row, and four walk trails fewer in every block: 23,808 closed
  trails. Neither is proved optimal. The only bound I have is a linear programme at 1,376 for Q + D per block,
  against 2,877 for N, and that bound is weak (see "How much is left").

Outside the blocks I found nothing. Pantone's walks are rigid there also with all row lengths: in 40 regions of
400 loops the cheapest change that uses a row of another length costs at least 8 more, and in 32 of them 9.

`selection/` builds all four selections again from Pantone's published file and a few small data files, and has
the searches that found the data files. Its README says for each search what it finds again today and what it
does not. The n = 10 selection and the block solutions of n = 11 and n = 13 are found again, on one machine and
with one version of the solver. The n = 12 block search was not run again. The 10 rebuilt blocks of n = 11 come
from an earlier state of their search, which does not find them again, and are kept as data.

## Why every n needs its own block search

Rows of other lengths do not transport. A row that misses three or more classes has no image one level up: an
exhaustive search over the candidates finds none for K up to 8 (`selection/transport_search.py`). That is computed
once and not proved. The cheapest lift of the n = 11 block to n = 12 that an integer programme finds costs at
least 577, where leaving all 504 loops without a row costs 504 (`arrange/liftmip.py`). So X, E and N are three
unrelated block solutions, each used at its own n only. Only C goes up, and it does not go down: it is not the
transport of any selection on 10 symbols.

## Chains

A loop without a row gives a small closed trail. Two small trails follow each other at the cost of one letter
exactly when their loops are consecutive in an F-orbit, that is, when one letter moves through the gaps of the
cyclic order of the others. `arrange/linkcheck.py` checks this on every cut of every small trail of a piece set.
Any other join between two small trails costs 2 letters or more, and in the optimised plans the small trail after
the end of a chain is reached for 4.8 letters on average.

So small trails have to be written in chains, and a selection pays roughly one letter per small trail plus four to
five per end of a chain. A chain, or a small trail that stays single, is a unit. What counts is the number of
units and not the number of closed trails:

* The largest set of cost-1 links is an integer programme (`arrange/chainplan.py`). For C it finds 3,504 links,
  which is also the upper bound, so the 6,048 small trails make 2,544 units.
* A fourth block solution, D, has fewer closed walks than C but its 9,072 small trails make 2,976 units. After
  the same passes its n = 12 word was 2,837 letters longer than that of C. I had predicted it 1,000 to 2,000 ahead.
* The search of part one, step 2, breaks chains. At n = 12 and n = 13 I start from the chained plan and run only
  the passes. At n = 11, where a search costs minutes, a short one from the chained plan is still the first step.
* At n = 13 with C transported the ten loops above one loop are a whole F-orbit: 6,048 chains of ten small trails
  at one letter per join, and the 3,504 links of n = 12 join them further into 2,544 units.
* In N the 12,768 small trails fall into 4,032 chains with 8,736 links, which is the optimum, and none stays
  single. At n = 11 the 672 small trails of X make 146 chains and 4 single trails.

| n = 12, letters per closed trail in the word | small trails | big trails | all |
|---|---:|---:|---:|
| Pantone's pieces, 522,745,350 | | | 1.14 |
| C, chained plan, 522,745,026 | 2.83 | 1.73 | 2.74 |
| C after three cuts, 522,743,110 | 2.60 | 1.57 | |
| E after three cuts, 522,738,261 | 2.84 | 1.51 | 2.45 |

A word on the new pieces pays more per closed trail and has far fewer of them.

## The order of the chains by integer programmes

Local moves do not find a good order of the chains. A link of cost 3 between two chains needs the right cut on
both trails of the link and on every trail of the two chains, and no single move makes that. For C at n = 12 I
computed the order instead. The 168 relabellings of the seven old letters map small trails to small trails with
their cuts, so an integer programme on the quotient by them is small. It chooses runs of small trails:

| run system | runs | joins inside the runs | plan as built | after three cuts |
|---|---|---|---:|---:|
| the local search before it | | | 522,742,718 | |
| links up to cost 3 | 1,344 (336 single, 672 of 5, 336 of 7) | 3,360 of cost 1, 336 of cost 2, 1,008 of cost 3 | 522,742,649 | 522,741,682 |
| links up to cost 4 | 1,008 (336 each of 5, 6 and 7) | the same and 336 of cost 4 | 522,741,902 | 522,740,945 |
| links up to cost 5, cuts at vertices only | 504 (168 of 10, 336 of 13) | the same and 504 of cost 5 | 522,741,478 | 522,740,898 |

After three cuts the third system was 47 letters ahead of the second. One cycle of moves of equal length took it
to 522,740,818. The line of the second system, with more such cycles, reached 522,740,635, and I did not go on
with the third. The first two systems are proved optimal among the symmetric systems with all cuts allowed, the
third only with cuts at vertices. With all cuts the best symmetric system of that level is not known: in the units
of the programme its value lies between 266, which this system has, and 276. The scripts are `arrange/q12.py` and
`arrange/q12b.py`.

At n = 13 with the first version of N the order of the 5,328 units (chains of small trails and chains of walk
trails) comes from an assignment problem: the cheapest successor for all units at once, the cycles joined
afterwards. That took the first plan from 6,747,808,751 to 6,747,807,339, before any pass.

## The lift from n = 12 to n = 13

For C the n = 13 problem is the n = 12 problem again, on cuts at vertices. Every small trail of n = 12 is one
chain of ten small trails at n = 13, and every walk trail is one chain of ten walk trails. A cut of the n = 12
trail at a vertex fixes the first and the last word of the whole chain. A join of cost c between two such cuts at
n = 12 is a join of cost c + 1 between the two chains at n = 13. So an n = 12 plan can be lifted
(`arrange/lift13.py`), and its n = 13 length is known before the word is written:

    10 + 6,747,720,000 + 9 x 6,048 + 10 x 1,152 + 7,199 + (the joins of the n = 12 order, cut at vertices).

I checked the rule by assertions on the words, for every unit. What does not lift is what an n = 12 plan gains from
cuts between two 2-cycles and from dropped duplicates: 1,463 letters of the plan I lifted.

| what was lifted | n = 13 length |
|---|---:|
| the run system with links up to cost 4 | 6,747,810,685 |
| the n = 12 word of 522,740,945 letters | 6,747,810,280 |
| the same after three cuts at n = 13 | 6,747,808,844 |

Selection N then went below this without any lift. `tools/segins_gpu.c` has an option that keeps only cuts at
vertices (`--gap3-list`), so that a search at n = 12 optimises exactly what lifts. It gives valid n = 12 words
whose lift is predicted at 6,747,809,330; I have not built an n = 13 word that way, because N overtook the lift
first. The same kind of lift is how I would try n = 14, where the word no longer fits into memory; I have not
tried it.

## Moves of equal length

On Pantone's pieces segment insertion looks for shorter moves and stops when there is none. On the new pieces a
round has tens of thousands of candidates that leave the length exactly as it is, because many small trails are of
the same kind and the estimate of a move is exact there: of 30,000 judged candidates with estimate 0, 29,991 kept
the length. The rule that uses this:

* every round judges the candidates with an estimate above 0 and E drawn at random from those with estimate 0;
* the shorter moves are taken first, the best first;
* then moves of gain exactly 0 are taken in random order wherever cuts and zones are free, except a move that
  would make a join again that was cut in the last 8 rounds;
* the word never gets longer.

After a round with about 50 such moves the next round typically has a hundred or more shorter candidates, of
which a few fit together. Measured on C at n = 12 with three cuts on 2 threads: shorter moves alone gave 6
letters in 2 rounds and then nothing; with moves of equal length in every round 6.1 letters per round over the
first rounds. A gaining move is then a new pairing of three chain ends with three chain starts.

| n | pieces | before | after | cost |
|---|---|---:|---:|---|
| 12 | C | 522,743,076 | 522,742,718 | the first runs of the rule, 2 threads |
| 12 | C | 522,740,945 | 522,740,635 | a loop of runs of 3 to 10 minutes; the last 37 letters on the card |
| 12 | E | 522,738,261 | 522,737,466 | three cuts, runs of 5 to 10 minutes; 10 further runs found nothing |
| 12 | E | 522,737,466 | 522,737,395 | four cuts with moves of equal length (455), five cuts (452), three cuts again (445), then a loop with four cuts (419, 415, 400, 395); nine more cycles found nothing |
| 13 | N, first version | 6,747,805,121 | 6,747,805,059 | 125 rounds in 1,119 seconds on the card, 18.8 GB |
| 13 | N | 6,747,804,887 | 6,747,803,439 | 195 rounds in 1,500 seconds (to 6,747,804,324), 408 rounds in 2,700 seconds (to 6,747,803,497), then 97 rounds; 10 threads and the card, 18.6 to 19.4 GB |
| 13 | N | 6,747,803,439 | 6,747,802,875 | 443 rounds in 3,000 seconds with the pair lists `--or3-v 5 --or3-x 4` in place of `--or3-v 4 --or3-x 5` (to 6,747,803,080), then 623 rounds in 3,000 seconds with the first lists again; stopped for the release |
| 11 | the selection before X, and X | 43,930,605 | 43,930,584 | 7 of these 21 letters; 1 of the 15 on X |

At n = 13 a round found 60 million moves with estimate 0, kept one in 31 and had about 490,000 candidates of equal
length to draw from.

On Pantone's pieces the rule has nothing to work with: 37 candidates of equal length per round at the n = 12
record plan. Its limits: the gain per round falls; with narrow pair lists it starves (330 to 360 candidates with
estimate 0 instead of about 3,500); on a plan that has not been through a pass with slack 0 it stores tens of
millions of moves.

Tool: `tools/segins_gpu.c`, option `--or3-eq`. The rule first ran in a variant of `segins.c` on the CPU.
`segins_gpu.c` takes the same moves in every round for the same seed, on the CPU and on the card, so it is the
only one in `tools/`.

## Local kicks

The loop of `tools/segins_ils.c` (a move that costs nothing or one letter, a local repair, keep if shorter or
equal and new) found nothing at n = 11 on Pantone's pieces. On the new n = 11 pieces it gave most of the last
letters: 13 of the 21 from 43,930,605 to 43,930,584 on the selection without the rebuilt blocks, and 14 of the 15
from 43,930,593 to 43,930,578 on X. At n = 10 it gave 4 letters once and then nothing in 49 runs. At n = 12 on E
it took over when the moves of equal length stopped giving: two loops on one thread each, in runs of seven
minutes, went from 522,737,395 to 522,737,299 in 77 minutes. They were still gaining when I stopped them for the
release. It has not run at n = 13.

## The n = 10 construction

At n = 10 rows of other lengths give nothing, and the passes above stopped at 4,034,880, seven letters above
rumstd's 4,034,873. The word of 4,034,855 letters comes from two things together.

The pieces: the selection has full and short rows as Pantone's, but two closed walks where his has four: 14 big
closed trails instead of 28, 350 closed trails instead of 364. Its 336 small closed trails are Pantone's small
closed trails with the letters relabelled.

The structure of rumstd's word, which I read off his word on Pantone's pieces: the 336 small trails form 48 groups
of seven. A group can be written as a path through its seven trails. It can also be closed into a loop: one of its
trails is written in two segments with the other six between them, and the group is entered and left at the same
cut. The five trails that rumstd's word writes in two segments are exactly this. His word is 8 chains of 6 groups
with the big trails in the gaps between them. My passes had lost their letters exactly there: 23 joins between
groups at cost 4, where 8 chains of 6 give 36 to 40.

So the word is constructed and not searched. rumstd's order of the 48 groups is carried over by the relabelling.
For that order the best cuts of every group and its mode (path or loop) are found exactly. The 14 big trails go in
as five blocks, each valued exactly in each of the 13 expensive gaps, and a small integer programme chooses the
gaps. That gave 4,034,860, and five and six cuts of segment insertion from it find nothing.

A second model works on chains. The cheapest ways through a group join each other at the lowest cost only along 56
closed chains of six groups, and there are 56 ways to split the 48 groups into 8 such chains. For each split an
integer programme chooses the order of the 8 chains, the join at which each is cut open and the big trails that go
into each gap, and the order it finds is valued exactly as before. With a first table of the big trails in the gaps
that gave 4,034,856, with a better table 4,034,855.

That length is the optimum of the family this model describes: the 48 groups stand as 8 runs of six, each run one
of the 56 chains cut open at one of its joins, the big trails stand anywhere between the runs or at the two ends,
each written once, and every cut and every mode of a group is free. Three computations close it. The join that
the model keeps in the middle of a chain is no restriction: for all 85,349,376 pairs of cuts at the two ends of a
chain the model gives the exact cost of its six groups. Every cheap sequence of big trails was listed by an
exhaustive search, and the others enter with a bound. Each of the 56 splits then has a certificate that no word
of the family is shorter, and 25 of them reach 4,034,855.

What this rests on: the certificates are linear programmes of one solver in floating point, with a smallest
margin of 0.04 where 1 is typical. The word, the cost of a chain, the values of the listed sequences and the
optimum were each computed in two ways that agree. Three things have one implementation only: that the search for
sequences of big trails is complete, the bound for the sequences it does not list, and the lists of the 56 chains
and the 56 splits. Nobody else has checked any of it.

What the repository reproduces is less. The scripts in `arrange/` write the plan of the word again, byte for byte,
and solve the model for all 56 splits with the 638 sequences of big trails it is offered: 25 splits reach 4,034,855
and none goes lower. The programs for the wider statement, with any sequences of big trails, ran once and are not
in the repository.

## The lengths in order

Each number is a word that passed `delcheck`. The first entry of each line is the best word on Pantone's pieces.

n = 10: 4,034,873 (rumstd). On the pieces of the selection with two closed walks: 4,034,895 (search and passes),
884 (five cuts), 880 (local kicks), 860 (the construction), 856 and 4,034,855 (the model over the chains).

n = 11: 43,930,614. On the selection with a walk in every block: 43,931,193 (chained plan), 43,930,699 (480
seconds of the search of part one), 611 (three cuts), 607 and 605 (five cuts), then 584 by local kicks, moves of
equal length and one probe move. On X: 43,930,593 after the same passes, 43,930,578 by local kicks and one move of
equal length.

n = 12: 522,745,350. On C: 522,745,026 (chained plan), 522,743,110 (three cuts, 158 seconds on the card), 076
(four cuts), 522,742,718 (moves of equal length), 649 (first run system), 522,741,682 (three cuts), 522,740,945
(second run system and three cuts), 635 (moves of equal length). On E: 522,739,939 (chained plan), 522,738,261
(three cuts), 522,737,971 and on to 522,737,466 (moves of equal length with three cuts), 455 (the same with four
cuts), 452 (five cuts), 445 and on to 522,737,395 (moves of equal length with three and four cuts),
522,737,299 (local kicks, stopped for the release).

n = 13: 6,747,916,657. On C transported: 6,747,911,676 (the base word itself, with the small trails in their
chains), 6,747,820,565 (chained plan), 6,747,813,583 (greedy order of the units), 6,747,812,160 (three cuts in
stages, loop moves), 6,747,810,280 (the lift), 6,747,808,844 (three cuts). On the first version of N:
6,747,808,751 (greedy start plan), 6,747,807,339 (order by assignment), 6,747,805,729 and 6,747,805,121 (three
cuts), 6,747,805,059 (moves of equal length). On N: 6,747,807,082 (first plan), 6,747,805,084 and 6,747,804,887
(three cuts), 6,747,804,324, 6,747,803,497 and 6,747,803,439 (moves of equal length),
6,747,803,080 (the same with other pair lists), 6,747,802,875 (the first lists again, stopped for the release).

Where the letters below the best word on Pantone's pieces came from, along these lines:

| | n = 10 | n = 11 | n = 12 | n = 13 |
|---|---:|---:|---:|---:|
| the pieces with their first plan (chains, order of the units) | | | 5,411 | 109,575 |
| segment insertion with three cuts | | | 1,678 | 2,195 |
| moves of equal length, with three to five cuts | | | 866 | 2,012 |
| local kicks | | | 96 | |
| total | 18 | 36 | 8,051 | 113,782 |

For n = 12 (selection E) and n = 13 (selection N) the first row is the first plan against the best word on
Pantone's pieces, and the other rows are the passes on it. At n = 10 and n = 11 the first plans are longer than the
old records and the pieces pay off only after the passes, so only the total is given.

# What gave nothing

Each item says what was tried and the numbers that show the result.

## On the words, with Pantone's pieces

* More of the plain search. From the 43,930,623 word 18 million iterations found nothing. At n = 12 the last 3
  hours on 18 threads gave one letter. A hotter second set of options (`--kmax 18 --T0 1.0`) at n = 12 gave nothing
  in the two rounds it ran.
* More search at n = 11 after 43,930,614. Twelve searches of 100,000 iterations with moves judged after re-cutting,
  three new starts each followed by all passes, and the five-cut pass on a different word of 43,930,618 letters
  reached by another route: nothing below 614. With five cuts and slack 4 the pass lists 12,808 candidates at 614
  and none is shorter. The 9 sequences of equal length next to it have no shorter neighbour either.
* The run level of step 1 after the first gain. A second round at n = 11 stayed at 939 with a bound of 935. See the
  table of step 1 for n = 10 and n = 12.
* The fixed-order pass on windows inside the search, around every accepted move. No gain over one pass at the end
  in 8 runs.
* An assignment neighbourhood: a set of trails is taken out and put back into the places the others leave, all at
  once by one assignment problem, with the cuts of the others fixed. Gain 0 on three words (43,930,623, 522,745,531,
  522,745,526). The trails are rigid: at n = 12 25,145 of 25,187 trails have no other place that costs 2 letters or
  less while their neighbours keep their cuts.
* A removal rule guided by the symmetries of the trails. 0 new best words in 54 trials, against 1 in 38 for the
  controls.
* Reordering inside windows of K consecutive pieces with all cuts free (the neighbourhood of Balas and Simonetti).
  Nothing on the 43,930,623 word up to K = 9. It does take Pantone's raw n = 11 word from 680 to 674 with K = 3.
* Moves on letters, without the trails. In the 43,930,623 word no substring of any length can be deleted, no window
  of up to 49 letters can be replaced by a shorter one, and no exchange of two or three parts of the word or chain
  of up to 7 cuts gives a shorter word. The exchanges that gain only make loops that are detached from the word.
  That observation led to the loop moves.
* Loop moves at n = 11. An exact scan finds no such move that shortens the 43,930,623 or 43,930,628 words, Theo
  H.'s word or Pantone's. No join in them passes through a cut of another trail.
* Cuts inside a 1-cycle on later words. On 43,930,623, 522,745,526 and 522,745,498 the pass with these cuts gives
  the same length as the pass without. A search with them from Pantone's n = 11 word ended at a mean of 651.1 against
  654.4 without, over ten runs, which is inside the noise. Relocation and segment insertion with these cuts find
  nothing on the 43,930,614 and 522,745,355 words. A whole pass of segment insertion from 522,745,445 ended at 397
  with them and at 383 without, at almost four times the cost.
* Merging several plans exactly. The union of the cuts of 27 n = 11 plans, solved as an integer programme: the
  43,930,623 word is optimal in it. Crossing the plans block by block gains 0. 57 windows of 24 pieces around the
  expensive joins are each optimal for one cut per trail.
* Wider settings of segment insertion that let moves of one round lie closer together. More moves per round, but
  the run from 522,745,445 ended at 393 instead of 383.
* Strong new starts at n = 11. A start that ends 13 letters up comes back to 6 above the record, one that ends 240
  up to 64 above.

## On Pantone's pieces themselves

* Other traversals of the same trails. No two trails of Pantone's words touch at any level: every cut vertex, every
  1-cycle and every step of weight 2 belongs to one trail. The cheapest change that merges two trails costs exactly
  h letters, against 1.2 letters for an average join at n = 11. Twins of the small trails under a swap of two letters
  and 2,324 exchanges inside the big trails at n = 11 exist, and all give the same lengths.
* Other selections at n = 9. None beats Pantone's there. Sixteen ways to splice the walks again give 408,731 to
  408,736, unspliced cycles 408,798, selections with fewer short rows 408,819 to 408,895. The 48 isolated small
  trails of n = 9 cost 149 letters to join, and every maximum packing I sampled leaves 48 of them. From n = 10 on
  this is different, and the loops above those 48 are where part two begins.
* The search at n = 9 and n = 10 from rumstd's words. Several hours and more than 2 million iterations each:
  nothing. For n = 9 the section on what is left says why. The n = 10 word of part two was constructed, not found
  by this search.

## On the new pieces

* Other block solutions at n = 12. The first two, A and B (11,856 and 10,416 closed trails), ended at 522,750,126
  and 522,747,315. D, with fewer walks and more chains than C, ended 2,837 letters behind C after the same passes.
  F (7,344 closed trails, rows of other lengths) starts 5,726 letters above E with its chained plan; its pass did
  not finish.
* Other block solutions at n = 11. One with 28 rows that ties with the one I use in the block price: 43,930,668
  against 43,930,607 after the same light passes. Rebuilding 12 blocks instead of 10 onto big walks: 43,930,586
  against 43,930,578. A walk of 20 rows: 43,930,776.
* Rows of other lengths at n = 10. The block of 7 loops has no better solution than no rows.
* Four added letters with full and short rows only. A lower floor than C transported (3,046 against 3,110 per
  block) but 203 chains per block against 126, and it loses at every price I tried.
* Block searches without the symmetry. With three added letters a search from scratch reached 317 against the 301
  of the symmetric class. With four added letters the sub-models of 1,000 to 2,600 loops did not finish in the time
  and memory I gave them. Larger symmetry classes are worse (336 with three added letters).
* Run systems with links above cost 4. The system with links up to cost 5 gave no shorter word than the one
  below it: 47 letters ahead after three cuts, 522,740,818 after one cycle of moves of equal length, against
  522,740,635 on the other line. The next levels keep producing cycles that have to be broken by hand.
* The search of part one on the new pieces at n = 12. On A it reached 522,753,420 in 387 seconds on the card and
  levelled off: it breaks the chains. At n = 11 a short search from the chained plan is still the first step.
* Loop moves and relocation. n = 10: nothing. n = 13 on C: loop moves 7 letters, relocation one letter in 20
  minutes. n = 12 on C: relocation alone reached 522,744,313 in four sweeps where three cuts reached 522,743,110.
* Segment insertion beyond three cuts. Three cuts with slack 1 on C without moves of equal length: nothing. Six
  cuts with slack 3 at n = 11: nothing. Four cuts at n = 13 with narrow pair lists: the memory holds now, but a
  round has 26,097,749,606 candidates, about 36 hours of judging, because a join that is not listed counts as 4 in
  a move made of two pairs. With wider lists it has not run.
* Probe moves (one letter longer, taken back unless something better appears) on the new pieces: two letters at
  n = 11, little at n = 12.
* Cutting only at vertices at n = 12, so that an n = 12 search optimises exactly what lifts to n = 13. The option
  exists and gives valid words (522,741,458, predicted n = 13 length 6,747,809,330); no lifted word came from it,
  because selection N overtook the lift.

## On speed

These gave speed or nothing, and no letters.

* Rust. Ports of `delcheck`, the fixed-order pass and the inner loop of the search run within 2 %, 6 % and the
  noise of the C programs, with the same memory. I stay with C.
* Compiler options. `-O3`, `-march=native`, link-time optimisation and alignment options are all inside 4 % of
  `-O2`. Two things matter: `-mpopcnt` halves the loading time and nearly doubles `delcheck`, and profile-guided
  optimisation makes the search 25 % faster. clang is about 10 % slower than gcc.
* Pinning threads to cores. 17 % more iterations per second at 8 threads on the first version of the search. I did
  not merge it, because by then the search was no longer what limited progress.
* A different layout of the index of the search. 3.3 times faster than the first version on its own, but it attacks
  the same two costs as the speed-ups that are in `trailsearch.c` now and I did not merge it.
* On the card: waiting so that more jobs share one launch, one context per thread, a kernel that stays on the card
  with a mailbox, smaller blocks. None helped. One launch per exchange did, by a factor of 2 to 4 on a shared card,
  and is in `trailsearch_gpu.c`.

# How much is left

Everything in this section is a computation inside one family of words on one set of closed trails. None of it is
a lower bound for superpermutations, and nobody has refereed any of it.

## On Pantone's pieces

For n = 9 the answer is nothing, inside the families of words that these tools produce. rumstd's 408,731 is
optimal among all words made from the 52 closed trails of Pantone's n = 9 word with one cut per trail, with or
without cuts inside a 1-cycle, and among all words with any number of cuts per trail and overlaps of at most n - 3
letters. The proof is a counting argument whose finite facts are checked by exhaustive computation. The scripts are
in [`proofs/n9/`](proofs/n9/README.md).

For n = 10 and n = 11 the same method, with a sharper programme for the blocks of trails, gives bounds that are not
tight.

| n | shortest word on these pieces | one cut per trail | small trails in any number of segments, big trails in one | any number of cuts per trail |
|---|---:|---:|---:|---:|
| 9 | 408,731 (rumstd) | at least 408,731 | | at least 408,731 |
| 10 | 4,034,873 (rumstd) | at least 4,034,860 | at least 4,034,849 | at least 4,034,835 |
| 11 | 43,930,614 | at least 43,930,481 | | at least 43,930,373 |

At n = 11 that leaves 133 letters between the word and the bound for one cut per trail: about 80 of them in the
two blocks of 56 big trails and about 50 in the joins between classes of small trails. The n = 10 word of part two is
shorter than the bound in this table for one cut per trail. That is no contradiction: it is made of other closed
trails.

## On the new pieces

| n | pieces | shortest word | bound | for which words |
|---|---|---:|---:|---|
| 10 | two closed walks where Pantone's has four | 4,034,855 | at least 4,034,848 | one cut per trail |
| 10 | | | at least 4,034,842 | small trails in any number of segments, big trails in one |
| 10 | | | 4,034,855, the optimum | the groups in 8 runs of six along the chains (the second model of the n = 10 section) |
| 12 | C | 522,740,635 | at least 522,736,830 | one cut per trail, with cuts between two 2-cycles and dropped duplicates |
| 11, 12, 13 | X, E, N | 43,930,578, 522,737,299, 6,747,802,875 | none | |

At n = 10 the word is the optimum of the family of its model, with the limits given in the n = 10 section. From
one optimal word of each of the 25 splits that reach it I moved every segment of one to four consecutive groups or
big trails to every other gap and valued the result exactly. No move gives a shorter word: the best ones keep the
length in four splits and cost a letter in the others.

A shorter n = 10 word on these pieces would have to do one of four things. It could break a chain: cut it into
two runs, or put a group or big trails between two of its groups. It could write a small trail in three or more
segments, or close a loop around other pieces. For these two the bound of 4,034,842 holds, 13 letters below the
word. It is a linear relaxation, and I have an argument, not a computation, that better prices cannot raise it.
It could write a big trail in more than one segment, and for that I have no bound. Or it could use an overlap of
more than 7 letters, or other closed trails.

For C at n = 12 the bound says more than one number. The small trails alone need at least 12,432 letters of cuts
and joins, the best run systems I constructed need about 13,900 and the word pays about 15,100. Part of this
bound is a linear programme solved in floating point, and there is no second implementation of it.

For N at n = 13 the only figure is for the start plan: the joins between its 5,280 units cost 29,328 letters and
an assignment bound for them is 27,712 (`arrange/plan13n.py`). So more can only come from cutting inside the chains
again, which is what the passes then did.

The selections themselves are not known to be optimal. For the block of 504 loops the best Q + D is somewhere
between 224 and 300 when rows of all lengths are allowed and no symmetry is imposed, and 301 is the optimum under
rotation. The blocks in use cost more: 308 for C, the optimum with full and short rows under rotation, and 315 for
E, which was chosen by price. For the block of 5,040 loops the block in use costs Q + D = 2,611 + 266 = 2,877, the
best I found for Q + D alone is 2,849, and the only bound is 1,376. That bound is a linear relaxation. It holds
for every solution, symmetric or not, and it is weak: the same relaxation gives 182 for the block of 504 loops,
where the optimum under rotation is 301. So it does not say how much a better block could give.

## The constant

Pantone's bound is S(n) <= n! + (n - 1)! + (n - 2)! + (43/80 + o(1)) (n - 3)!. Selection C has full and short
rows only and transports to every n, so it has a constant of its own. What I can say about it:

* Its floor, Q plus the number of closed trails, is 193/378 = 0.510582 times (n - 3)! at n = 12 and n = 13. For
  Pantone's selection the same count gives 193/360 = 0.536111. The count is made by a checker that shares no code
  with the program that builds the selection (`selection/check12.py`). That a transport keeps this ratio at every
  larger n rests on a short argument that is not written out here and that nobody else has checked.
* With connector cycles chosen explicitly at n = 12 (203 cycles that meet the 1,152 walk trails, checked by two
  programs), sections 4 and 5 of Pantone's summary applied to this selection give

      S(n) <= n! + (n - 1)! + (n - 2)! + (1771/3456 + o(1)) (n - 3)!,     1771/3456 = 0.512442.

  I checked the hypotheses of his argument for this selection by computation and did not prove the argument
  again for it. The rule that carries the cycles one level up was checked literally on two levels and has no
  written proof for one kind of walk. The cycles at n = 13 are not built, and 203 is not known to be the least
  number (the bound is 201). Read it as a statement to be checked and not as a theorem.

X, E and N have rows that do not transport. They say nothing about the constant.

# How the words were checked

Three programs that share no code:

1. `reproduce/tools/check_min.py`: every permutation occurs (numpy, one bit per permutation, about 60 lines).
2. `tools/delcheck.c`: every permutation occurs and no single letter can be deleted.
3. Pantone's `literal_check --deletions`: the same two statements.

All three passed on each of the four words. For n = 13 `literal_check` ran under Linux: 18 minutes and about
13 GB.

The selections were checked before any word existed: every loop has at most one row, the selection is balanced,
and the closed trails are found in two ways that must agree (at n = 13 in one way only, for memory). The program
that does this for the four words, `reproduce/tools/geng.py`, was written from the description of the rules alone
and shares no code with the programs that searched for the selections. A second checker, `selection/check12.py`,
counts loops, rows, Q and closed trails of each whole selection and agrees.
