# Arranging the pieces

A piece set is a family of closed trails that together hold every permutation. A word is these trails written one
after the other, each cut open at one place. This folder holds the programs that choose a first order and first
cuts, a start plan, before any local search runs. It also holds the programs behind the statements I make about
arrangements: which chains exist, how good a system of runs can be, what an n = 12 plan gives at n = 13, and how far
the lower bounds lie below the words.

The piece sets themselves come from the reproduction folder: `geng.py` or `gen12.py` turn a selection into a base
word and its table, `applyplan.py` turns a plan into its word, `check_min.py` and `delcheck` check the word. The
passes that shorten a plan afterwards are in `tools/`. Nothing here loads a word into a search model. The scripts
map the base word and read the short words at the ends of pieces from it.

    bash test.sh REPRO WORK

runs what can be run in a few minutes and compares it with the numbers below (see Tests at the end).

I use the terms of `REPRODUCE.md` (loop, row, loop without a row, small trail, closed walk, closed trail, piece,
cut, vertex, join, plan). A few more:

- h = n - 3. A piece cut at a vertex starts and ends with the same h letters. A cut at a vertex is free; a cut at a
  step of weight 2 costs one letter.
- The cost of a plan is its cuts plus its joins, and length = h + sum R + cost. The selection fixes sum R, so a plan
  decides only the cost.
- An F-orbit (c, m) is the K - 1 loops that come from a cyclic order c of K - 1 letters by putting the letter m into
  each of its gaps in turn (K = n - 2 letters in a loop).
- A chain is a sequence of trails that follow each other at cost 1 (small trails) or 0 (trails of one walk).
- A unit is a chain or a single trail, handled as one object with a first and a last word.
- An event is one piece as a plan writes it. A trail written in two segments is two events. The programs print
  this word.
- A run, in the n = 12 programs, is a maximal sequence of small trails joined below a given level of cost.
- W is the cost of a join in half letters with the cuts counted in: W(x, y) = 2 (join) + (cut of x) + (cut of y).

## How a piece set becomes a plan

### Small trails go into chains

The small trail of a loop x has one vertex for every letter m of x: the word "x without m, read from the letter
after m". Two small trails can follow each other at cost 1 exactly when their loops are consecutive in an F-orbit,
and then each is cut at its vertex without the mobile letter of that orbit. `linkcheck.py` checks this on every cut
of every small trail (651 such pairs at n = 11, 3,024 at n = 12; the set of pairs that join at cost 1 and the set of
neighbours are equal). A trail has one cut, so a chain of three or more stays inside one orbit, and the largest set
of links is an integer programme: `chainplan.py`. It is small and solves to optimality in a second, so the number of
units of a piece set (chains and single trails together) is exact: 146 chains and 4 single trails for the 672 small
trails at n = 11, 768 chains and 336 single trails for the 2,352 at n = 12.

This comes first because of what a chain end costs. In the n = 12 start plan the 1,248 joins inside chains cost 1
letter each, and the 1,104 joins that follow a chain or a single small trail cost 5.8 on average. A piece set pays
for its small trails by the number of chain ends, and a search that starts from an arbitrary order does not find the
chains. The fixed-order pass on the base word as written gives 522,744,506 letters at n = 12; the chained plan has
522,739,939.

### Trails of one walk chain at cost 0

The K - 1 trails that the completion makes of one walk pass a full row of the walk with the completion letter in
consecutive gaps. Cut each at the step of weight 2 after "its" class of that row (one letter each), and each piece
ends with the word the next begins with. At n = 13 the start plan does this for the walks (`plan13n.py`,
`gen13.py`). At n = 11 and n = 12 `chainplan.py` leaves the walk trails as the fixed-order pass cut them, which
finds the same joins where the base word has the trails of a walk side by side.

### Chains become units, and the units get an order

A chain has a fixed first and last word. `chainplan.py`, `gen13.py` and `order13.py` order the units greedily: after
a unit, the unused unit whose first word overlaps its last word most. `plan13n.py` does better with an assignment:
the cheapest successor for all units at once, the cycles of that assignment joined one by one, the cuts of the walk
chains chosen again. The value of the assignment is a lower bound for a closed order of these units with these end
words. At n = 13 it says that reordering whole chains is almost used up: the joins between the 5,280 units of the
start plan cost 29,328 letters against 27,712. What is left has to come from other cuts inside the chains, and that
is the work of the local passes.

### Run systems at n = 12

On the first n = 12 piece set that beat Pantone's pieces (full and short rows only, 7,200 trails, 6,048 of them
small) I looked for better systems than cost-1 chains: runs of small trails that also use joins of cost 2, 3, 4, 5.
A join of cost 3 needs the right cut on both trails and on every trail of the two chains it connects, so local moves
from the chained plan do not find them. The cuts of the small trails are kept by 168 relabellings of the old letters
(`sym12.py`), and every orbit of cuts has 168 cuts. On the quotient the problem is small: `q12.py` solves its linear
relaxation (an upper bound on what any system can save), `q12b.py` solves it in integers and expands the solution by
the group to a real system of runs, `build12.py` turns a system into a plan.

### The lift from n = 12 to n = 13

If the n = 13 pieces come from the same selection by one more transport, every n = 12 trail corresponds to one unit
of ten trails at n = 13, and a join of cost c between two vertices at n = 12 is a join of cost c + 1 between the
units. So an order found at n = 12 is an order at n = 13 with a known length (`lift13.py`). Cuts at steps of weight
2 and cuts that drop a repeated permutation do not lift.

### The n = 10 construction

The pieces are 48 groups of seven small trails and 14 big trails. A group can be passed in one run for a
W-sum of 12, or closed into a loop and hung on one cut of one of its trails, which is then written in two segments.
The loop is rumstd's device, from his word of 4,034,873 letters. `tl10.py` takes an order of the 62 objects and
finds the best cuts and the best mode of every group exactly. What remains is the order. The cheapest passes through
the groups join each other at W = 8 in exactly 56 cycles of six groups (`trav10.py`); I call them chains. The 48
groups can be split into 8 chains in 56 ways (`parts10.py`). For each split an integer programme chooses the order of
the chains, the join at which each is cut open, and which big trails stand in which gap (`chain10.py`). `plans10.py`
values the result exactly and writes the plan. 25 of the 56 splits give 4,034,855.

## What is exact, what is optimal in which class, what is a heuristic

| statement | program | status |
|---|---|---|
| pairs of small trails that join at cost 1 = neighbours in an F-orbit | `linkcheck.py` | exhaustive over all cuts of the small trails of the piece set given |
| largest number of cost-1 links, smallest number of chains | `chainplan.py`, `plan13n.py`, `gen13.py` | optimal (integer programme, solver status 2) |
| order of the units | the same, `order13.py` | heuristic (greedy; assignment with patching) |
| "assignment bound" | `plan13n.py` | lower bound for a closed order of these units with these end words only |
| run systems of level 8, 10, 12 | `q12b.py` | optimal among symmetric systems: level 8 and level 10 with all cuts, level 12 with cuts at vertices; level 12 with all cuts is not settled; not shown to be optimal among all systems |
| sum over runs at a level | `q12.py` | bound by a linear programme in floating point, not certified; equal to the integer optimum at level 6 (`runs12.py`) |
| plan from a run system | `build12.py` | heuristic |
| length >= 522,736,830 on the first n = 12 piece set | `bound12.py`, `hop12.c`, `attach12.py`, `q12.py` | lower bound for words that write every trail once with overlaps of at most h; exact integer block values, floating-point linear programmes for the runs; one implementation, not refereed |
| length of a lifted plan | `lift13.py` | exact, asserted on the words while it runs; two lifted words were rebuilt and checked |
| cuts and modes for a given order of the groups and big trails at n = 10 | `tl10.py` | exact (dynamic programme over the cuts) |
| the 56 chains, the 56 partitions into 8 chains | `trav10.py`, `parts10.py` | exhaustive |
| order of the chains and places of the big trails, per partition | `chain10.py` | optimal in its model (solver status 2 for all 56 partitions): these chains, with the 638 sequences of big trails it offers as blocks; not a bound for other arrangements |
| bounds for Pantone's pieces at n = 10 and n = 11 | `cert10.py`, `cert11.py` | exhaustive integer computation, cross-checked as described in the headers, not refereed |
| rows of other lengths do not transport | `liftmip.py` | integer programme; optimal on the two small cases, a bound on the n = 11 block |

Every bound here is a bound for one piece set and one family of words. None of them says anything about another
piece set, and none is a lower bound for superpermutations.

## Commands and expected results

The commands are written for a folder that holds `selections/` and `tools/` of the reproduction package next to
`arrange/`, with a directory `work/` for what is produced. `recut` is the fixed-order pass of `tools/` (`recut
BASE.txt OUT.txt --co-skip --time 0` writes the plan `OUT.txt.plan`). Several scripts import `gen12.py` and
`geng.py`:

```sh
export PYTHONPATH=tools
```

Scripts that need Gurobi say so in their header: `chainplan.py`, `plan13n.py`, `gen13.py`, `liftmip.py`,
`joins12.py`, `runs12.py`, `q12.py`, `q12b.py`, `chain10.py solve`. The size-limited licence that comes with the
PyPI package is too small for all of them. Gurobi is not needed to rebuild or check any word: the plans are
published. Times and memory are from runs on one machine with two threads while other jobs ran; read them as orders
of magnitude.

### n = 11 and n = 12: the chained plan

```sh
python tools/geng.py selections/n11-selection.txt work/n11-base.txt --table work/n11-base.tsv
./recut work/n11-base.txt work/n11-dp.txt --co-skip --time 0 --threads 1
python arrange/chainplan.py work/n11-base.txt work/n11-base.tsv work/n11-dp.txt.plan work/n11-chain.plan
python arrange/plancost.py work/n11-base.txt work/n11-base.tsv work/n11-chain.plan
python arrange/linkcheck.py work/n11-base.txt work/n11-base.tsv
```

The same lines with `n12` give the n = 12 plan (unpack the selection first, as in `REPRODUCE.md`).

| | n = 11 | n = 12 |
|---|---|---|
| base word; after the fixed-order pass | 43,935,602; 43,932,949 | 522,762,033; 522,744,506 |
| small trails | 672 | 2,352 |
| pairs of loops without a row that are neighbours | 651 | 3,024 |
| links used (solver status 2, bound equal) | 522 | 1,248 |
| chains | 146 (39 of 2, 6 of 3, 17 of 4, 84 of 6) | 768 (288 of 2, 480 of 3) |
| single small trails | 4 | 336 |
| units = small trails - links (the program prints this number as "chains") | 150 | 1,104 |
| events of the plan | 800 | 3,648 |
| length of the chained plan | 43,931,105 | 522,739,939 |
| SHA-256 of the plan | 0feeeb14e2d9de6795f25509303a003d95263bbd534fcd0625593769b57feab3 | 93d6c671c24a53c7eb1457b3b3fd7d9562484b8b29654da8f468497619f30cb6 |
| word after the local passes | 43,930,578 | 522,737,299 |

Both plans rebuild to valid words of these lengths (`applyplan.py`, then `delcheck`: nothing missing, no letter can
be deleted). They are the plans the passes started from. Which optimal set of links the solver returns can depend on
its version; the hashes are those of Gurobi 13.0.3 with two threads. Another optimal set has the same number of
units and may give another length.

`plancost.py` on the n = 12 plan: the small trails cost 3.23 letters each (7,600.5 for 2,352), the trails of the
long walks 1.73 each, the plan 10,618 in all.

### n = 13: the start plan of the word

```sh
xz -dc selections/n13-selection.txt.xz > work/n13-selection.txt
python tools/geng.py work/n13-selection.txt work/n13-base.txt --table work/n13-base.tsv --noliteral
python arrange/plan13n.py work/n13-selection.txt work/n13-base.txt work/n13-base.tsv work/n13-start.plan
python arrange/plancost.py work/n13-base.txt work/n13-base.tsv work/n13-start.plan
```

`plan13n.py` maps the base word (6.7 GB on disk) and reads only 10-letter words from it. It prints:

| | |
|---|---|
| rows, loops without a row, closed walks | 3,616,032, 12,768, 1,248 |
| pairs of neighbouring loops without a row; links used | 13,440; 8,736 (status 2, bound 8,736) |
| chains of small trails | 4,032 (1,296 of 2, 768 of 3, 1,968 of 4), no single trail |
| walks whose 10 ports are 10 trails | 1,056, each a chain of 10 at cost 0 |
| other walks | 192, in 144 chains of 2 and 48 chains of 4 |
| joins between units, greedy order | 30,670 |
| after assignment rounds 1, 2, 3 | 29,377, 29,367, 29,328 (assignment values 27,744, 27,721, 27,712) |
| events; cuts at steps of weight 2 | 23,808; 11,040 |
| length of the plan | 6,747,807,082 = 10 + sum R + 49,104 (2.06 letters per trail) |
| SHA-256 of the plan | 93a4946eba5d2493a802b912604c3871a4ef6c57653491dbe5a706f752d8de06 |

185 s and 1.05 GB (numpy held to two threads). The word of this plan was built and checked before the passes
started. The passes took it to 6,747,802,875.

### n = 13 from the transported selection, and the lift

This is the earlier route to n = 13. Its words are longer than the one above (best: 6,747,808,844) and it is here
for what it shows: one transport multiplies every count by ten, the small trails come in whole chains of ten, and a
plan at n = 12 carries over.

`data/n12t-selection.txt.xz` is the 11-symbol selection with full and short rows that this route starts from. The
selection folder builds the same file (SHA-256 of its data lines 12cfdcf1...8c47c7a3).

```sh
xz -dc arrange/data/n12t-selection.txt.xz > work/n12t-selection.txt
python arrange/verify.py work/n12t-selection.txt
python arrange/gen13.py work/n12t-selection.txt work/n13t-base.txt --table work/n13t-base.tsv \
    --plan work/n13t-chain.plan
python arrange/order13.py work/n12t-selection.txt work/n13t-base.txt work/n13t-base.tsv \
    work/n13t-chain.plan work/n13t-order.plan
```

| | |
|---|---|
| `verify.py` | every loop once, balanced by both tests, 256 closed walks, Q = 178,080, 7,200 closed trails after completion, floor (Q + trails) / 9! = 193/378 |
| `gen13.py` | 72,000 closed trails (60,480 small), 41,697,600 slices, sum R = 6,747,720,000 = F3(13) + 1,780,800; base word 6,747,911,676 letters; 290 s, 0.18 GB |
| its plan | 2,544 units of small trails, 1,152 walk chains; 6,747,820,565 letters |
| `order13.py` | 6,747,813,583 letters; 539 times no unit overlapped; 89 s, 0.46 GB |

With `--no-word` `gen13.py` writes the table and the plan without the 6.7 GB word. Both words were built and checked
at the time.

The lift needs the n = 12 pieces of the same selection and their file of cuts:

```sh
python tools/gen12.py work/n12t-selection.txt work/n12t-base.txt --table work/n12t-base.tsv
gcc -O2 -o cuts12 arrange/cuts12.c
cd work
export PYTHONPATH=../tools
../cuts12 n12t-base.txt n12t-base.tsv cuts12c.bin
python ../arrange/lift13.py PLAN12 n13t-lift.plan n12t-selection.txt n13t-base.txt n13t-base.tsv
```

PLAN12 is any plan on `n12t-base.txt` that writes every trail once.

What lifts is the order of the trails, with every trail cut at a vertex. Every small trail of n = 12 is one chain of
ten small trails at n = 13, every other trail one chain of ten walk trails, and a join of cost c between two
vertices at n = 12 is a join of cost c + 1 between the two units. So

    length at n = 13 = 6,747,793,161 + (joins of the n = 12 order with every trail cut at a vertex).

Cuts at steps of weight 2 and cuts that drop a repeated permutation do not lift. `lift13.py` cuts the n = 12 order
again at vertices before it lifts, and a plan that used such cuts loses what they gained: the plan of 522,740,945
letters costs 17,119 at vertices, 1,463 more than as it was, and its lift has 6,747,810,280 letters (120 s, 0.89
GB). One thing is not settled: the lift uses 3,282,720 of the 3,628,800 vertices of n = 12, those that it can
generate as ends of a chain of walk trails. Whether a chain can end at one of the other 346,080 was not examined.

#### Passes at n = 12 that optimise the n = 13 length

`tools/segins_gpu` has two options for this. `--gap3` keeps only the cuts at vertices and writes no trail in two
segments. `--gap3-list FILE` keeps of those only the vertices listed in FILE, and `mkverts.py` writes the list of
the vertices the lift can use:

```sh
python ../arrange/mkverts.py vertices.txt n12t-selection.txt
../segins_gpu n12t-base.txt out.txt --plan-in PLAN12 --gap3-list vertices.txt --time 0
```

The second line brings a plan into the restricted model. A restricted plan is an ordinary plan and rebuilds without
any option. Its cost is its length minus 522,725,289, and its lift has 6,747,793,161 plus that cost. `mkverts.py`
writes 3,282,720 words in 44 s with 1.9 GB (SHA-256 of the list
b7e4e973d4ba67a01898db6f7b039e9ab6744b5c71a637fa0d2484fab7db8fef).

### n = 12 on the transported selection: run systems, the plan built from one, the bound

This piece set is not the one of the n = 12 word. It was the first that beat Pantone's pieces (chained plan
522,745,026, passes down to 522,740,635), and it is the one whose arrangement I studied most closely. The scripts
carry its numbers (7,200 closed trails, the first 6,048 small with 110 cuts each) and work in one directory with
fixed file names.

```sh
gcc -O2 -o hop12 arrange/hop12.c
cd work                                                  # with n12t-base.txt, n12t-base.tsv, cuts12c.bin from above
python ../arrange/sym12.py                               # 168 relabellings -> sym12.pkl
python ../arrange/joins12.py                             # cost-1 joins: at most 3,504 at once (status 2)
python ../arrange/runs12.py 4 6                          # exact run programme: 34,368 and 44,352
python ../arrange/q12.py 4 6 7 8 9 10 11 12              # linear programme on the quotient
python ../arrange/q12b.py 8                              # symmetric run systems -> runs12_8.pkl
python ../arrange/q12b.py 10 --d0                        #                       -> runs12_10_d0.pkl
python ../arrange/q12b.py 12 --d0                        #                       -> runs12_12_d0.pkl
python ../arrange/smallpos.py n12t-base.txt n12t-base.tsv
python ../arrange/build12.py runs12_12_d0.pkl OTHER.plan n12t-runs.plan n12t-base.txt n12t-base.tsv
../recut n12t-base.txt n12t-runs.txt --plan-in n12t-runs.plan --co-skip --time 0
```

The base word has 522,789,969 letters; `cuts12` lists 40,272,960 cuts (0.8 GB; 150 s, 2.75 GB of memory).

#### Run systems

A level E allows joins with W < E inside runs. The value of a system is the sum of E - W over its joins, per orbit
of 168; a larger value is better. `q12.py` gives the linear bound of the value, `q12b.py` the best symmetric system.

| level | cuts | linear bound (`q12.py`) | best symmetric system (`q12b.py`) | runs | joins inside, by W | last round |
|---|---|---|---|---|---|---|
| 8 | all | 148 | 140 | 1,344: 336 single, 672 of 5, 336 of 7 | 2: 3,360; 4: 336; 6: 1,008 | status 2 |
| 10 | vertices only | | 200 | 1,008: 336 each of 5, 6, 7 | the same and 8: 336 | status 2 |
| 10 | all | 214 | 200 | the same system | | status 2 with `--time 60 --prove 2700`, after 15 to 20 minutes of proof (two runs) |
| 12 | vertices only | | 266 | 504: 168 of 10, 336 of 13 | the same and 10: 504 | status 2 |
| 12 | all | 284 | not settled: between 266 and 276 | | | two runs: one stopped at 3 GB of memory, one came to the system of 266 again and stopped at the solver's memory limit of 10 GB with the bound at 276 |

A value with "status 2" in the last round, and no cycle left, is the optimum among symmetric systems: no system that
the 168 relabellings map to itself does better with the cuts allowed. The constraints that exclude cycles hold for
every system, so the earlier rounds need no proof. Level 8 and level 10 are settled with all cuts, and at level 10
the cuts at steps of weight 2 add nothing. Level 12 with all cuts is not settled. The system with cuts at vertices
(266) is a system there too. With all cuts the first round, before any cycle is excluded, ends with optimum 276,
which is an upper bound. A first run then stopped at 3 GB of memory. A second one with 10 GB (`--time 600
--prove 5400`) excluded cycles for nine rounds, came to the same system of 266 without a cycle and stopped in the
proof phase at the solver's memory limit, with the bound still at 276. None of this says the systems are
optimal among all systems, symmetric or not: there the linear bound is what is known, and the gap is 8, 14 and 18
per orbit at the three levels. In the accounting of the bound, where a run end is charged 3 letters at level 12, the
level-12 system costs 13,944 letters and the linear bound is 12,432.

#### From a run system to a plan

`build12.py` orders the runs and puts the other trails between them as blocks taken from OTHER.plan, any plan that
writes every trail once from one cut. With the chained plan of the piece set as OTHER.plan (`chainplan.py`,
522,745,026 letters) and the fixed-order pass afterwards, the level-8 system gives 522,742,771 letters, and the
level-10 and level-12 systems both give 522,741,782. The three words were built and checked. That is 3,244 letters
below the chained plan before any search. The two lengths agree because the level-12 system is the level-10 system
with 504 joins of W = 10 added, and the order of the level-10 runs finds the same joins. On the day I used the best
plan I had as OTHER.plan and got 522,742,649, 522,741,902 and 522,741,478; segment insertion then took the second to
522,740,945. Cut at vertices, the plan of 522,741,782 letters costs 17,406, so its lift to n = 13 has 6,747,810,567
letters.

#### The bound

```sh
python ../arrange/attach12.py                            # a short-walk trail alone between small trails: W-sum >= 4
python ../arrange/prep_hop.py                            # prints the first big cut: 2678592
../hop12 cuts12c.bin 2678592 hop_src.i16 hop_snk.i16 hop_d.i16 hop_d.i16 19 5 > hop12.log
../hop12 cuts12c.bin 2678592 hop_src.i16 hop_snk.i16 hop_d.i16 hop_d.i16 300 5 --pot 7 2 > hop12_pot.log
python ../arrange/bound12.py
```

`hop12` prints the block values B_k = 16, 16, 20, 24, 28, 32, 36, 40, 44, 44, 50, 54, 60, 64, 66, 70, 74, 76 for k =
1 .. 18 (318 s, 1.47 GB), and with `--pot 7 2` the line "FIXED POINT: mu = 7 / 2 per join; every block of k cuts: 2
* B_k >= 7 (k - 1) + 8 + 8". `bound12.py` carries these numbers and those of `q12.py` in its source and prints

    4 cost >= 46,162, cost >= 11,541, length >= 522,736,830

for every level from 7 up (522,736,734 at level 6). It covers the words that write each of the 7,200 trails once,
from one cut of any kind, with overlaps of at most 9 letters. The best word I have on these pieces has 522,740,635
letters, 3,805 above the bound. The bound uses linear programmes solved in floating point for the runs and exact
integer block values; it has one implementation and no referee. It says nothing about the piece set of the n = 12
word, which is another one.

### n = 10: the construction of the word

```sh
python tools/geng.py selections/n10-selection.txt work/n10-base.txt --table work/n10-base.tsv
cd work
python ../arrange/gt.py n10-base.txt gt10m.npz               # traversal tables of the 48 groups; 30 s
python ../arrange/trav10.py n10-base.txt gt10m.npz           # -> c10m_states.pkl
python ../arrange/parts10.py                                 # -> c10m_parts.pkl
python ../arrange/chain10.py tables n10-base.txt gt10m.npz   # -> c10m_tab.npz; 40 minutes, 1.7 GB
python ../arrange/chain10.py solve 2 --verify                # -> c10m_sol_2.pkl; 30 s
python ../arrange/plans10.py c10m_sol_2.pkl n10-base.txt gt10m.npz
python ../arrange/cert10.py n10-base.txt gt10m.npz --a 2 --cap 2
python ../arrange/cert10.py n10-base.txt gt10m.npz --a 1 --cap 2 --multi
```

| | |
|---|---|
| `trav10.py` | 1,008 traversals with W-sum 12, 21 per group; 336 joins between them at W = 8; these form 56 cycles of six groups and nothing else; every group lies on 7 cycles |
| `parts10.py` | 56 partitions of the 48 groups into 8 chains; every chain is in 8 of them |
| `chain10.py tables` | half chains cost 52 in all 336 cases; direct joins between chains 114, 116 or 118; 2,172,452 joins with W <= 5 between big trails; 638 sequences |
| `chain10.py solve 2 --verify` | 254,004 variables; 2 cost 992 (status 2, bound 992); blocks (3, 4, 5, 6), (12, 13, 7), (0, 1, 2), (8, 9, 10, 11) in four of the nine gaps; "PRUNED blocks with reduced cost below the gap: 0" |
| `plans10.py` | chain model 992, exact 2 cost 992, length 4,034,855, 5 groups written as loops; plan `plan10m_p2_4034855.plan`, 355 events |
| SHA-256 of the plan | 6ced8b2589feda32fadc6cfd9701b02d8c50df492acd79cffec74214e33cda02 |
| `cert10.py` | length >= 4,034,848 for words that write every trail once; >= 4,034,842 for words that may write small trails in several segments, the family of this word |

The plan is the plan of the published word. Over all 56 partitions the programme gives 992 for 25 of them, 994 for
17, 996 for 7 and 1,004 for 7, each with status 2.

4,034,855 is the best the chain model can do with the blocks it is offered, and for a given order `tl10.py` is
exact. It is 13 letters above the bound for its family. A word that cuts a chain in two, puts a group between two
other chains, writes a small trail in three segments or a big trail in two is outside the model. A further set of
programs lists every cheap block of big trails by exhaustive search and certifies, partition by partition, that no
word made of 8 whole chains is shorter than 4,034,855 whatever its blocks are. They ran once and are not in this
folder, so that statement cannot be reproduced from here.

### Bounds for Pantone's pieces at n = 10 and n = 11

PANTONE10.txt and PANTONE11.txt are Pantone's words of 4,034,889 and 43,930,680 letters.

```sh
python arrange/gt.py PANTONE10.txt work/gt10p.npz
python arrange/cert10.py PANTONE10.txt work/gt10p.npz --a 2 --cap 2
python arrange/cert10.py PANTONE10.txt work/gt10p.npz --a 1 --cap 2 --multi
python arrange/cert11.py PANTONE11.txt
python arrange/cert11.py PANTONE11.txt --slack 4 --kmax 40
python arrange/t_minplus.py PANTONE10.txt
python arrange/anatomy.py PANTONE10.txt RUMSTD10.txt work/a10
python arrange/check10m.py PANTONE10.txt work/gt10p.npz work/a10_seq.pkl
```

| n | pieces | family of words | bound | shortest word known in the family |
|---|---|---|---|---|
| 10 | Pantone's | every trail once, overlaps of at most 7 | 4,034,860 | |
| 10 | Pantone's | small trails in several segments, big trails once | 4,034,849 | 4,034,873 (rumstd) |
| 10 | the n = 10 pieces | every trail once | 4,034,848 | |
| 10 | the n = 10 pieces | small trails in several segments, big trails once | 4,034,842 | 4,034,855 |
| 11 | Pantone's | every trail once, overlaps of at most 8 | 43,930,476; 43,930,481 with `--slack 4 --kmax 40` | 43,930,614 |

The last column is the best word I know in the family, where I know one that I have checked to be in it. It does not
say that no shorter word exists between the bound and that word.

Status of each: exhaustive integer computation, cross-checked as described in the headers (the min-plus steps
against the direct formula: 0 differences in 2,250 comparisons; the accounting identity on rumstd's word, 4 cost =
2,056 on both sides; the same on my n = 11 word of 43,930,614 letters, 4 cost = 13,240 on both sides), one
implementation, not refereed. The n = 11 word of 43,930,578 letters and the n = 12 and n = 13 words are on other
pieces; no bound here applies to them.

`liftmip.py` belongs to the generation of pieces more than to their arrangement: it shows that a selection with rows
of other lengths cannot be carried one symbol higher at the price of a transport (576 = K Q for the selection of
Pantone's n = 8 word, optimal; 426 against 288 for a test selection with rows of 3 and 4 classes, optimal; at least
577 against 504 for the block of the n = 11 pieces). So each n needs its own search for the blocks.

## Left out

These were written on the way and are not in this folder. Each showed something.

- An earlier lift that could only carry run systems to n = 13. `lift13.py` lifts any plan.
- A greedy chain order for n = 12 from before the integer programme. It failed on the first piece set, and
  `chainplan.py` replaced it.
- A test whether the 11-symbol selection is the transport of a 10-symbol one (`untransport.py`, now in the selection
  folder). It is not: deleting any one letter leaves thousands of loops below with mixed types. So the gain at n =
  12 does not go down to n = 11 by itself, and n = 11 got its own search.
- At n = 12: the classes of cuts under all permutations of the old letters, which led to the group of 168. The
  cheapest join between every two small trails (W = 2 for 10,752 ordered pairs, 4 for 8,064, 6 for 43,008, 8 for
  147,840). The shape of the solution of the linear programme (half-integral on 6 of the 36 orbits of trails). What
  a walk trail costs as a connector between two runs when only cuts at vertices are allowed (a single big trail 5 to
  12 letters, a short-walk trail 4). Run systems of level 14 and above: cycles kept coming back. Level 14 was closed
  with `--maxrounds`, which breaks the cycles that are left and proves nothing, and it was not turned into a plan.
- For the bounds on Pantone's pieces: a linear programme over potentials on the cuts, with optimum 952.0 at n = 10.
  It says that no argument of that kind beats 4,034,835 unless it uses that a big trail is entered and left at one
  cut, which is what the block programme of `cert10.py` does. Column generation on the same programme did not
  converge. Colour refinement of the join structure found no usable symmetry at n = 10. Cheap joins between big
  trails form threads: a path of joins with W <= 2 meets at most 8 big trails, at n = 10 and at n = 11. Searches for
  a shorter n = 11 word in a model of blocks (annealing, beam search, exact placement of the two blocks) found
  nothing below the 272 that the big trails cost in my word of 43,930,614 letters. Every single two-segment change
  of rumstd's n = 9 word loses at least 3 letters.
- At n = 10, the first construction. The small trails of these pieces are Pantone's small trails with the letters
  renamed, so the order of the 48 groups in rumstd's word carries over. With that order, the best cuts and modes
  from `tl10.py` and the big trails placed by a small integer programme, the word had 4,034,860 letters. This is where
  the idea came from: it showed that rumstd's chains of six groups and his loops work on these pieces. The chain
  model replaced it and gave 4,034,855.
- At n = 10, a local search on the order of the 62 objects with the exact evaluator, moving every segment of 1 to 4
  objects to every gap. It found no better order from any of the 25 partitions at 992.
- At n = 10, the programs that close the family of 8 whole chains (the search for all cheap blocks, the table of
  their values, column generation with a dual certificate for each partition, and the check that keeping the middle
  join of a chain costs nothing). See the n = 10 section.

## Tests

    bash test.sh REPRO WORK

runs the scripts on the n = 10 and n = 11 pieces of the reproduction package (REPRO is its folder) and compares what
they print with the numbers above: about 5 minutes and 0.5 GB without a solver. `GUROBI=1` adds the steps that need
the solver, `RECUT=FILE` the chained plan of n = 11 with its SHA-256, `SLOW=1` the 40 minutes of tables at n = 10,
and `BIG=1` the n = 12 chain on the transported selection (20 minutes more, 2.75 GB). The header of `test.sh` lists
what each of them covers. With `GUROBI=1`, `RECUT` and `BIG=1` it ran 61 checks on my machine and none failed, and 4
more with the n = 10 tables in place. It runs nothing at n = 13, and not `cert11.py` or `liftmip.py`; I ran those by
hand, with the results given above.

These are my working scripts with headers and comments added. Each was compared with the script that produced the
numbers: the two are the same program, by syntax tree for the Python files and by the compiler's output for the two
C files, except for the edits below, and the two give the same output and files on the inputs I tried: 53 runs of
both at n = 10 to 13, and 10 runs of the cleaned script alone against files or logs that the original had written.
At n = 13 only scripts that map the word without loading it were run.

The edits: file names that were fixed in the source are arguments now (`smallpos.py`, `build12.py`, `lift13.py`,
`mkverts.py`, `trav10.py`, `chain10.py`, `plans10.py`); the solver's licence banner is no longer printed
(`chainplan.py`, `gen13.py`, `liftmip.py`); three group labels of `plancost.py` say what the groups are; one line of
`cert11.py` no longer names a file that is not here; two functions that nothing calls are gone (`c12.py`,
`q12b.py`); `cmptrails.py` carries the four functions it used to import; `q12b.py` has one new option, `--prove`,
and is unchanged without it.

## Files

Start plans:

- `chainplan.py`: the small trails in chains (integer programme), the units ordered greedily, the other trails as the
  fixed-order pass left them. The start plans of n = 11 and n = 12.
- `plancost.py`: the length of a plan and what every kind of trail costs in it.
- `linkcheck.py`: the check that cost-1 pairs of small trails are the neighbours in an F-orbit.
- `plan13n.py`: chained plan from a selection with rows of any length and the table of its base word; units ordered
  by an assignment. The start plan of n = 13.
- `gen13.py`: selection with full and short rows, transported once and completed: base word, table and chained plan.
- `order13.py`: a better order of the units of the plan of `gen13.py`.
- `verify.py`: independent check of a selection with full and short rows; counts and floor constant.
- `liftmip.py`: the cheapest selection one symbol higher above a given one (rows of other lengths do not transport).
- `cmptrails.py`: do two base words consist of the same closed trails?

n = 12, the piece set of the transported selection (`data/n12t-selection.txt.xz`):

- `cuts12.c`: the file of all cuts of a base word. `c12.py`: reading it, min-plus steps (module).
- `sym12.py`: the 168 relabellings that keep the cuts of the small trails.
- `joins12.py`, `runs12.py`: the cheap joins between small cuts; the run programme solved exactly at levels 4 to 6.
- `q12.py`, `q12b.py`: the run programme on the quotient by the symmetry, as a linear programme and in integers
  (symmetric run systems).
- `smallpos.py`, `build12.py`: a run system turned into a plan.
- `attach12.py`, `prep_hop.py`, `hop12.c`, `bound12.py`: the lower bound for words made of this piece set.
- `lift13.py`: any n = 12 plan lifted to n = 13. `mkverts.py`: the vertices at which the lift can cut, for
  `tools/segins_gpu --gap3-list`.

n = 10 and the bounds for Pantone's pieces:

- `tl10.py`: an order of the groups and big trails of n = 10 valued exactly, with loops; writes plans (module).
- `trav10.py`, `parts10.py`: the 56 chains of six groups, and the 56 partitions of the groups into chains.
- `chain10.py`, `plans10.py`: the integer programme for a partition; its solutions valued exactly and written as
  plans.
- `tm.py`, `countn.py`, `top.py`, `grp.py`, `fdp.py`: the parser of a base word into trails, cuts and joins, its
  top-level objects, the exact programme inside a group, the fixed-order pass on whole trails (modules).
- `gt.py`: the table of traversals of every group.
- `cert10.py`, `cert11.py`: the lower bounds at n = 10 and n = 11.
- `t_minplus.py`, `anatomy.py`, `check10m.py`, `check11.py`: the checks of the bounds on random cuts and on real
  words.

`test.sh` runs the tests. `SHA256SUMS` lists every file of this folder with its hash.
