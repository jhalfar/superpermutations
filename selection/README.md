# Where the selections come from

The reproduction package has four selection files, for n = 10, 11, 12 and 13, and shows how a selection becomes a
word. This directory shows where those files come from. Each of them is built again here from Jay Pantone's
published `construction-input.txt` and a few small data files, and the searches that found the data files are
here too.

    bash test.sh construction-input.txt WORK SELDIR

builds the four selections, compares them with the files of the reproduction package (`SELDIR`) and runs the
checkers. It takes 2 to 3 minutes on one thread and 1.0 GB, with Python 3 and numpy.
`GUROBI=1 bash test.sh ...` also runs the searches that can be repeated, which adds 4 minutes.

The construction, the selection, the completion, the transport and the connector cycles are Pantone's (sections
2 to 6 of his paper). Two things are different here. A row may have any number of the classes of its loop, and
the loops that his construction leaves over get rows of their own.

## Terms

I use the terms of the reproduction package.

| term | meaning |
|---|---|
| K, s, z, n | a selection lives on K letters `0 .. K-1` and a distinguished letter s; completion adds a letter z and gives closed trails on n = K + 2 symbols |
| loop | Pantone's 2-loop: a cyclic order of the K letters. There are (K-1)! loops |
| row | the slice a selection takes from a loop. The row (x, v) starts at the rotation x of the loop and has v of its K cyclic classes. v = K is full, v = K - 2 is short, v = 1 .. K-3 are rows of other lengths |
| loop without a row | a loop from which the selection takes no slice: a left-over loop |
| Q | the sum of K - v over all rows. The closed trails have F3(n) + Q letters in total, F3(n) = n! + (n-1)! + (n-2)! |
| step | the row after (x, v) starts at a state that x and v fix; the step exchanges two cyclically adjacent letters |
| selection | one row or no row in every loop, closed under the step. The rows then form closed walks |
| closed trail | a closed trail of the completion, on n symbols. The closed trail of a loop without a row is a small trail |
| transport | Pantone's rule that turns a selection on K letters into one on K + 1 letters |
| block | the loops above one left-over loop D: all cyclic orders of 7 + r letters whose old letters `0 .. 6` stand in the cyclic order D. The r other letters are the added letters |
| floor | Q + the number of closed trails |

I wrote the scripts in one day, in three places, and their output keeps other words for the same things.
"D loop", "detached loop" and "loop without a slice" are a loop without a row. The "deficit" or "cost" of a row is
K - v. "Tokens" are the added letters. "Paths" and "chains" are runs of small trails that follow each other at one
letter per join.

## The idea

### Pantone's base and its left-over loops

`untransport.py` shows that Pantone's 10-symbol selection is his 8-symbol selection transported twice, apart from
56 rows where a full and a short row are exchanged. The exchanges join the 28 walks of the plain transport into
14. The 8-symbol selection has 720 loops. 672 of them lie on two closed walks with 168 short rows, and 48 are
left over.

At every level the loops above these 48 carry no short row. There are 336, 2,688, 24,192 and 241,920 of them for
n = 10 to 13, one loop in fifteen. Pantone's file writes them as walks of full rows. Such a walk gives as many
closed trails as it has loops, the same number as when its loops have no row at all, so each of these loops costs
one closed trail. The floor of his selection is 193/360 = 7/15 (Q) + 1/15 (left-over loops) + 1/360 (the other
walks), in units of (n-3)!. `acct.py` counts this from his file: Q = 18,816, 2,800 closed trails at n = 11, 357
connector cycles, 43/80.

### The closed sub-problem above a left-over loop

Take one left-over loop D and the r letters added since. A row on a loop above D whose step does not exchange two
old letters leads to another loop above D. So rows on these loops that are closed under the step and never
exchange two old letters can replace "no rows", and nothing outside the block is touched.

The problem is the same above every D and depends only on r: 56 loops for r = 2 (n = 11), 504 for r = 3
(n = 12), 5,040 for r = 4 (n = 13). One solution of it, relabelled into the 48 blocks, gives a selection.

### Rows of other lengths

A row may have any number v of the K classes of its loop. It costs K - v, and completion repairs the K - v
classes it misses with full loops of the new letter z. A closed trail that enters such a row at the inserted
slice with z in gap j ("port" j) leaves it for port pi_v(j) of the next row; pi_v is a fixed permutation of the
K - 1 ports, written out in `gcore.py`. The closed trails of a closed walk are the cycles of the product of its
pi_v. For full and short rows this is Pantone's count gcd(K - 1, f - t).

With full and short rows only, the 56-loop block has nothing cheaper than no rows. With rows of all lengths it
has: 49 against 56.

### Why such rows do not transport

A full or short row has a transport: K rows one level up whose completion has the same ends.
`transport_search.py` and `transport_search2.py` try every candidate for a row that misses three or more classes
and find none (K = 5 to 7 with the same length above, K = 6 to 8 with any lengths above). So a block solution with
such rows works for one n only, and every n needs its own search. A block solution of full and short rows can be
transported.

### Block optima

Q + D is what a block solution costs before its closed trails are counted (D = loops without a row). "No rows"
costs the number of loops. Each line below is about the solutions that are invariant under the relabellings
named, and "optimal" speaks only about those solutions and about Q + D.

| block | rows | invariant under | least Q + D | status | command |
|---|---|---|---|---|---|
| (7, 2), 56 loops | full, short | nothing required | 56 = no rows | optimal | `gblock.py 7 2 --vset 9,7` |
| (7, 2) | all lengths | nothing required | 49 | optimal, 336 solutions | `block_grb.py 7 2 --sym none --slack 0`; `gblock.py 7 2 --gap 0` |
| (7, 2) | all lengths | rotation of the old letters | 56 | optimal | `block_grb.py 7 2 --sym old --slack 0` |
| (7, 3), 504 loops | full, short | rotation | 308 | optimal, 6 solutions | `block_grb.py 7 3 --sym old --maxd 2 --slack 0`; `gsegip.py 7 3 --dmax 2` |
| (7, 3) | full, short | nothing required | 308 | best found, bound 270 | not here |
| (7, 3) | all lengths | rotation | 301 | optimal, 12 solutions | `block_grb.py 7 3 --sym old --slack 0`; `gsegip.py 7 3 --dmax 9` |
| (7, 3) | all lengths | rotation and shift of the added letters | 336 | optimal | `block_grb.py 7 3 --sym old,tok --slack 0` |
| (7, 3) | all lengths | shift of the added letters | 300 | best found, bound 258 | `block_grb.py 7 3 --sym tok --slack 0 --time 240` |
| (7, 3) | all lengths | nothing required | 300 | best found, bound 224 | not here |
| (7, 4), 5,040 loops | all lengths | rotation | 2,849 | best found, bound 1,376.2 | `gsegip.py 7 4` |

I ran the six "optimal" lines again with the scripts here. The "best found" lines for the (7, 3) block and their
bounds are quoted from the logs of the first runs. The bound 1,376.2 is a linear relaxation. It holds for every
solution of the (7, 4) block, invariant or not, and it is weak: the same relaxation gives 182 for the (7, 3)
block, where the optimum under rotation is 301.

The blocks in use are not the solutions with the least Q + D. A loop without a row is cheap in the floor, where
it counts as one closed trail, and costly in a word, because small trails have to be joined in chains. So the
searches also count chains, and the later ones count walks.

| data file | used for | Q | D | closed trails of its walks | found by | status |
|---|---|---|---|---|---|---|
| `block_7_2_n11.txt` | n = 11 | 38 | 14 in 3 chains | 2 | `gblock.py`, objective Q + D + 2 x chains | optimal for that objective (58); the command writes the file again |
| `connect_n11_a.json`, `connect_n11_b.json` | n = 11, 10 of the 48 blocks | 86 more in all | unchanged | 80 fewer in all | an earlier state of the search in `gregion.py` | best found; checked, not found again |
| `block_7_3_c.txt` | n = 13 outside the blocks; the asymptotic coefficient | 182 | 126 | 3 | an earlier script | one of the 6 optimal full / short solutions invariant under rotation |
| `block_7_3_n12.txt` | n = 12 | 266 | 49 | 6 | `block_grb.py --links --no6 --P 2.9` | best found (objective 396, bound 338); the run is not repeatable |
| `block_7_4_n13.txt` | n = 13 | 2,611 | 266 in 84 chains | 20 | `gsegip.py --lns --zprice`, the last of a chain of runs | best found; the last two stages write `step2` and this file again |
| `block_7_4_step2.txt`, `block_7_4_step1.txt` | the two steps before it | 2,611; 2,443 | 266; 406 | 24; 26 | the same chain | best found; `step1` has the lowest floor met (2,875) |

A connection is a block solved again together with the loops around it, so that its rows lie on one of the 14
big walks of Pantone's selection. That walk then gives 2 closed trails instead of 8.

### Floors of the selections

`check12.py` counted these. `check2.py` and the scripts that build the selections give the same numbers. The
lines "in use" are the four selections of the reproduction package.

| n | selection | Q | loops without a row | closed trails | floor | floor / (n-3)! |
|---|---|---|---|---|---|---|
| 10 | Pantone's 8-symbol selection transported once | 2,352 | 336 | 364 | 2,716 | 97/180 |
| 10 | in use: two walks instead of four | 2,352 | 336 | 350 | 2,702 | 193/360 |
| 11 | Pantone's 10-symbol selection | 18,816 | 2,688 (as walks of full rows) | 2,800 | 21,616 | 193/360 |
| 11 | the block solution in all 48 blocks | 20,640 | 672 | 880 | 21,520 | |
| 11 | in use: 10 of the blocks connected to big walks | 20,726 | 672 | 800 | 21,526 | |
| 12 | Pantone's selection transported | 169,344 | 24,192 | 25,200 | 194,544 | 193/360 |
| 12 | the transportable selection (`block_7_3_c.txt`) | 178,080 | 6,048 | 7,200 | 185,280 | 193/378 |
| 12 | in use | 182,112 | 2,352 | 3,648 | 185,760 | 43/84, this n only |
| 13 | the transportable selection transported | 1,780,800 | 60,480 | 72,000 | 1,852,800 | 193/378 |
| 13 | in use | 1,818,768 | 12,768 | 23,808 | 1,842,576 | 38387/75600, this n only |

A word pays more than the floor. Every closed trail has to be cut and joined, and the tools that arrange the
trails decide what that costs. A selection with fewer, longer closed trails pays more in Q and less there: at
n = 11 and n = 12 the selection in use has a higher floor than the one above it in the table.

### The asymptotic coefficient

The transportable selection has the floor 193/378 = 0.510582 at every n >= 12, because a transport multiplies Q,
the loops without a row and the closed trails of the walks by the same number. With explicit connector cycles it
gives

    S(n) <= F3(n) + (1771/3456 + o(1)) (n-3)!,      1771/3456 = 53/108 + 7875/9! = 0.512442

against Pantone's 43/80 = 0.5375. This is a consequence of sections 4 and 5 of his paper applied to this
selection. I checked the hypotheses by computation and did not prove the argument again.

What I computed: 203 cycles that contain z meet all 1,152 closed trails of the walks at n = 12 (`conn_big.py`,
`data/zcycles_n12.txt`, checked again by `cyccheck.c`). One level up each of the 6,048 loops without a row gets
one cycle without z and each of the 203 cycles becomes 9, which makes 7,875. I checked the rule that carries
cycles one level up literally from 9 to 10 and from 10 to 11 symbols (`conn.py --lift`). I did not build the
cycles at n = 13. 203 is the best found; the bound is 201.

## What is proved, what is computed, what is best found

Three things rest on short arguments and not on computation, and nobody else has checked the arguments. When
every loop has at most one row, the closed trails are forced. Rows inside a block that never exchange two old
letters touch nothing outside it. A transport keeps the floor per (n-3)! of a selection of full and short rows.

I computed the following and checked each a second way.

- The port rule, against the literal endpoint graph of all slices: on 120 random selections (`gcore.py --test`),
  on every block solution (`lit_block.py`), and on the whole selections of n = 10 and 11
  (`check2.py --complete`). For n = 12 and 13 the block is completed literally, the rows outside the blocks are
  full and short, and the generator of the reproduction package completes the selection once more with code of
  its own.
- That the completion covers every cyclic class once: `gcover.py` for n = 10 and 11; for n = 12 and 13 the
  generator and the checkers of the words.
- The numbers in the table of floors: `check12.py`, which shares no code with the scripts that build.
- The optima 308 and 301 of the (7, 3) block under rotation: two programs with different models
  (`block_grb.py`, `gsegip.py`). The optimum 49 of the (7, 2) block: `block_grb.py` and `gblock.py`.
- The step, the port rule and the completion were written three times that day, independently. I keep one
  version, `gcore.py`: the written rule that the generator of the reproduction package follows was taken from
  it, and it carries the test against the literal graph. The other two gave the same numbers on every block and
  selection here. The three checkers each keep a copy of their own on purpose.

Two things I computed once, with no second check: that rows of other lengths have no transport (K up to 8, for
the two kinds of rule the scripts describe), and that Pantone's 10-symbol selection is a double transport with 56
exchanged rows.

The blocks of n = 12 and n = 13, the connections of n = 11, the two walks of n = 10 and the 203 cycles are the
best found. I do not know whether any of them is optimal, or whether one walk is possible for n = 10.

## Commands

`IN` is Pantone's `construction-input.txt`. Times are for one thread. (G) marks a script that needs Gurobi with
a full licence; academic licences are free, and the size-limited licence that comes with the Python package is
too small. Building and checking a selection needs no solver.

Pantone's 8-symbol selection, used for n = 10, 12 and 13:

    python untransport.py IN --out sel9_pantone.txt            # his 10-symbol selection with the last letter deleted
    python untransport.py sel9_pantone.txt --out base8.txt     # 8 symbols, 48 loops without a row
    python acct.py IN --full                                   # the accounting of his selection: 38 s, 0.7 GB

n = 10:

    python lns.py base8.txt n10.txt --transport 1 --order walk --free 300 --rounds 3 --time 30 --pool 40 --seed 1 --threads 2    # (G) 3 s
    python check2.py n10.txt --complete
    python gcover.py n10.txt

The search is random. With these arguments and Gurobi 13.0 it writes the selection of the reproduction package
again. Without the solver, take `n10-selection.txt` from there.

n = 11:

    python gblock.py 7 2 --cC 2 --pool 3000 --gap 1.01 --time 200 --threads 1 --out block.txt    # (G) 20 s; = data/block_7_2_n11.txt
    python lit_block.py data/block_7_2_n11.txt
    python gapply.py IN data/block_7_2_n11.txt n11_plain.txt --literal
    python gregion.py multi IN data/block_7_2_n11.txt n11.txt data/connect_n11_a.json data/connect_n11_b.json --walks 0:0
    python gcover.py n11.txt                                   # 10 s, 0.5 GB
    python check2.py n11.txt --complete                        # 49 s, 0.85 GB
    python check12.py n11.txt

n = 12:

    python lit_block.py data/block_7_3_n12.txt
    python hybrid3.py base8.txt n10.txt 3 data/block_7_3_n12.txt n12.txt    # 6 s, 0.3 GB
    python check2.py n12.txt                                   # 12 s, 0.3 GB
    python check12.py n12.txt

n = 13:

    python hybrid3.py base8.txt n10.txt 3 data/block_7_3_c.txt sel11c.txt --fsd    # the transportable selection
    python lit_block.py data/block_7_4_n13.txt
    python build12.py sel11c.txt base8.txt data/block_7_4_n13.txt n13.txt          # 9 s; the file has 53 MB
    python check12.py n13.txt                                  # 14 s, 1.0 GB

The searches behind the data files, all (G):

    python block_grb.py 7 3 --sym old --maxd 2 --slack 0 --out c
    python block_grb.py 7 3 --sym old --links --no6 --P 2.9 --slack 10 --pool 400 --time 300 --threads 3 --out x
    python gsegip.py 7 4 --dmax 6 --P 2.6 --wt 3.5 --chains --lns 2000 --sub 50 --frac 0.3 --time 100 --threads 1 --seed 101 --start data/block_7_4_step1.txt --out s2.txt
    python gsegip.py 7 4 --dmax 6 --P 4.5 --wt 1 --wu 4.5 --zprice --chains --lns 2000 --sub 60 --frac 0.35 --time 100 --threads 1 --seed 91 --start data/block_7_4_step2.txt --out b4.txt
    python gsegip.py 7 4 --dmax 10 --lp
    python gregion.py multi IN data/block_7_2_n11.txt unused.txt --fullring --walks 0:1 --json new.json --time 240 --gap 8 --pool 60 --poolgap 2

The first lists the 6 optimal full / short solutions of the (7, 3) block (1 s). The second found
`block_7_3_n12.txt`; it ends by its time limit and does not give the same file twice. The third and the fourth
write `block_7_4_step2.txt` and `block_7_4_n13.txt` again, 100 s and 0.5 GB each. The round that finds the second
of these ends by a time limit, so on another machine it may come out differently. The fifth is the bound 1,376.2
(7 s, 0.5 GB). The last is the search for a connection as it stands. It does not find the two connection files
again; the header of `gregion.py` says what it finds.

Rows of other lengths have no transport:

    python transport_search.py 7                               # 47 s
    python transport_search2.py 8

Connector cycles:

    python conn.py base8.txt --lift data/cycles_n9.txt         # the rule for one level up, 9 to 10 symbols
    python conn.py n10.txt --lift data/cycles_n10.txt          # 10 to 11 symbols
    gcc -O2 -o cyccheck cyccheck.c
    ./cyccheck sel11c.txt data/zcycles_n12.txt                 # the 203 cycles meet all 1,152 closed trails of the walks
    python conn_big.py sel11c.txt cycles.txt --time 240        # (G) finds such cycles: 4.5 minutes, 2.1 GB

## What was tried and is not here

I left out the scripts that led nowhere or were replaced. For the whole problem they showed: selections invariant
under a group, 11 groups on 9 to 12 symbols, gave nothing below 0.61 per loop; the selections on 8 symbols
invariant under PSL(2,7) have the optimum 384, Pantone's, also with rows of all lengths; exchanges of a full and a
short row do not join Pantone's 14 walks further. Around his 10-symbol selection outside the blocks: in 40 regions
of 400 loops a change that uses a row of another length costs at least 8 more in Q + D. For n = 10: the block of
7 loops has nothing cheaper than no rows, with rows of all lengths. For n = 11: three other block solutions with
a lower Q + D (49, 50 and 51) and more loops without a row, and a selection with 12 connected blocks, gave longer
or equal words; a price of a block from the real costs of its joins has the block in use as its optimum. For
n = 12: four other block solutions, three of full and short rows and one with rows of other lengths, gave longer
words or were not run; a model that priced every walk inside the programme did worse when the symmetry group was
small; a model without symmetry, started from the block in use, found nothing. For n = 13: with full and short
rows only the (7, 4) block reaches the floor 3,046 against 3,110 for the transport, but its small trails do not
chain; a search without the rotation symmetry gained 3.5 once in eight minutes and then nothing; one more block
with fewer chains and a higher floor was found and not used. Replaced by what is here: an earlier checker, three
generators (the reproduction package has the generator), the other libraries for the step and the port rule, and
the solvers these scripts grew out of. Rows of other lengths were first tried for n = 7 and 8: the best word of
that family for n = 7 has 5,907 letters (the record is 5,905), and for n = 8 nothing below Pantone's Q = 96 was
found.

## Files

| file | what it does | needs |
|---|---|---|
| `gcore.py` | the library: step, port rule, closed trails, literal completion, transport, file format | |
| `acct.py` | the accounting of Pantone's input | |
| `untransport.py` | is a selection a transport? writes the selection on one letter less | |
| `lns.py` | neighbourhood search on a selection of full and short rows (n = 10) | Gurobi |
| `gblock.py` | the (7, 2) block as an integer programme (n = 11) | Gurobi |
| `gapply.py` | a block solution above every left-over loop of Pantone's selection | |
| `gregion.py` | a block connected to a big walk: assembly of the n = 11 selection, and the search | Gurobi for the search |
| `block_grb.py` | a block with a required symmetry, with all solutions near the optimum (n = 12) | Gurobi |
| `hybrid3.py` | a transported selection outside the blocks, a block solution inside (11 symbols) | |
| `gsegip.py`, `lns_part.py`, `quot.py` | the (7, 4) block: programme over segments and neighbourhood search (n = 13) | Gurobi |
| `build12.py` | the 12-symbol selection, written line by line | |
| `lit_block.py` | literal completion of a block solution | |
| `check2.py` | checker of a selection, from the letters of the slices | |
| `check12.py` | checker of a selection in arrays, up to 12 symbols | numpy |
| `gcover.py` | every cyclic class in exactly one slice of the completion (n = 10, 11) | numpy |
| `transport_search.py`, `transport_search2.py` | no transport for rows of other lengths | |
| `conn.py`, `conn_big.py` | connector cycles for the completion of a selection | Gurobi, numpy |
| `cyccheck.c` | checks connector cycles with a completion of its own | a C compiler |
| `test.sh` | the builds and checks in one run | bash |
| `data/` | block solutions, connections, cycles | |
