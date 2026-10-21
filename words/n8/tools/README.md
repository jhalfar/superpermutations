# Tools for n = 8

One program, [`n8.py`](n8.py), with commands. It needs Python 3 with numpy and scipy, and nothing else: the integer
programmes run on HiGHS, which comes with scipy. The program uses Gurobi or OR-Tools when they are installed and
you ask for them.
Run the commands from the top of the repository.

```sh
# the 46,174 word from its selection: about 3 seconds
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt

# the best word of any selection, with a proven lower bound
python3 words/n8/tools/n8.py price SELECTION.txt

# the search that found the selection: walk types, packing, then parallel tempering
python3 words/n8/tools/n8.py search --time 1800 --seed 1
```

`python3 words/n8/tools/n8.py COMMAND --help` lists the options of a command. `bash words/n8/tools/test.sh` runs
the tests (about 2 minutes).

## The commands

| command | what it does |
|---|---|
| `check WORD` | every permutation of `01234567` occurs, and no single letter can be deleted |
| `price SELECTION` | the best word of the selection in a model (below), its J and a proven lower bound on J |
| `rebuild SELECTION -o WORD` | the same, writes the word and checks it; with `--order ORDER` it writes the word of a given slice order and uses no solver |
| `extract WORD -o SELECTION` | the selection of a word of this framework, and with `--order-out` its slice order |
| `walks` | the types of closed walks with few letters per loop |
| `pack` | a selection made of disjoint closed walks: a set partition, or with `--copies` every packing by copies of one type |
| `search` | `walks`, then `pack`, then parallel tempering over selections, every candidate priced by `price` |

Every command that solves an integer programme takes `--solver highs` (the default), `gurobi`, `scip` or `cbc`.
The output names the solver and the bound.

## The model

The words are built like the completion step of Jay Pantone's construction, with the letters 6 and 7 fixed. The
120 cyclic orders of `012345` are the loops. A selection gives each loop a row of length v (v from 1 to 6), which
costs 6 - v letters, or no row. Q is the cost of all rows. The row of one loop leads to a state of another, so the
rows form closed walks. Each row, and each loop without a row, is written as a few short words, the slices: a loop
gives 6 + (6 - v) slices, 720 + Q in all. Two slices overlap by at most 5 letters, and by exactly 5 only along the
closed trails, in which every slice has one successor and one predecessor. A closed walk is read as one or more
closed trails, and a loop without a row is a closed trail of its own.

A word writes all slices. Each slice is joined to the one before it with an overlap of ov letters, which costs
5 - ov. With J the cost of all joins, the word has

    46,085 + Q + J

letters. Inside a closed trail the joins are free. Between two trails they cost 1 to 5, so J is at least the number
of trails minus 1. The program knows two models for the order of the slices.

* `--model trails` (the default). Every closed trail is written in one run, opened at one place, and the runs are
  joined with the largest overlap (up to 7 letters). With `--min-weight 3` (the default) a trail is opened
  between two of its slices. With `--min-weight 2` it may also be opened inside a slice, at a step of weight 2,
  which makes the run one letter longer; with `--min-weight 1` at any permutation window. The programme chooses
  one opening for each trail, and for the order goes through hubs: a run that ends with the letters w goes to the
  hub of w, and from there to a run that starts with w.
* `--model slices`. The slices in any order, so a trail may also be split into several runs. This is an asymmetric
  travelling salesman problem with one variable for each pair of slices that overlap.

In both models the parts of a solution that are not joined to the start of the word are cut away in a loop: solve,
add a cut for each such part, solve again. Every programme of the loop leaves out some cuts, so its optimum is a
lower bound on J. When J equals the bound, no word of that model is shorter. That is all the program proves: a word
of another form can be shorter, and for this selection one is ([below](#trails-opened-inside-a-slice)). The two
models overlap: a word of whole slices in which every trail is one run lies in both.

`--min-overlap K` allows only joins of overlap K or more.

## Rebuilding the 46,174 word

```sh
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt -o w46174.txt
```

prints Q 64, 16 closed trails, `J 25, lower bound on J 25: optimal in this model`, length 46,174, and the checks.
The solver chooses one of many words of the same length, so the word is usually not the published one, and its
SHA-256 depends on the solver and its version. With HiGHS from scipy 1.18.1 it was the same in every run,
`820f7096791c7064f7c80870a394d42a9a5181c4e6a90116e598af2ee9f57cc9`; with Gurobi 14 it was another word.
[`../order-46174.txt`](../order-46174.txt) is the slice order of the published word, and

```sh
python3 words/n8/tools/n8.py rebuild words/n8/selection-46174.txt --order words/n8/order-46174.txt -o w.txt
```

writes it letter for letter (SHA-256 `50d9bb150ffcf28482e4663f9d8a5ff449fae2de2ef09643eefd922fe1b224aa` without the
line feed). `extract` gives both files back from the word:

```sh
xz -dk words/superpermutation-8-46174.txt.xz
python3 words/n8/tools/n8.py extract words/superpermutation-8-46174.txt -o sel.txt --order-out order.txt \
    --compare words/n8/selection-46174.txt
```

## Why the selection was missed

My earlier program for the best word of a selection allowed only joins of overlap 3 or more. The same selection,
priced that way:

```sh
python3 words/n8/tools/n8.py price words/n8/selection-46174.txt --model slices --min-overlap 3
```

gives J 33 with lower bound 33, so 46,182 letters. With every overlap allowed, `--model slices` gives J 25, 46,174
letters, and the word it writes has three joins of overlap 2, four of overlap 3 and eight of overlap 4 between its
16 trails. In the model `trails` the programme with overlap 3 or more has no solution: if every trail is one run,
opened between two slices, the 16 runs cannot all be joined with overlap 3 or more.

## Trails opened inside a slice

With `--min-weight 3`, the default, a trail is opened only between two of its slices. The J that `price` proves is
then the least J under that rule. For the selection itself it is only an upper bound: opening a trail inside a
slice, at a step of weight 2, costs one letter more but can make the joins cheaper. Theo H. found a word of 46,173
letters on this selection with [`tools/trailsearch.c`](../../../tools/trailsearch.c); his word opens three of the
16 trails at a step of weight 2 ([`../README.md`](../README.md)). The program finds a word of 46,173 letters again
in about 3 seconds from the base word of the selection. Which word it is depends on the build: with two compilers
I got words with three and with two trails opened inside a slice.

```sh
python3 reproduce/tools/geng.py words/n8/selection-46174.txt base8.txt --table base8.tsv
cc -O2 -mpopcnt -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch base8.txt w46173.txt --iters 30000 --seed 1 --kmax 12 --T0 0.7 --threads 1
python3 words/n8/tools/n8.py check w46173.txt
```

`price --min-weight 2` makes the openings variables of the programme: 5,040 openings instead of 784 for this
selection. Both words above write every trail in one run and open it at a step of weight 3 or 2 inside a slice or
between two (I checked their plans), so they are words of this model. With Gurobi the loop reached the lower bound J
24 after about 15 minutes and kept it until its time limit of 50 minutes, without writing a word that short itself.
Together: if every trail is written in one run and opened at a step of weight 2 or 3, no word of this selection is
shorter than 46,173. I did not run this programme with HiGHS.

## Pricing another selection

A selection file has one line per loop: a state (an ordering of `012345` at which the row starts) and v, with 0
for no row. `#` starts a comment. The file must list all 120 loops and the rows must form closed walks; the program
says what is wrong otherwise. `price` prints J, the bound and the length; `-o` writes the word.

William Echols's word of 46,178 letters is in his repository
[github.com/WilliamEchols/superpermutations](https://github.com/WilliamEchols/superpermutations). The copy I used
has no line feed and the SHA-256 `5b69631fa8c20e056c3a49abbd6e8e4ab60abc25bc0541becf689bdf88b0ac8d`. It is not
copied here. Saved as `46178.txt`:

```sh
python3 words/n8/tools/n8.py extract 46178.txt -o echols.txt
python3 words/n8/tools/n8.py price echols.txt
```

`extract` reads it forwards with 6 and 7 as the fixed letters, finds Q 92, no loop without a row, 2 closed walks
and 2 closed trails, and a word of whole slices with J 1. `price` gives J 1 with lower bound 1: 46,178.

`extract` tries both directions of reading and every choice of the two fixed letters, renames the other six to
`0..5` in their order, and takes for each loop the option whose slices all occur in the word. A word that opens a
trail inside a slice has a cut slice; `extract` then still finds the selection and says that the word is not made
of whole slices (one word in [`../ties/`](../ties/) is of this kind).

## The search

`search` runs the steps that found the selection.

1. `walks`: closed walks up to renaming the letters `0..5`. A walk is a cyclic sequence of row lengths; the search
   goes depth first from `012345` and prunes with the fewest rows and the least Q needed to get back. With at most
   32 loops and Q / L at most 0.625 it finds 6 types in about 30 seconds. With at most 44 loops and Q at most 27
   (also Q / L at most 0.625) it finds 9 types in 76 minutes; they are in [`walk-types.txt`](walk-types.txt). The
   two lowest ratios (Q + T) / L among them are 9/16 for the 16-walk `4666` x 4 and 17/27 for the 27-walk
   `266646664666466466646664666`; each of the two is a single closed trail. `search` uses 30 loops.
2. `pack`: a set partition over every placement of every type (720 renamings each), cost Q + T per walk and 100
   per loop without a row, so that it first covers as many loops as it can. HiGHS finds and proves the best one in
   about 25 seconds: four 27-walks, 108 loops, 12 loops without a row. `pack --copies TYPE 4` lists every packing by
   four copies of one type: 360 for the 27-walk, 2 up to renaming, one the reverse of the other. Both are priced at
   46,174.
3. Parallel tempering. A move takes a region of 12 to 50 loops (a ball in the graph of rows), keeps every other loop
   as it is, and solves the region again with an integer programme that covers its loops by closed walks at cost
   Q + T (the trails are counted by roots on the 5 strands of a walk, with Pantone's port rule), with random noise
   on the costs and the condition that the region changes. `price` (model `trails`) prices the new selection,
   and the Metropolis rule accepts it or not. Neighbouring chains swap selections now and then. Every word
   shorter than `--save-below` (default 46,178) is checked and written to the output directory with its selection.

`search --start SELECTION ...` skips steps 1 and 2. The packing itself gives 46,174 letters, so the search reaches
it within a minute; the tempering then looks for shorter words near it. My run of the command at the top of this page
(`--time 1800 --seed 1`, HiGHS) made 173 moves in each of its 3 chains and 227 pricings. It found no word shorter
than 46,174 and wrote two words of 46,177.

## Solvers

[`n8lib/milp.py`](n8lib/milp.py) is the only place that talks to a solver. A programme is a list of variables
(cost, bounds, integer or not) and rows (lo <= sum of coefficients times variables <= hi). A backend is one
function `backend(problem, time_limit, threads, verbose)` that returns the status, the values, the objective and the
best lower bound; it is entered in the table `BACKENDS`. There are four: `highs` (scipy.optimize.milp), `gurobi`
(gurobipy), and `scip` and `cbc` (OR-Tools). The cut loops do not need callbacks, so any solver of mixed integer
programmes fits. Every backend is asked to solve to a gap of zero.

## Run times

One thread, Ryzen 9 5950X under Windows, Python 3.14, scipy 1.18.1, Gurobi 14.0, OR-Tools 9.15, while other jobs
ran on the machine.

| command | HiGHS | Gurobi |
|---|---|---|
| `check` the 46,174 word | under 1 s | |
| `extract` the 46,174 word | under 1 s | |
| `rebuild` (model `trails`) | 3 s | 1 s |
| `price --model slices` | 4 min | 15 s |
| `price --model slices --min-overlap 3` | 28 min | 2 min |
| `walks` (32 loops) | 30 s | |
| `walks --max-loops 44 --max-q 27` | 76 min | |
| `pack` | 25 s | |
| `pack --copies` (27-walk, 4) | 35 s | |
| `test.sh` | 2 min | 4 min |

`test.sh` also passes with `SOLVER=scip` (7 minutes). With `SOLVER=cbc` every test passes but the packing
(test 8): CBC did not finish that programme in 40 minutes, and I stopped it. Memory: `rebuild` needs 0.15 GB with
`OPENBLAS_NUM_THREADS=1`, as `test.sh` sets it. Without it numpy reserves memory for every thread of the machine,
here 1.6 GB, and `price --model slices` reached 2.4 GB.

## Files

| file | content |
|---|---|
| `n8.py` | the commands |
| `n8lib/model.py` | loops, rows, slices, closed trails, walks, reading and writing selections, the word checks |
| `n8lib/openings.py` | the model `trails` |
| `n8lib/price.py` | the model `slices`, and the order files |
| `n8lib/extract.py` | selection and order of a word |
| `n8lib/walks.py` | closed walk types and their placements |
| `n8lib/pack.py` | packings |
| `n8lib/search.py` | the region programme and the parallel tempering |
| `n8lib/milp.py` | the solver adapter |
| `walk-types.txt` | the output of `walks --max-loops 44 --max-q 27`, the default input of `pack` |
| `test.sh` | the tests |
