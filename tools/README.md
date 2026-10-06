# Tools

These are the programs that shorten a word once its closed trails are given. They take a base word, which is any
word of Jay Pantone's construction that holds every closed trail once: one of his words, or a base word that
`reproduce/tools/geng.py` writes from another selection. They split it into its closed trails and join the trails
again. The construction is Pantone's. Cuts between two 2-cycles come from rumstd's n = 10 word, and cuts inside a
1-cycle from Theo H.'s n = 11 word. Where the closed trails come from and how a first plan is made is in
[`selection/`](../selection/README.md) and [`arrange/`](../arrange/README.md).

To rebuild or check a published word you need `trailsearch.c`, `delcheck.c` and a C compiler. No solver is involved.

## How a word is described

A word is a sequence of pieces. Each piece is one closed trail, cut open at one place, and consecutive pieces are
joined with the largest overlap of their ends. A plan is a text file that lists the pieces in order:

    TRAILSEARCH-PLAN n length-of-the-base-word number-of-lines
    P k                 piece k of the base word as it is
    O t start g g1      trail t cut at offset start; g is the weight of the step that is cut
    S t start len       len letters of trail t from offset start (a trail written in two or more parts)

A plan belongs to the word it was made from, the base word. Every tool reads `BASE.txt` and a plan, and writes
`OUT.txt` and `OUT.txt.plan`.

The cost of a cut is 3 minus the weight of the step. A cut at a step of weight 3 is free. A cut between two 2-cycles
(weight 2) costs one letter. A cut inside a 1-cycle (weight 1) costs two letters, and only `recut_wide.c` and
`word2plan.c` use it.

The code and the program output use older words of mine for the same things. An "opening" or "option" is a cut. Its
"gap" is the weight of the step. An "event" is one piece as it is written. A "skip" is a cut that drops one of the
two occurrences of a permutation that the trails hold twice. "Cluster optimisation" is the fixed-order pass.

## The files

| file | what it does | the option that matters | binary name in my logs |
|---|---|---|---|
| `trailsearch.c` | local search over trails and cuts; rebuilds a word from a plan | `--plan-in PLAN --time 0` rebuilds | `trailsearch_merged` |
| `recut.c` | fixed-order pass: the best cut of every trail at once for the order as it is | `--co-skip --time 0` | `co` |
| `relocate.c` | relocation: neighbouring trails moved to another place, the trails around re-cut | `--dpa` | `as3` |
| `segins.c` | segment insertion: the sequence cut at 3 to 6 joins and put together in another order | `--or3 C --or3-slack S` | `tsw2` |
| `segins_gpu.c`, `segins_kern.cu` | segment insertion for long words: tables kept between rounds, candidates judged on an NVIDIA card, moves of equal length, bounded memory, cuts at vertices only | `--or3 C --or3-gpu`, `--or3-eq E`, `--gap3-list FILE` | `tsw5` with the parts `g3`, `e`, `h` |
| `segins_ils.c` | local kicks: a small move, a local repair by segment insertion, keep if shorter or equal | `--ils SEC` | `tsils` |
| `loopscan.c` | loop moves: a block of pieces hung into another trail, which is then written in two parts | `--greedy` | `loopscan2` |
| `trailsearch_gpu.c`, `kern.cu` | the search on an NVIDIA card, with block moves and the fixed-order pass inside | `--gpu --ptx kern.ptx` | `tsg4p` |
| `recut_wide.c`, `kern_wide.cu` | fixed-order pass with cuts inside a 1-cycle (experimental) | `--wide --co-skip --time 0` | `seg` |
| `word2plan.c` | writes any word of the same trails as a plan on a base word | | `word2plan` |
| `delcheck.c` | checks a word: every permutation present, no letter that can be deleted | | `delcheck` |
| `letter.c` | moves on letters, independent of the trails; gives certificates, finds nothing | `del`, `win` | `letter` |
| `polish.sh` | cycles `relocate`, `segins` and `loopscan` until nothing gains | | `polish2.sh` |
| `rounds.sh` | rounds of search, each followed by the passes | | `alt7.sh` |
| `kick.sh` | a short hot search, then `polish.sh` on where it ended | | `kick3.sh` |
| `xzpar.sh` | makes the `.xz` archives of `words/` on several threads | | |
| `mkptx.sh` | compiles the CUDA kernels to PTX | | |
| `test.sh` | builds everything and runs the tests below | | |
| `verify.c`, `verify_par.c`, `pieces.c`, `assemble.c`, `runjoin.py`, `connector_splice.py` | the earlier tools, unchanged except for the header of `runjoin.py` | | |

`segins.c` contains all of `recut.c`: `segins BASE OUT --plan-in PLAN --co-skip --time 0` is the same pass. I keep
`recut.c` because it is the shortest file that shows the dynamic programme. In the same way `segins_gpu.c` contains
a later state of `segins.c`, and without its new options it wrote the same plans wherever I compared the two. I
keep `segins.c` because it made the words on Pantone's closed trails and is half as long.

## What these files are

Eight of the C files (`trailsearch`, `recut`, `relocate`, `segins`, `segins_gpu`, `segins_ils`, `trailsearch_gpu`,
`recut_wide`) are copies of one program with parts added to each. Each was written in a night against the search
program as it was then, so the loader, the model and the search exist in three generations: the first published
`trailsearch.c` inside `recut.c` and the three `segins` files, the present one inside `relocate.c`, and the present
one with card code inside `trailsearch_gpu.c` and `recut_wide.c`. `loopscan.c` and `word2plan.c` carry their own
copy of the loader. Together the eight files have about 1.5 MB of source, of which roughly half is distinct.

For a reader this means: the header of each file says what its own part is, and lines of equal signs mark where
that part begins and ends. The rest can be skipped. For anyone who changes the loader it means the same change in up
to ten files. I plan to merge them into one program with the passes behind options. Until then the copies are
what produced the words, and I would rather publish what ran than a merge that has not.

## Building

    gcc -O2 -mpopcnt -fopenmp -o NAME NAME.c -lm

for every C file. `word2plan.c` needs neither `-fopenmp` nor `-lm`. On Linux `trailsearch_gpu.c`, `recut_wide.c` and
`segins_gpu.c` also need `-ldl`. I build with MinGW gcc 13.2 on Windows. gcc 13.3 on Linux gives the same words.
`-mpopcnt` halves the loading time on x86; leave it out on other processors. Profile-guided optimisation makes the
search about 25 % faster. `-O3` and `-march=native` change nothing I could measure. The code uses GNU extensions,
so MSVC does not compile it. gcc 13 with `-Wall -Wextra` and clang 18 with `-Wall` compile all twelve files without
a warning.

The sources are formatted with clang-format 23 and the `.clang-format` file in the root of the repository:
`clang-format -i tools/NAME.c`, and for the three kernels `clang-format --assume-filename=kern.cpp`.

The kernels are compiled once to PTX with the CUDA toolkit:

    bash tools/mkptx.sh

It runs `nvcc -arch=sm_120 -ptx` on `kern.cu` and on `segins_kern.cu`, and writes one line into `segins_kern.ptx`
that nvcc does not write: `.maxnreg 56`, which keeps a block of 1024 threads inside the registers of one
multiprocessor. With that line the file is byte for byte the one my runs loaded. The programs load the CUDA driver
library at run time, so the toolkit is needed for this one step only. `sm_120` is the RTX 50 series, the only one I
tested.

Plans are written with LF line ends on every system. Earlier builds wrote CR LF on Windows, so a plan made there
before this release has another SHA-256 than the same plan here. The tools read both.

## Testing

    git clone https://github.com/jaypantone/superperm-upper-43-80
    xz -dkc superperm-upper-43-80/words/11/superpermutation-11-43930680.txt.xz > pantone-11.txt
    bash tools/test.sh pantone-11.txt

The script builds the twelve programs and runs them at n = 11 on Pantone's word and on my published plans, and at
n = 10 and n = 11 on the words of the other selections. It compares the length and the SHA-256 of every word it
writes with the values in the script, and checks every word with `delcheck`. It takes 5 to 9 minutes on one
thread and 0.6 GB. Tests 17 to 20 need Python 3 and are skipped without it. What it runs:

| test | from | to | tool |
|---|---|---|---|
| rebuild | plan of 43,930,614 on my 43,930,674 word | 43,930,614 | `trailsearch --time 0` |
| fixed-order pass | Pantone's 43,930,680 | 43,930,678 | `recut` |
| relocation | 43,930,678 | 43,930,660 | `relocate` |
| segment insertion, three cuts | 43,930,660 | 43,930,653 | `segins` |
| loop moves | 43,930,653 | 43,930,652 | `loopscan` |
| a second cycle of relocation and segment insertion | 43,930,652 | 43,930,652, the same word | `relocate`, `segins` |
| loop moves on Pantone's word | 43,930,680 | 43,930,678 | `loopscan` |
| fixed-order pass on my 43,930,628 word | 43,930,628 | 43,930,625, the word in `plan/history/` | `word2plan`, `recut` |
| the same with cuts inside a 1-cycle | 43,930,628 | 43,930,624 | `recut_wide` |
| segment insertion on the 43,930,623 plan | 43,930,623 | 43,930,622 | `segins` |
| search, 20,000 iterations on one thread | 43,930,680 | 43,930,661 | `trailsearch` |
| search with block moves, 5,000 iterations | 43,930,680 | 43,930,662 | `trailsearch_gpu` on the CPU |
| no substring can be deleted | 43,930,614 | | `letter del` |
| segment insertion, three cuts, the new program | 43,930,660 | 43,930,653, the word of `segins` | `segins_gpu` on the CPU |
| moves of equal length, 6 rounds | 43,930,623 | 43,930,620 | `segins_gpu --or3-eq` |
| local kicks, 150 trials | 43,930,623 | 43,930,619 | `segins_ils` |
| n = 10: selection, base word, word | `reproduce/selections/n10-selection.txt` | 4,034,855 | `geng.py`, `trailsearch --time 0`, `applyplan.py` |
| n = 11: selection, base word, word | `reproduce/selections/n11-selection.txt` | 43,930,578 | the same |
| the passes on the n = 10 base word | 4,036,801 (base word) | 4,035,422 | `recut`, `segins_gpu` |
| moves of equal length on the n = 11 word, 3 rounds | 43,930,578 | 43,930,578, another word of the same length | `segins_gpu --or3-eq` |

In tests 17 and 18 the word that `trailsearch` rebuilds from the base word and the plan must be byte for byte the
word that `reproduce/tools/applyplan.py` writes, with the SHA-256 given in `reproduce/REPRODUCE.md`.

With `GPU=1` it also runs the search of `trailsearch_gpu` and the two `segins_gpu` tests on the card and compares
them with the CPU runs; that needs `bash tools/mkptx.sh WORK/bin` first.

On the sources of this release the script passes all 34 tests with `GPU=1` on Windows 11 (MinGW gcc 13.2,
kernels built with CUDA 13.4) and on Ubuntu 24.04 under WSL 2 (gcc 13.3, kernels built with CUDA 12.9), with the
same lengths and hashes on both.

There is no script for n = 12. I ran the tools of the first release there once, on 2 threads. `trailsearch` rebuilt
the 522,745,464 word from `plan/history/trailsearch-12-522745464-rb.plan`, and `relocate` took it to 522,745,445.
Both words have the SHA-256 values listed in `plan/history/README.md`. Three rounds of `segins` with three cuts
then gave 522,745,418, `loopscan` found nothing and `recut` gave 522,745,416. `delcheck` passed every word.

The search options of the two new programs were compared with the programs that made the words at n = 11: 23
runs, each with the same plan and the same word from both. At n = 12 I ran `segins_gpu` of this release twice, on
2 threads, from the plan of the 522,740,945 word on the pieces of selection C: with `--gap3` and with `--gap3-list`
it wrote the plans of 522,742,394 and 522,742,408 letters that the working version had written, byte for byte, at
0.7 GB.

At n = 13 I made two runs with the sources of this release. `trailsearch` rebuilt the word of 6,747,802,875 letters
from its base word and its plan, with the SHA-256 of the front page, in 4 minutes on 10 threads and 10 GB.
`segins_gpu` repeated one pass of the runs that made the word, the one from 6,747,803,497 to 6,747,803,439, with
the same options, the same seed, 10 threads and the card. It wrote the same plan and the same word, byte for byte,
after the same 97 rounds, in 13 minutes at 18.6 GB. A run with moves of equal length repeats exactly for a seed
and a number of threads.

## Working on the sources

After this release the files here are also the sources I work on. If you change one:

* Run `bash tools/test.sh pantone-11.txt` before and after. A change that is meant to keep the behaviour must keep
  every length and hash of the script. The searches of tests 11 and 12 repeat exactly for a seed on one thread.
* A pass must never return a longer word, and every word a program writes should go through `delcheck`.
* Format with `clang-format` and the `.clang-format` of the repository, and keep the comments: every file has a
  header with what it does, how to build it, its options and where its parts start, and every function that is
  not trivial says what it computes and what it assumes.
* The loader exists in several copies (see "What these files are"). A change to it has to be made in each, or
  stated as made in one only.
* Plans are written with LF line ends. A plan file is the only state: a program that stops leaves its best plan,
  and any other program goes on from it.

## The tools one by one

The n = 11 figures are from one run of each tool on one thread, made for this release. They include a few seconds
of loading. The n = 12 and n = 13 figures are from the runs that made the words, on a Ryzen 9 5950X that was busy
with other jobs; where a figure comes from a run of this release it says so. Memory is the peak of the process.
"Not run" means that I never ran the tool at that size.

### trailsearch

It removes a few trails from the sequence, puts each back at its best place with its best cut and accepts the
result by the rule of simulated annealing. With several threads, independent searches share the model and the odd
threads restart from the best sequence from time to time. With `--plan-in PLAN --time 0` it only rebuilds the word
of a plan. This version writes the same plan as the first published one for the same command on one thread and is
about four times faster.

    trailsearch BASE.txt OUT.txt --plan-in PLAN --time 0                       # rebuild
    trailsearch BASE.txt OUT.txt --time 10800 --seed 51 --kmax 12 --T0 0.3 --threads 8 --sync 120 [--focus 0.9]

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 90 MB | 0.8 GB | 10 GB for a rebuild; 11 GB and 0.45 GB per search thread with the first version |
| rebuild | 8 s | 68 s on 2 threads | 4 min on 10 threads; about 10 min with the first version |
| search | 20,000 iterations in 1 to 2 min | 1,500 iterations in 10.5 s | not run with this version |

On its own the search gave 43,930,628, 522,745,537 and 6,747,917,987. After the passes below have run it finds
almost nothing more.

### recut

For a fixed order of the pieces the best cuts of all trails together are a shortest path through layers, one layer
per piece and one state per cut. A join costs h = n - 3 minus an overlap, so a layer is handled with tables indexed
by the ends of the words, in time proportional to its number of cuts. Theo H. found the same pass independently.

    recut BASE.txt OUT.txt --plan-in PLAN --co-skip --time 0

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 90 MB | 0.8 GB | one byte per cut more than the rebuild, 0.5 GB |
| time | 11 s, of which the pass is 0.3 s | 51 s on 2 threads, of which the pass is 4 s | 402 s |

One pass gave 43,930,628 to 43,930,625, 522,745,537 to 522,745,531 and 6,747,917,987 to 6,747,917,970. After a
round of search it gives 1 to 8 letters.

### relocate

From the tables of the fixed-order pass run from both ends it computes exactly what is saved by taking a window of
neighbouring trails out when all other cuts may change, and what it costs to put a trail somewhere else when its new
neighbours may be cut again. Windows whose saving is larger than the cost are moved and the move is confirmed by the
pass. There is no random search in it.

    relocate BASE.txt OUT.txt --plan-in PLAN --threads 1 --time 0 --dpa --dpa-thr 4 --dpa-v      # n = 13: add --dpa-full 2

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 110 MB | 1.0 GB | 12.5 GB |
| one sweep | 2 to 21 s | 45 to 72 s on one thread | 330 to 460 s on 8 threads |
| a run | 43,930,678 to 43,930,660 in 20 s | 522,745,526 to 522,745,483 in 751 s on one thread; 522,745,464 to 522,745,445 in 282 s on 2 threads | 6,747,917,824 to 6,747,917,498 in 6,916 s |

At n = 11 it finds nothing on words that have been through the search and the fixed-order pass. On a word that has
not, wider settings pay: from 43,930,678 the defaults reach 43,930,660 in 18 s, and
`--dpa-lmax 40 --dpa-imax 3 --dpa-tau 2 --dpa-win 8 --dpa-full 3` reaches 43,930,649 in 90 s.

### segins

The sequence is cut at three to six joins and the blocks of pieces between the cuts are put together in another
order. With three cuts this is a 3-opt move without reversal: two neighbouring blocks of any length change places.
Candidates come from a table that says what every join is worth when the cuts on both sides may change, by a chain
search as in the method of Lin and Kernighan. Every candidate is then judged exactly, with the best cuts of the
whole new sequence, and a round makes all shorter moves that do not disturb each other.

    segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 5 --or3-slack 4                    # n = 11
    segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 4 --or3 5 --or3-slack 1                    # n = 12
    segins BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 8 --or3 3 --or3-slack 0 --or3-maxcand 3000 \
           --or3-sec 14400 --or3-stop STOPFILE                                                           # n = 13

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 125 to 140 MB | 1.1 GB | 12.6 GB |
| one round | 18 s for a whole run with 3 cuts and slack 0; 5 min with 5 cuts and slack 2 on one thread | 27 s with 3 cuts on 4 threads, 104 s on 2 threads; 45 to 75 s with 5 cuts and slack 1 on 2 threads | 270 s the first, then 70 to 120 s, with 3 cuts on 8 threads |
| a run | 43,930,623 to 43,930,614 | 522,745,445 to 522,745,383 in 492 s | 6,747,917,421 to 6,747,916,917 in 4,050 s |

This is the pass that gave the most. The slack is a filter and not a bound: larger values find more and cost much
more. With slack 2 the first version did not finish a round at n = 12.

At n = 13 I ran this version with three cuts only. A move of four cuts made of two pairs gets too high an estimate
here when one of its new joins is not in the lists. That does not change the result, because every candidate is
judged exactly, but with five cuts at n = 13 such moves were 107,087 of the 107,692 candidates of a first round.
`segins_gpu.c` gives the joins of such candidates their exact values.

### segins_gpu

Segment insertion as in `segins`, for long words and for piece sets with many pieces of the same kind. What is new
is in the header of the file, in six points:

1. What a round needs is kept from round to round: the tables are brought up to date where the moves changed them
   and are not made again, and so are the exact values of joins, the gains of judged candidates and the pair lists.
2. A candidate whose blocks are all long gains exactly its estimate, so it gets exact values and is judged only if
   the estimate is 1 or more (`--or3-long Z`).
3. The candidates can be judged on an NVIDIA card (`--or3-gpu`), with the same gains and zones as on the CPU.
   `--or3-gpu-check` judges on both and compares.
4. A round can take moves that leave the length as it is (`--or3-eq E`). On the new pieces this is what keeps the
   search going after the shorter moves are used up.
5. The candidates of a round are kept in a fixed amount of memory (`--or3-hmem MB`, on by default), with the same
   candidates, order and moves as with one list.
6. `--gap3` and `--gap3-list FILE` keep only cuts at vertices, the model in which a plan lifts from n to n + 1
   (see `arrange/`).

    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 3 --or3-slack 0 \
               --or3-maxcand 200000 --or3-gpu                                              # n = 12
    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 3 --or3-slack 1 \
               --or3-eq 3000 --or3-long 600 --or3-gpu --or3-seed 1 --or3-sec 180           # n = 12, equal length
    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 10 --or3 3 --or3-slack 0 \
               --or3-v 3 --or3-x 6 --or3-long 1000 --or3-maxcand 200000 --or3-gpu \
               --or3-gpu-check --or3-gpu-checkmax 600 --or3-sec 3600 --or3-stop STOPFILE   # n = 13
    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 10 --or3 3 --or3-slack 1 \
               --or3-v 4 --or3-x 5 --or3-long 1000 --or3-eq 30000 --or3-eq-keep 2000000 \
               --or3-seed 1 --or3-gpu --or3-sec 2700                                       # n = 13, equal length

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| host memory | 0.13 to 0.16 GB, 0.27 GB with the card | 2.0 GB with the card before any candidate, 0.2 to 0.7 GB for the candidates (7,200 pieces) | 18.6 to 19.4 GB with narrow pair lists (about 24,000 pieces) |
| card memory | not measured | not measured | 6 to 8 GB |
| time | a whole pass of three cuts 8 s; two rounds of five cuts with slack 1: 64 s on the CPU, 9 s with the card | a round with moves of equal length 3 s on 2 threads, of which judging is 0.1 s; 16 to 19 s on the CPU | 408 rounds with moves of equal length in 2,700 s on 10 threads |

The n = 11 figures are from runs of this release on one thread under Linux. Most n = 12 and n = 13 figures were
measured with the three programs this file was merged from. The merged program itself has run at n = 11 and n = 12
and, with moves of equal length on the card, at n = 13, where it made the last steps of the n = 13 word. Without
`--or3-gpu`, or when `segins_kern.ptx` is not found, it judges on the CPU and says so in one line of the log.

The moves of equal length were run as a loop of short passes (3 to 10 minutes, `--or3-sec`), each from the best
plan so far and with another `--or3-seed`. That gave most of the letters after the first three-cut pass on the
new pieces of n = 12 and n = 13. Such a pass ends by itself after 20 rounds in a row without a gain
(`--or3-eq-stop K`); for one long pass set K high. Change the pair lists between passes: at n = 13 a pass with
`--or3-v 5 --or3-x 4` after passes with `--or3-v 4 --or3-x 5` found moves the first lists did not show, and took
the word from 6,747,803,439 to 6,747,803,080 in 3,000 seconds. The first lists then gave 205 letters more.

At n = 13 use narrow pair lists (`--or3-v 3 --or3-x 6`, then `--or3-v 4 --or3-x 5`): the default lists listed 79
million pairs there and ran the machine out of memory in an earlier version. Four cuts at n = 13 with the narrow
lists are a flood of 26 billion candidates and cannot be judged; with wider lists I have not run them.

### segins_ils

Local kicks. A trial makes one move that costs nothing or one letter, repairs it with segment insertions around
the place of the move, and keeps the result if the word is shorter, or as long and not seen before. Nothing is
computed again for the whole sequence, so trials are cheap: about 10 per minute at n = 12 and 1,000 per minute at
n = 11 on one thread.

    segins_ils BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --seed S --ils 540 --ils-log 120 \
               --ils-kmax 1 --ils-slack 2 --ils-near -1 --ils-cuts 3 --or3-stop STOPFILE                    # n = 12
    segins_ils BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 1 --seed S --ils 240 \
               --ils-kmax 1 --ils-kup 3 --ils-slack 2 --ils-near -1                                          # n = 11

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 0.3 GB on Pantone's pieces, 0.75 GB on the new ones | 1.95 GB | not run; about 16 GB by my estimate |
| speed | 1,170 trials per minute on Pantone's pieces, 740 on the new ones | 10.6 trials per minute | |
| gain | most of the letters from 43,930,605 to 43,930,578 on the new pieces; nothing below 43,930,614 on Pantone's | on Pantone's pieces 522,745,355 to 354, 352 to 351, 351 to 350: a letter in 3 of 8 runs of nine minutes; on the new pieces 522,737,395 to 522,737,299 in two loops of runs of seven minutes on one thread | |

A run with `--ils-trials N` repeats exactly for a seed, whatever the number of threads.

### loopscan

A trail does not have to be written in one piece. This tool cuts a block of consecutive pieces out of the sequence,
closes it into a loop and hangs the loop into another trail at a second cut of that trail, or the other way round.
It scans all such moves exactly and makes the ones that shorten the word. A move pays when a join already passes
through a cut of another trail, which does not happen in my final n = 11 words.

    loopscan BASE.txt --plan PLAN --only PABD --nogap1 --threads 4 --quiet --greedy --neutral --nbatch 16 \
             --maxrounds 40 --planout OUT.plan --out OUT.txt

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 95 MB | 0.55 GB | 6.3 GB |
| one scan | 1 s | 2.6 s | 37 s on 8 threads |
| gain | none on my final words | 1 to 3 letters per run | 6,747,917,498 to 6,747,917,464 in 27 min |

### trailsearch_gpu

The search of `trailsearch.c` with three additions: the best place of every big trail is found on the card, whole
blocks of pieces are moved without being cut again, and the fixed-order pass is kept up to date inside the search.
The card gives the same answers as the CPU code, and the program prints a checksum of all accepted moves so that
two runs can be compared. Without `--gpu` it runs on the CPU.

    trailsearch_gpu BASE.txt OUT.txt --plan-in PLAN --time 1200 --seed S --threads 4 --kmax 14 --T0 0.6 --focus 0.8 \
        --sync 120 --ckpt 120 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --coit 2000 --co-skip --gpu --ptx kern.ptx

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| host memory | 95 MB on one thread | not measured | 11 to 13 GB |
| card memory | 0.5 GB, of which 42 MB are tables | 11 bytes per cut, 0.44 GB, and a copy of the sequence per thread | 11 bytes per cut, 5.3 GB, and a copy of the sequence per thread |
| speed | 7,000 iterations per second on one thread; 1,600 with block moves and the pass inside | 2,600 to 4,400 on one thread | 1,700 on 4 threads with the earlier card code |

Rounds of this search, each followed by the passes, took n = 12 from 522,745,530 to 522,745,464.

### recut_wide

The fixed-order pass with one more kind of cut. A trail cut inside a 1-cycle is two letters longer, but two such
pieces can overlap in n - 2 or n - 1 letters, more than the n - 3 of the other tools. This is Theo H.'s idea. The
pass offers these cuts where a neighbour can use them.

    recut_wide BASE.txt OUT.txt --plan-in PLAN --wide --co-skip --time 0

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 100 MB | not measured | not run |
| time | 13 s | 60 s | not run |

It gave 43,930,628 to 43,930,624 where `recut` gives 43,930,625, and at n = 12 the word 522,745,530 where `recut`
gives 522,745,531. On every later word it gives what `recut` gives. Take the word it writes and not the plan: the
other tools do not know the long overlaps. `word2plan --rebase` turns such a word into a base word and a plan that
the other tools can go on from.

### word2plan

It reads a base word and any other word made of the same trails and writes the plan that rebuilds the other word
from the base word. I use it to read other people's words and to write my words as plans on Pantone's words.
`--rebase` handles words with cuts inside a 1-cycle. `--rephase` is the pass of `recut_wide` in an earlier form.

    word2plan BASE.txt OTHER.txt PLAN

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 245 MB | 3.0 GB | refused: it would need 31 GB |
| time | 15 s | not measured | |

### delcheck

It checks that every permutation occurs and lists the letters that can be deleted without losing one. It is the
same test as Pantone's `literal_check --deletions` with 2 bits per permutation.

    delcheck WORD.txt [threads]

| | n = 11 | n = 12 | n = 13 |
|---|---|---|---|
| memory | 23 MB | 150 MB | 1.6 GB |
| time | 3 s on one thread | 21 s on 4 threads, 22 to 30 s on 2 | 2 min on 8 threads |

### letter

Moves on the letters of a word without any knowledge of trails: deleting substrings, replacing windows of letters
by shorter ones (exact, by branch and bound), exchanges of parts of the word. On my words it finds nothing. I
keep it for what that says: in the 43,930,623 word no substring of any length can be deleted and no window of up to
49 letters can be replaced by a shorter one. At n = 11 `del` takes 18 s and 0.6 GB. The program works up to n = 12.

    letter del WORD.txt
    letter win WORD.txt --what sweep --R 24

## The drivers

`polish.sh DIR BASE PLAN [THREADS] [CYCLES] ["--or3 5 --or3-slack 1"]` runs `relocate`, `segins` and `loopscan` in
turn until a whole cycle gains nothing. Every word is checked with `delcheck` before its plan is accepted.

`rounds.sh` alternates rounds of `trailsearch_gpu` with the passes. `kick.sh` is for the point where neither finds
anything: a short search at a constant high temperature ends on a sequence a few letters longer than the best, and
the passes start again from there. At n = 12 this gave 522,745,376 to 522,745,374 and 522,745,366 to 522,745,355.
At n = 11 it found nothing below 43,930,614.

Each script says in its first lines what I ran with it. They look for the binaries next to themselves, or in the
directory named by `TOOLS`.

## What is experimental

* `recut_wide.c` and `kern_wide.cu`. The pass is tested at n = 11 and n = 12. Its search and its card code were
  not tested again for this release, and nothing in it has run at n = 13.
* In `trailsearch_gpu.c`: removal rules 4, 5 and 7 and `--ties` showed no benefit, and I have no measurement that
  shows a gain for `--reow`.
* In `segins.c`: `--or3-zone` ended on longer words in the runs I made, and `--bs` finds nothing on words that
  have been through the other passes.
* In `relocate.c`: `--dpa-sec`, the pass inside the search.
* In `loopscan.c`: everything except the command line above was used for analysis only. `--wide` writes plans that
  the other tools read as longer words.
* `trailsearch.c` in this version has rebuilt one n = 13 word, the newest. Its search has not run at n = 13, and
  the earlier n = 13 words in this repository were rebuilt with the first version.
* The three driver scripts were rewritten for this release, without the paths of my machine. I tested them at
  n = 11 on the CPU. The runs that made the words used the earlier scripts. They drive the tools of the first
  release; the loops with moves of equal length and with local kicks were run by hand, as described above.
* `segins_gpu.c` is a merge of three programs that each made words: the one with the card, the one with moves of
  equal length and the one with bounded memory. The merged program gives their plans on the cases I compared, at
  n = 11 and n = 12. At n = 13 it has run with three cuts and moves of equal length only, and the source of this
  release repeated one of those passes byte for byte. In it: `--or3-hmax` and `--or3-eq-max` are hardly tested,
  and `--or3-focus` showed no gain.
* `--gap3` and `--gap3-list` in `segins_gpu.c`: checked at n = 11 and n = 12 against the working version of the
  option. No published word was made with it; it is here because it is the way from a plan on n symbols to a plan
  on n + 1 symbols.
* `segins_ils.c` has not run at n = 13. Its other kinds of kick (`seg`, `db`, `ins`) and `--ils-rebase` are tested
  for identical output only.

## Solvers

Nothing that rebuilds or checks a published word needs a solver. One file here does: `runjoin.py`, the first step
of October 2 and 3, which orders the runs of a word with Gurobi and gave the 43,930,674 and 6,747,918,058 words.
Those two words are in `words/`, and every later plan refers to them or to Pantone's words, so the step does not
have to be repeated. To run it you need `gurobipy` with a full licence. The licence that comes with the PyPI package
is limited to about 2,000 variables and constraints, which is too small for these models. Academic users can get a
free full licence from Gurobi, others need a commercial one. I have not tried the model on an open solver.

`connector_splice.py` needs `numpy`. The checkers in `proofs/n9/` need `numpy` and no solver.

## Not here

Two variants of segment insertion that gave letters are not in this directory. Probe moves (a few moves that add a
letter, taken back unless something better appears next to them) gave 522,745,355 to 522,745,352 on Pantone's
closed trails; on the new pieces moves of equal length do that work. The first CPU program with moves of equal
length is replaced by `segins_gpu.c`, which takes the same moves.

The eight copies of the search program are not merged yet. A trial merge of `trailsearch`, `recut`, `relocate` and
`segins` into one file gave the same words on the tests above; the real merge will follow.

## Licence

Apache License 2.0, as the rest of the repository. All code here is mine. Theo H.'s repository is under the GPL and
I took no code from it, only the idea of cutting inside a 1-cycle, which is credited above and in `NOTICE`.
