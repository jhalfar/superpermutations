# Reproducing the words from their selections

This folder holds what is needed to rebuild four superpermutations, each from a small input, and to check them.
The construction is Jay Pantone's (slices of 2-loops, selection, completion, closed trails; his summary
`docs/upper-bound-explained.pdf` in jaypantone/superperm-upper-43-80). What differs is the selection, and with it
the closed trails the words are made of. This is research code: every program does one thing and prints what it
checked.

| n | length | input | plan |
|---|---|---|---|
| 10 | 4,034,855 | `selections/n10-selection.txt` (9 symbols, 56 KB) | `plan/n10-4034855.plan` |
| 11 | 43,930,578 | `selections/n11-selection.txt` (10 symbols, 0.5 MB) | `plan/n11-43930578.plan` |
| 12 | 522,737,175 | `selections/n12-selection.txt.xz` (11 symbols, 0.6 MB, 5 MB of text) | `plan/n12-522737175.plan` |
| 13 | 6,747,802,393 | `selections/n13-selection.txt.xz` (12 symbols, 2.9 MB, 54 MB of text) | `plan/n13-6747802393.plan` |

## The pipeline

1. `tools/geng.py` reads a selection on n - 1 symbols, checks it, completes it and finds the closed trails on
   n symbols.
2. It writes every closed trail once into a base word (a valid superpermutation, not a short one) and a table that
   says where each trail lies.
3. `tools/applyplan.py` writes the trails in the order of the plan, each cut open where the plan says, with the
   largest overlap between neighbours. That is the word.
4. `tools/check_min.py` and `tools/delcheck.c` check the word, and its SHA-256 is compared with the one below.

`geng.py` imports `tools/gen12.py`. You need Python 3, numpy (for `check_min.py` only), a C compiler with OpenMP,
and `xz` for n = 12 and 13 (Python's `lzma` module reads the same files). None of this needs a solver.

## Terms

I use Pantone's terms, with these differences.

- **Loop** is his 2-loop. A selection on K + 1 symbols has K letters 0 .. K-1 and the distinguished letter s = K; a
  loop is a cyclic order of the K letters. n = K + 2.
- **Row** is the slice a selection takes from a loop. The row (x, v) is his S(x, s; v): it starts at x and has v
  cyclic classes. v = K is full, v = K - 2 is short.
- **Loop without a row** is a 2-loop from which the selection takes no slice (a left-over loop). Completion covers
  its K classes with K repair slices, and these form a closed trail of their own, of (n - 2) n^2 letters. I call it
  a small trail.
- **Rows of other lengths** have any number v of classes from 1 to K - 3. I use Pantone's rules as they stand,
  read for general v. The row after (x, v) starts at x[v+1 ..] x[.. v-2] x[v] x[v-1] (after a full row at
  x[1 .. K-2] x[0] x[K-1]). Its completion is the K inserted slices S(x with z before x[j], s; v + [j < v]),
  j = 0 .. K-1, and the K - v repair slices S(rot^i(x) s, z; K + 1), i = v .. K-1. Such rows do not transport, so
  a selection that has them serves its own n only.
- **Closed walk** is a closed trail of the selection itself, on n - 1 symbols. I keep **closed trail** for the
  trails after completion, on n symbols. Written out as a word, a closed trail is a **piece**.
- **Q** is the sum of K - v over the rows, the number of classes the rows miss. Completion gives K! + Q slices, and
  the cyclic words of the closed trails have F3(n) + Q letters in total (**sum R**), F3(n) = n! + (n-1)! + (n-2)!.
- **Cut** is the place where a closed trail is opened to be written as a word. At a vertex (a step of weight 3) it
  costs nothing, at a step of weight 2 one letter. A **join** is the overlap of two consecutive pieces, at most
  h = n - 3 letters. A **plan** lists the pieces in order with their cuts.

## Commands

Run the commands from this folder (with `python3` where that is the name of the interpreter). The last argument
of `delcheck` is the number of threads.

```sh
gcc -O2 -fopenmp -o delcheck tools/delcheck.c
mkdir -p work
```

n = 10:

```sh
python tools/geng.py selections/n10-selection.txt work/n10-base.txt --table work/n10-base.tsv
python tools/applyplan.py work/n10-base.txt work/n10-base.tsv plan/n10-4034855.plan work/superpermutation-10-4034855.txt
python tools/check_min.py 10 work/superpermutation-10-4034855.txt
./delcheck work/superpermutation-10-4034855.txt 2
sha256sum work/n10-base.txt work/superpermutation-10-4034855.txt
```

n = 11:

```sh
python tools/geng.py selections/n11-selection.txt work/n11-base.txt --table work/n11-base.tsv
python tools/applyplan.py work/n11-base.txt work/n11-base.tsv plan/n11-43930578.plan work/superpermutation-11-43930578.txt
python tools/check_min.py 11 work/superpermutation-11-43930578.txt
./delcheck work/superpermutation-11-43930578.txt 2
sha256sum work/n11-base.txt work/superpermutation-11-43930578.txt
```

n = 12:

```sh
xz -dc selections/n12-selection.txt.xz > work/n12-selection.txt
python tools/geng.py work/n12-selection.txt work/n12-base.txt --table work/n12-base.tsv
python tools/applyplan.py work/n12-base.txt work/n12-base.tsv plan/n12-522737175.plan work/superpermutation-12-522737175.txt
python tools/check_min.py 12 work/superpermutation-12-522737175.txt
./delcheck work/superpermutation-12-522737175.txt 2
sha256sum work/n12-base.txt work/superpermutation-12-522737175.txt
```

n = 13 (14 GB of disk; `--noliteral` leaves out one of the two ways `geng.py` finds the trails, the one that needs a
dictionary with one entry per slice):

```sh
xz -dc selections/n13-selection.txt.xz > work/n13-selection.txt
python tools/geng.py work/n13-selection.txt work/n13-base.txt --table work/n13-base.tsv --noliteral
python tools/applyplan.py work/n13-base.txt work/n13-base.tsv plan/n13-6747802393.plan work/superpermutation-13-6747802393.txt
python tools/check_min.py 13 work/superpermutation-13-6747802393.txt
./delcheck work/superpermutation-13-6747802393.txt 2
sha256sum work/n13-base.txt work/superpermutation-13-6747802393.txt
```

## Expected results

`geng.py` prints the first nine lines of this table, `applyplan.py` the events and the length.

| | n = 10 | n = 11 | n = 12 | n = 13 |
|---|---|---|---|---|
| loops of the selection, (n-3)! | 5,040 | 40,320 | 362,880 | 3,628,800 |
| rows: full / short / other lengths | 3,528 / 1,176 / 0 | 29,730 / 9,620 / 298 | 271,824 / 86,016 / 2,688 | 2,716,896 / 888,048 / 11,088 |
| loops without a row | 336 | 672 | 2,352 | 12,768 |
| closed walks | 2 | 52 | 304 | 1,248 |
| Q | 2,352 | 20,726 | 182,112 | 1,818,768 |
| slices after completion, (n-2)! + Q | 42,672 | 383,606 | 3,810,912 | 41,735,568 |
| closed trails: small + from walks | 336 + 14 = 350 | 672 + 128 = 800 | 2,352 + 1,296 = 3,648 | 12,768 + 11,040 = 23,808 |
| sum R = F3(n) + Q | 4,034,352 | 43,929,206 | 522,729,312 | 6,747,757,968 |
| base word, letters | 4,036,801 | 43,935,602 | 522,762,033 | 6,747,994,945 |
| events of the plan | 355 | 800 | 3,648 | 23,808 |
| word, letters | 4,034,855 | 43,930,578 | 522,737,175 | 6,747,802,393 |
| letters spent on cuts and joins (word - sum R) | 503 | 1,372 | 7,863 | 44,425 |

A plan has more events than trails when some trails are written in two segments. `check_min.py` must end with
`VALID: every permutation occurs`; `delcheck` must print `"missing_permutations":0` and
`"coverage_preserving_deletions_count":0` (no letter can be deleted).

```
SHA-256 (files of one line, ending with a line feed)
n = 10  base word  0ccfcddc26ed6a3268d38dabd8398c308cdf3a14e0d957c88fa554c9ecbd48c3
        word       09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6
n = 11  base word  9bcb862f56592583c4e4f34e9c7d366e2c3753be98b08d3ce1877ecec02a4e84
        word       65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092
n = 12  base word  0d36cdd07fe7c90912fc0a295ca9b9895c9fba0ad0769196e2b37960b1657c68
        word       97ab1d7c37f1a19f9c9c10d8109382f501da1982f1b66bfa1ddd2511f9149cde
n = 13  base word  39491951984db206e07d63ab7beaa6c495f9499966f863804d15474dcdb65e26
        word       96bf9191a6fe281e6cb4a55eef989e158ab5e1d6e46373c3c7be6adb3dfc272b
```

Time and peak memory, one thread except `delcheck` (Ryzen 9 5950X, Windows, Python 3.14, while other jobs ran):

| step | n = 10 | n = 11 | n = 12 | n = 13 |
|---|---|---|---|---|
| `geng.py` | under 1 s, 0.03 GB | 2 s, 0.10 GB | 28 s, 0.73 GB | 3 min, 1.98 GB |
| `applyplan.py` | under 1 s, 0.02 GB | under 1 s, 0.02 GB | 1 s, 0.02 GB | 16 s, 0.05 GB |
| `check_min.py` | under 1 s, 0.19 GB | 8 s, 0.75 GB | 3 min, 0.84 GB | 33 min, 1.56 GB |
| `delcheck`, 2 threads | under 1 s, 0.04 GB | 2 s, 0.05 GB | 23 s, 0.15 GB | 3 min, 1.56 GB |

I ran the steps from a copy of this folder that held nothing else, with `OPENBLAS_NUM_THREADS=1` (without it numpy
reserves about 0.7 GB more on a machine with 32 threads). `delcheck` at n = 13 ran with 6 threads.

## How the selections and the plans were found

**How the selections were found.** The selection for n = 10 has full and short rows only. It differs from Pantone's
8-symbol selection transported once on 32 of the 5,040 loops. That gives 2 closed walks instead of 4, so 14 big
trails instead of 28, with the same Q. A neighbourhood search found it. The other three selections keep full and
short rows on most loops and differ in 48 blocks. A block is the set of loops that lie above one of the 48 loops
without a row of the 8-symbol selection, that is, the loops in which the seven old letters keep that cyclic order.
Walks inside a block that never exchange two old letters can be replaced without touching the rest, so a block is a
small search problem of its own, and it depends only on the number of added letters. n = 11: Pantone's selection on
10 symbols, with a walk of 42 rows in each of 38 blocks of 56 loops; the other 10 blocks were rebuilt together with
their neighbours so that their rows lie on one of the big walks. n = 12: the n = 10 selection transported twice,
with one solution of the block of 504 loops copied into all 48 blocks. n = 13: the same transported three times,
with one solution of the block of 5,040 loops. The block solutions use rows of other lengths. They come from integer
programmes and neighbourhood search and are not proved optimal as a whole. The programs are in
[`../selection/`](../selection/README.md): the search for the n = 10 selection, the block searches, and the scripts
that build the selections for n = 11, 12 and 13 again from Pantone's `construction-input.txt` and a few small data
files. The searches need a commercial solver. Building a selection from the data files does not.

**How the plans were found.** A plan decides where every closed trail is cut and what follows it. The start is a
plan that writes the small trails in chains, each following the previous one at the cost of one letter. Local search
then shortens it. It moves segments of the sequence elsewhere and chooses all cuts again by dynamic programming, it
accepts moves that keep the length, and it makes small random changes and repairs them. For n = 10 the order of the
48 groups of seven small trails is that of rumstd's word of 4,034,873 letters, carried over by a relabelling, with
the cuts and the places of the 14 big trails then chosen exactly for that order. The programs that make the start
plans and the n = 10 arrangement are in [`../arrange/`](../arrange/), the local search programs in
[`../tools/`](../tools/README.md). The plans here are their output. Turning a plan into its word needs only
`applyplan.py`, which searches nothing.

## The checks

I ran three programs that share no code on the words:

1. `tools/check_min.py`: every permutation occurs (numpy, one bit per permutation, about 60 lines).
2. `tools/delcheck.c`: every permutation occurs, and no single letter can be deleted without losing one.
3. Pantone's `literal_check --deletions` (`tools/literal_check.cpp` in his repository, not copied here): the same
   two statements.

- n = 10: checks 1, 2, 3 passed (all 3,628,800 permutations; 2,349 further occurrences of permutations already
  seen).
- n = 11: checks 1, 2, 3 passed (all 39,916,800 permutations; 19,784 further occurrences of permutations already
  seen).
- n = 12: checks 1, 2, 3 passed (all 479,001,600 permutations; 177,466 further occurrences of permutations already
  seen).
- n = 13: checks 1, 2, 3 passed (all 6,227,020,800 permutations; 1,797,600 further occurrences of permutations
  already seen). Check 3 was run on the same word in a separate run, with the Linux build, because the Windows build
  cannot read a file of this size.

`geng.py` checks the construction before any word exists: every loop on one line, balance, and the closed trails
found two ways that must agree (the cycles of the graph "slice to the slice whose head is its tail", and Pantone's
port rule), except at n = 13 where only the port rule is run.
