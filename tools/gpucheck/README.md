# Checks and loads on the card

These programs do the slow parts of checking a word, and of loading it into the trail tools, on an NVIDIA card.
Each one gives the same numbers as the processor tool it replaces, and I checked each against that tool before I
used it. They are fast first checks: in `prepub_gl.sh` the processor checkers still run and still give the verdict.

`gdelcheck` matters most. `delcheck` stops at n = 13, so at n = 14 `gdelcheck` is the only deletion check I have,
and my n = 14 note on the Superpermutation Almanac relies on it.

| file | what it is | the processor tool it matches |
|---|---|---|
| `gcheck.c` | coverage of a word: every permutation present, with vfast's numbers | `vfast` (`recipes/n14/vfast.c`) |
| `gdelcheck.c` | coverage and the single-deletion test, delcheck's fields and verdict | `delcheck` (`tools/delcheck.c`) |
| `gpuprep.cu` | the kernels of `gcheck` and `gdelcheck` | |
| `gp_cuda.h`, `gp_reader.h` | the CUDA driver library loaded at run time; the reader threads that feed the card in chunks | |
| `w2p13g.c`, `w2pg.cu` | word2plan for n = 13 with the bitmap passes, the index and the full lookups on the card | `w2p13o` (`tools/pipeline/w2p13.c`) |
| `trailsearch_gl.c`, `tsgl.cu` | trailsearch with the bitmap passes of its load on the card (`--gpuload`) | itself without `--gpuload` |
| `prepub_gl.sh` | `prepub.sh` with the card checks first, the card load and all six searches in one process | `tools/prepub/prepub.sh` |
| `gpubusy.sh` | exit 0 if the card is free | |
| `validate.sh`, `tstest.sh`, `w2ptest.sh` | the comparisons with the processor tools | |
| `corrupt.c` | writes a word with one change (letter replaced, deleted, swapped), for the tests | |
| `check_min_fast.py` | `check_min.py` on P ranges at once (`prepub_gl.sh --cmprocs P`) | `reproduce/tools/check_min.py` |
| `val/` | the results of my validation runs | |

## Building

    bash tools/gpucheck/build.sh OUTDIR

runs, for the three kernels and the five programs,

    nvcc -arch=sm_120 -O3 -ptx -o gpuprep.ptx gpuprep.cu        # also w2pg.cu, tsgl.cu
    gcc -O2 -Wall -o gcheck gcheck.c -lpthread
    gcc -O2 -Wall -o gdelcheck gdelcheck.c -lpthread
    gcc -O2 -fopenmp -o w2p13g w2p13g.c
    gcc -O2 -mpopcnt -fopenmp -o trailsearch_gl trailsearch_gl.c -lm
    gcc -O2 -o corrupt corrupt.c

On Linux add `-ldl` (`LIBDL=-ldl bash build.sh`). On Windows nvcc needs the MSVC build tools in its environment
(`vcvars64.bat`). The programs load the CUDA driver library at run time (`nvcuda.dll` or `libcuda.so.1`) and read
their `.ptx` file from the directory of the program, or from the current one; the toolkit is needed for the PTX
only. `sm_120` is the only architecture I tested. With CUDA 13.4 the three PTX files built from these sources are
byte for byte the ones my runs loaded. gcc 13.2 (MinGW) compiles everything with one warning, an unused function in
`gp_reader.h`.

## Running them on one word

    gcheck 13 WORD.txt                      # or WORD.txt.xz, or - for standard input
    gdelcheck WORD.txt 4                    # n up to 13
    gdelcheck WORD.txt 4 --shards 8 --nbuf 4   # n = 14: 13.5 GB of a 16 GB limit
    w2p13g BASE.txt WORD.txt OUT.plan
    trailsearch_gl BASE.txt OUT.txt --plan-in PLAN --time 0 --gpuload
    TOOLS=bin bash tools/gpucheck/prepub_gl.sh 13 WORD.txt --base BASE.txt --plan PLAN --threads 4 --par 6 --cmprocs 4

Each prints one JSON line (gcheck, gdelcheck) or the log of the program it replaces.

### gcheck

    gcheck N WORD [--alpha AL] [--skip P] [--chunk MB] [--nbuf K] [--readers R] [--io direct|buffered] [--xz EXE]

The full n! bit table sits on the card (10.9 GB at n = 14). Chunks of the file go to the card as bytes; a kernel maps
them to letters, ranks every window of n letters that is a permutation and sets its bit. A chunk with anything other
than letters is first filtered on the host exactly as vfast filters. The output has vfast's 11 fields in vfast's
order, then the alphabet and the times, and the exit code is vfast's: 0 only if nothing is missing, no byte is
foreign and the window count is right. `--skip P` checks the word without its letter P (0-based), which checks a
deletion without writing a copy. `--alpha` gives the letters; by default the first n of 0-9A-F, or the letters of the
first chunk if it has exactly n and one of them is outside that range. For a `.xz` word on a busy machine
`xz -dc WORD.xz | gcheck N -` is faster.

### gdelcheck

    gdelcheck WORD [threads] [--n N] [--skip P] [--shards K] [--chunk MB] [--nbuf B] [--readers R] [--io direct|buffered] [--xz EXE]

Pass 1 sets the bit of every permutation window in a "seen" table and, if it was set already, in a "twice" table.
Pass 2 marks for every window that occurs once the positions whose deletion would destroy it, using delcheck's
argument: one deletion destroys at most one occurrence of a permutation, and can only recreate a destroyed unique
window through an equal neighbour. The positions that no window protects are deletable; they are counted and the
first 4096 are listed. The output has delcheck's fields in delcheck's order, then the times; the exit code is
delcheck's (0, 3 if a permutation is missing, 2 on an error). `--shards K` makes pass 1 in K passes over the word with
1/K of the "seen" table on the card, which is what makes n = 14 fit.

### w2p13g and trailsearch_gl

`w2p13g` is `w2p13o` with the duplicate-window passes, the index and the full lookups on the card; the rest is the
code of `w2p13.c` unchanged. When a key occurs in several trails, it takes the matches in the order (trail, offset),
where `w2p13o` takes them in the order its threads find them.

`trailsearch_gl` is `trailsearch_fast`: `tools/trailsearch.c` with a faster load (three word passes in one, a faster
plan check and word write) and three options that are off by default. `--set OUT:KMAX:T0:SEED` (repeatable) runs
several settings on one loaded model, each with its own log `OUT.log`; `--setpar P` runs P of them at a time;
`--write-better-only` writes the word only if it is shorter than the input, and otherwise only the plan. `--prof`
prints the time of each phase. With `--gpuload` the word pass, the trail windows, the plan check and the coverage
check of the written word run on the card through a 256 MB buffer, which adds about 2.6 GB on the card and 0.3 GB on
the host at n = 13.

### prepub_gl.sh

The steps, checkers and verdict of `prepub.sh`, with these differences, none of which changes a search or the
verdict: `gcheck` and `gdelcheck` first, so a bad word stops in seconds; the checkers run in the background beside
the searches; all six settings run in one `trailsearch_gl` process on one loaded model (`--par P` of them at a time),
loaded on the card; a setting that does not shorten the word writes only its plan. If the card is busy
(`gpubusy.sh`), the card steps are skipped; `--nogpu` never uses the card. `--cmprocs K` runs `check_min_fast.py` on
K processes instead of `check_min.py`. `--par 6` at n = 13 needs about 11 GB plus 6 x threads x 0.45 GB in one
process, against 3 x 13 GB for `prepub.sh --par 3`.

## How each was checked

All runs compare the card tool with the processor tool on the same input; `val/` holds the JSON lines and the
tables of my runs (`results.tsv`: 95 of 95 passed, `tstest.tsv`, `w2ptest.tsv`).

* `gcheck`: 48 runs at n = 9 to 13, field for field equal to vfast and with the same exit code: record words; the
  corruptions of `corrupt` (a letter replaced, deleted or swapped, the first or the last letter deleted); a foreign
  byte, a line end inside, CRLF lines, lowercase letters, words of n - 1 and n letters, an empty word; 1 MB chunks,
  buffered reads, standard input and `.xz`; `--skip` at chunk edges.
* `gdelcheck`: 47 runs at n = 9 to 13 in `results.tsv`, equal to delcheck except for the times: words with deletable letters (a letter
  doubled, a window repeated, letters inserted at a chunk edge, the word written twice with 8,069,710 deletable
  letters), the corruptions, and `--skip`.
* n = 14: in a reordered word of 93,904,779,398 letters `gdelcheck --shards 8 --nbuf 4` found exactly one deletable
  letter, at position 46,605,489,182. Without it `gcheck --skip` and `gdelcheck --skip` give 0 missing and 0
  deletable, and vfast on one thread, fed the word without that letter through a pipe, gives length 93,904,779,397,
  missing 0, repeats 19,714,055 in 2,646 s. `delcheck` cannot run at n = 14.
* `w2p13g`: plans and logs identical to `w2p13o` in 3 cases at n = 13 (`w2ptest.sh`), one of them a plan with 51
  anomalies.
* `trailsearch_gl --gpuload`: plan, word and log identical to the run without the card in 11 tests (`tstest.sh`): n =
  10 to 12 with `--time 0`, with `--plan-in` and with `--iters`, and n = 13 with a plan and as its own base.
* `prepub_gl.sh` at n = 10: the same report and verdict as `prepub_fast`; it stops on a corrupted word and on a word
  with a deletable letter.

`validate.sh`, `tstest.sh` and `w2ptest.sh` repeat these runs. They need a work directory (`WORK`), and the words
that are not in this repository are optional: the header of each script says which.

## Times

On a loaded machine, 3 threads:

| step | n = 12 | n = 13 | n = 14 |
|---|---|---|---|
| vfast -> gcheck | 6.6 s -> 0.5 to 1.3 s | 85 to 90 s -> 1.4 to 2.1 s | 1,607 s -> 10.3 s (9 GB/s from disk) |
| delcheck -> gdelcheck | 12.7 s -> 0.65 s | 229 to 288 s -> 2.3 to 2.7 s | none -> 79 to 135 s |
| trailsearch load and rebuild (`--time 0`) | 25 s -> 6 to 10 s | 350 to 484 s -> 119 to 127 s with a plan; 237 s -> 80 s as its own base | |
| w2p13o -> w2p13g | | 617 to 783 s -> 94 to 106 s; a hard case 3,586 s on 6 threads -> 78 s | |

At n = 13 the rest of the trailsearch load is the pass over the cuts on the processor, about 70 s, and
`trailsearch_gl` peaks at 14.7 GB committed (memory on the card counts against a job limit on Windows).
