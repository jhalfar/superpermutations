# From a word to a fixed point

These scripts take an n = 13 word made by someone else (or by another tool), build a base word and a plan for it,
and then run the passes of `tools/` in a loop until none of them gains. This is how I worked on words such as Jay
Pantone's after his reorder notes: the word is not written on the closed trails of a published selection, so the
plan has to be made on a base word built from the word itself.

| file | what it does |
|---|---|
| `base.sh` | word -> hybrid base word -> plan (`hyb13`, `pieces`, `w2p13o`, `unitsplit.py`) |
| `hyb13.c` | the hybrid base word: the trails of a base word N, with the trails the word changed replaced by its own |
| `pieces.c` | the piece table of a word: start, length, windows, a hash, gap to the next piece (not the `tools/pieces.c` of the first release) |
| `w2p13.c` | word2plan for n = 13 without the n! table, built as `w2p13o`; open pieces of the base are written whole (`P k`) |
| `unitsplit.py` | rewrites a plan so that the long W2058 trails are written as their unit segments, which the passes can then move one by one |
| `tsnum.py` | renumbers the trails of a `w2p13o` plan to the numbering of `trailsearch` |
| `loop.sh` | GPU three cuts while they gain, then `trailsearch` and a long `loopscan`; stops when both gain nothing |
| `longloop.sh` | `loopscan` for up to 1,000 rounds instead of 40, then `delcheck` and `vfast` (Pantone's W-0100 note) |
| `line13.sh` | the whole line: `base.sh`, `tsnum.py`, `loop.sh`, then `prepub.sh`, repeated while prepub finds a shorter word |
| `gpucuts.sh` | GPU passes with more cuts: four cuts slack 0, five cuts slack 0, five cuts slack 1 |
| `ils12.sh` | n = 12 rounds of `polish.sh` and two `segins_ils` lanes side by side |
| `tswg.sh` | `tsw5g2` with a memory guard in front, for `orx.sh` |
| `guard.py` | runs a command under a memory limit (Windows job object) |

## Building

    gcc -O2 -mpopcnt -fopenmp -o hyb13 hyb13.c
    gcc -O2 -mpopcnt -fopenmp -o w2p13o w2p13.c
    gcc -O2 -o pieces pieces.c

The scripts also call `tsw5g2` and `orkern.ptx` ([`gpucuts/`](../gpucuts/README.md)), `trailsearch`, `loopscan`,
`delcheck`, `segins_ils` and `polish.sh` from [`tools/`](../README.md), `vfast` from `recipes/n14/vfast.c`, and
`prepub.sh` from [`prepub/`](../prepub/README.md). Build every program into one directory and give it as `TOOLS`;
the scripts default to their own directory. gcc 13.2 (MinGW) compiles the three files above without a warning.

Environment of the scripts:

* `TOOLS`: the directory of the binaries.
* `PYTHON`: the Python 3 to use (default `python3`).
* `GUARD`: a command put in front of each heavy job, empty by default. On Windows I ran every job under
  `guard.py`, for example `GUARD="python -I tools/pipeline/guard.py --gb 20 --"` (20 GB in `base.sh` and `loop.sh`,
  14 GB in `longloop.sh`, 12 GB in `ils12.sh`, 34 GB in `gpucuts.sh`). `guard.py` works only on Windows.
* `BASEN` (for `base.sh`): the base word of selection N, the n = 13 base word `work/n13-base.txt` that the steps of
  `reproduce/REPRODUCE.md` write from `reproduce/selections/n13-selection.txt.xz` (6,747,994,945 letters).
* `BASE` (for `loop.sh`, `longloop.sh`, `gpucuts.sh`, `ils12.sh`): the base word the plan refers to.
* `MAP` (for `base.sh`): the relabelling of the word into the labels of N, as an argument of `tr '0123456789ABC'`.

`loop.sh` waits before each GPU pass while `nvidia-smi` shows the card busy (utilisation above 30 % or more than
12 GB used).

## Running it on one word

The word must be in the labels of selection N; if it is a relabelled image, find the map first by matching a few of
its closed trails with trails of N (`prepub/relabel.py` does this for whole words, but in pure Python, so only for
small n) and pass it as `MAP`.

    export TOOLS=bin BASEN=base13N.txt
    bash tools/pipeline/line13.sh WORD.txt LENGTH DIR

`DIR/line.log` ends with `END best LENGTH word W`. The steps one by one:

    MAP=0123456789ABC bash tools/pipeline/base.sh WORD.txt DIR/base          # DIR/base/base.txt, DIR/base/w.plan
    python tools/pipeline/tsnum.py DIR/base/base.txt DIR/base/base_p.tsv DIR/base/w.plan DIR/base/w.ts.plan
    BASE=DIR/base/base.txt bash tools/pipeline/loop.sh DIR/loop DIR/base/w.ts.plan LENGTH 6
    BASE=DIR/base/base.txt bash tools/pipeline/gpucuts.sh 13 DIR/gpu PLAN LENGTH

Check `DIR/base/base.log` before going on: `w2p13o` must report 0 anomalies, and `trailsearch BASE out.txt --plan-in
PLAN --time 0` must write the word letter for letter. A wrong letter map gives a plan full of anomalies.

## What the parts do

`hyb13` parses both words as `trailsearch` does (pieces split at steps of weight 4 or more) and identifies every
trail by its set of windows. A closed piece of the word with the window set of a trail of N is that trail; the other
closed pieces are new trails, and a trail of N that shares a window with a new trail is dropped. Open pieces of the
word that hold windows covered by nothing else are kept as open paths, which the tools never move. The new base is
the kept trails of N, the new trails and those open pieces, two separator letters between pieces, and the program
checks that its windows cover all n!. It needs about 8.5 GB at n = 13.

`w2p13o` reads the word event by event: from an index of about one window in 64 of the trails it finds where each
piece of the word starts in a trail and how far it matches. Anything that is not a cut of a trail is reported as an
anomaly, and the program exits with code 3 if there is one.

`unitsplit.py` is for the 96 W2058 trails of selection N, of R = 3,443,055 = 7 x 491,865 and R = 383,789 = 7 x
54,827. Pantone's 6,747,801,272 writes them in up to 7 segments, cut at the 7 rotation-equivalent weight-3 steps of
the trail. The script cuts every event of such a trail at these unit boundaries, so the word stays the same letter
for letter but `segins` and `polish.sh` can move every unit on its own.

`longloop.sh` and `ils12.sh` call the `loopscan` and `segins_ils` of `tools/`. My runs used the builds of the first
release, before the coverage checks were added; on a plan that is safe to search from the two give the same words.
