# The check before publication

Since 21 October 2026 a word for n up to 13 goes through `prepub.sh` before I publish it. The script checks the
word with three independent checkers (two at n = 13, where I run `literal_check` by hand under Linux) and then
tries to shorten it with the trail tools. A word is published only if the report ends with `CLEAN`; if a tool
finds a shorter word, the report ends with `SHORTER` and the new word goes through the check again.

Not every word in this repository went through it first. The words for n = 8 and 10 are older than the script; on
the word for n = 8 (46,174) it finds a word of 46,173 letters, as Theo H. did. On the words for n = 10 and 11 it
gave `CLEAN` later, on 13 November; the word for n = 11 is of 27 October. The words of November for n = 13 got
`CLEAN` one after another, but each time the reorder of [`reorder/`](../reorder/README.md), which is not part of
this script, followed by the card passes, found a shorter word. The words for n = 14 have no plan for the trail
tools, so only the checkers ran on them, and the recipes for n = 15 to 18 have checks of their own.

| file | what it is |
|---|---|
| `prepub.sh` | the check |
| `relabel.py` | finds whether a word is made of the closed trails of a base word up to a relabelling of the letters and a reversal, and writes its image |

## What it does

1. Three checkers: `reproduce/tools/check_min.py`, `delcheck` (every permutation present, no letter that can be
   deleted) and Jay Pantone's `literal_check --deletions` up to n = 12. A word that fails one of them stops here.
2. A base word and a plan: from `--selection` (`geng.py` writes the base word, `word2plan` the plan, which must be
   exact and safe to search from), or from `--base` and `--plan`, or the word itself as its own base. In the last
   case the script compares the number of closed pieces with the number of trails and warns about a mismatch: a word
   read as its own base can hide a closed trail. If the word does not fit the trails of its selection, `relabel.py`
   looks for a relabelling and the search runs on that image.
3. Six runs of `trailsearch` from the plan (kmax 8 and 12, T0 0.4, 0.7 and 1.2) and `recut --co-skip`.
4. `REPORT.txt` in the work directory: either `CLEAN: no tool shortened the word ...` or `SHORTER: ...` with the new
   word checked by `delcheck`. The exit code is 0, 3 for a shorter word, and 1 if a check failed.

The GPU segment insertion is not part of this script. From n = 11 on I also run [`gpucuts/orx.sh`](../gpucuts/README.md)
on the word's plan. [`gpucheck/prepub_gl.sh`](../gpucheck/README.md) is the same check with the first checks and the
loading of the searches on the card, and with all six searches in one process.

## Building

`delcheck`, `trailsearch`, `word2plan` and `recut` are built from `tools/` as [its README](../README.md) says.
`literal_check` is `tools/literal_check.cpp` of Jay Pantone's repository
[superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80), built as that repository says.
Put the binaries in one directory and give it as `TOOLS` (default: the directory of the script). `PYTHON` is the
Python 3 with numpy for `check_min.py` (default `python3`).

## Running it on one word

    TOOLS=bin bash tools/prepub/prepub.sh 12 superpermutation-12-LENGTH.txt --selection SEL.txt
    TOOLS=bin bash tools/prepub/prepub.sh 13 WORD.txt --base BASE.txt --plan PLAN --threads 4 --par 3

| option | meaning |
|---|---|
| `--selection SEL` | the selection of the word; the base word is built from it with all closed trails (preferred) |
| `--base BASE --plan PLAN` | use this base word and plan instead |
| `--time SEC` | seconds per trailsearch setting (default: 60 up to n = 9, 300 for n = 10, 600 for n = 11, 1200 above) |
| `--threads T` | search threads per setting (default 4) |
| `--par P` | P settings at a time, each with its own memory; check_min and recut then run beside the searches |
| `--out DIR` | the work directory (default `$PREPUB_RUNS/N-LENGTH-TIME`, with `PREPUB_RUNS` = `prepub-runs`) |

The word may be `.txt` or `.txt.xz`; line ends are ignored. The script never deletes anything outside its work
directory. At n = 13 one trailsearch setting needs about 11 GB plus 0.45 GB per thread, so `--par 3` needs about
three times that; `check_min.py` takes 22 to 33 minutes there, and `literal_check` is skipped above n = 12.
