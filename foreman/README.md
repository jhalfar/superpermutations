# foreman: runs the search tools for you

Shortening a superpermutation with the tools in [`tools/`](../tools/README.md) is a long chain of runs: trailsearch
with several settings, segment insertion, local kicks, loop moves, a fixed-order pass, and so on. Each run starts from
the best plan so far, and a person usually decides which tool comes next. foreman makes that decision itself. It
keeps every plan it gets in a store, picks the next (tool, setting) from what has paid off so far, gives a tool more
time or larger caps when it stops gaining, never repeats a setting that gave nothing on the same plan, and stops
when no tool gains anything on the best plan any more (a fixed point). Every shorter word is checked with delcheck
(no permutation missing) before it counts.

foreman found the n = 12 word of 522,736,429 letters this way, from William Echols's W-0091; the steps are in
[`recipe/RECIPE.md`](recipe/RECIPE.md).

## What it needs

* Python 3.9 or newer (standard library only) and bash (on Windows: Git Bash).
* The tools built in `tools/` as [`tools/README.md`](../tools/README.md) says: `trailsearch`, `recut`, `relocate`,
  `segins`, `segins_ils`, `loopscan`, `delcheck`, `word2plan` (and `recut_wide` for the arm `wide`), with
  `tools/polish.sh`.
* For the arm `gpu_or3` and the card passes of `expert12`: `tools/gpucuts/tsw5g2` with `orkern.ptx` next to it
  ([`tools/gpucuts/README.md`](../tools/gpucuts/README.md)) and an NVIDIA card with `nvidia-smi`. `expert12` also calls
  `tools/pipeline/ils12.sh`.
* For the arm `cutlns`: `tools/reorder/steps` and `tools/reorder/cutlns2.py` with numpy, scipy and gurobipy (and a
  Gurobi licence for models of this size); at n = 13 also `tools/pipeline/w2p13o` and `unitsplit.py`. For the arm
  `rebase`: `tools/prepub/relabel.py`.
* A base word and a plan on it (a plan is the word written as pieces of the base; `tools/word2plan BASE WORD PLAN`
  makes one from a word).

foreman runs on Windows and on Linux. By default it expects the tools in `tools/` next to this folder and writes its
work files to `foreman/work/`; copy `config.example.json` to `config.json` to change that.

## Run it on one case

    bash foreman/fm.sh add-case w12 --n 12 --base BASE.txt --plan START.plan --max-hours 24
    bash foreman/fm.sh run w12 --threads 8 --gb 24
    bash foreman/fm.sh status w12

`add-case` reads the plan's length with trailsearch (or takes `--length L`). `run` keeps going until every case it
was given is at a fixed point, at its target (`--target L`) or out of budget (`--max-hours`, `--max-cpu-hours`).
`--arms ts,ils,recut` limits a case to some arms. `--report-below L` marks a verified word shorter than L as a
record in the event log; `run --on-record CMD` (off by default) also runs `CMD LENGTH WORD PLAN` for such a word.
`bash foreman/fm.sh report` prints a table of all cases: start, best, hours, the curve of the best length over time
and the letters each arm gained.

To repeat the run that gave the 429: the base word of the n = 12 package, the start plan in `recipe/`, and

    bash foreman/fm.sh add-case w0091 --n 12 --base base12_hybrid_e.txt --plan foreman/recipe/W-0091_on_base12_hybrid_e.plan --arms expert12
    bash foreman/fm.sh run w0091 --threads 8 --gb 24

While it runs: create the file `PAUSE` next to `foreman.py` to suspend every job, `STOP` to stop the running jobs
early and end, `RELOAD` to load edited arms without stopping. Its state is one SQLite file, `foreman.db`.

## What it has done so far (13-14 November 2026)

Lengths are word lengths in letters. Hours are wall-clock hours from the start of a case to its best word, and
thread-hours (threads x hours) of foreman's runs; foreman ran with at most 12 threads, often 6-8 because other jobs
shared the machine. Every best word passed delcheck. The benchmark runs used a larger set of arms than this copy,
some of them calling programs that are not in this repository (an exact solver for n = 8, another
reordering, other search variants, neutral moves); the case bench12z, which found the 429, used only the arm
`expert12`, which is included.

Benchmarks that re-found words already known (foreman started from a word with a known shorter word after it):

| n | start word | known later word | foreman's best | hours / thread-hours |
|---|---|---|---|---|
| 8 | 46,174 (W-0077) | 46,173 (Theo H., W-0078) | 46,173 | 0.1 / 0.1 |
| 8 | 46,173 (W-0078) | none known | 46,173, no shorter word | 4.0 thread-hours |
| 9 | 408,719 (Jay Pantone, W-0099) | 408,718 | 408,718 | 3.3 / 7.9 |
| 9 | 408,718 (the word above) | 408,717 (on another selection) | 408,717, on W-0099's own selection | 3.9 / 10.2 |

For the 46,173 of W-0078 an exact dynamic programme of mine, which is not in this repository, gives 46,173 as the
shortest word that writes each of the 16 closed trails of its selection once, in any order, opened at a step of
weight 1, 2 or 3, with neighbouring pieces joined by their largest overlap. Nobody else has checked that.

Benchmarks that went below their start but not as far as a later word:

| n | start word | later word | foreman's best | hours / thread-hours |
|---|---|---|---|---|
| 11 | 43,930,674 (`words/`) | 43,930,534 (`words/`) | 43,930,629 | 1.1 / 1.9 |
| 12 | 522,737,299 (`words/`) | 522,736,969 (`words/`) | 522,736,913 (below 969) | 29.7 / 60.4 |
| 12 | 522,736,503 (William Echols, W-0091) | 522,736,440 (a chain run by hand in about 20 h) | 522,736,468, without the chain arm | 25.9 / 37.9 |
| 13 | 6,747,801,177 (Jay Pantone's W-0094, 6,747,801,195, after one reordering by hand) | 6,747,800,688 (a chain run by hand in about 42 h) | 6,747,801,047 | 32.1 / 47.5 |

### Words foreman found by itself

| n | word | start word | how | hours |
|---|---|---|---|---|
| 12 | **522,736,429** | W-0091 (522,736,503) | case bench12z, arm `expert12` alone (`recipe/RECIPE.md`) | 11.8 (6 threads) |
| 12 | 522,736,428 | the 429 | the next step of the same run (relocate --dpa in `ils12.sh`'s polish) | 11.9 |
| 12 | 522,736,492 | W-0091 | an earlier chain arm (reordering, segment insertion on the card, trailsearch and long loop scans) | 3.1 |
| 9 | 408,717 | W-0099 | `ts` at its top rungs, on W-0099's own selection | 3.9 |

The n = 12 word of 522,736,428 letters that is submitted is not foreman's 428 but one more trailsearch of the 429
outside foreman (the prepublication check of the 429 gave it); the two 428 words differ. The n = 9 408,717 foreman
found is a different word from W-0103 (408,717 on another selection: W-0099's with four square flips): no letter map
or reversal turns one into the other. I have not published it. Where a chain run by hand did
most of the work (the n = 13 start 177 above, made by one reordering by hand from 195), foreman's part is only what
it added afterwards.

## The arms

An arm is one tool with a ladder of settings (rungs). A higher rung gives more time or lifts a cap.

| arm | tool | rungs |
|---|---|---|
| ts | trailsearch | kmax 8, 12, 12 at 3x time, 16 at 6x time, then larger split caps, then gap-1 cuts; T0 0.4 / 0.7 / 1.2 |
| loop | loopscan --greedy --neutral | 40 rounds, 1000, unlimited, then more kinds of loop moves |
| recut | recut --co-skip | one |
| dpa | relocate --dpa | defaults, then --dpa-imax 3 --dpa-theta 4 |
| or3 | segins (n <= 12) | 3 cuts slack 0, 3/1, 5/0, 5/1, then a larger cap |
| gpu_or3 | tools/gpucuts/tsw5g2 --or3-gpu (n >= 11) | 3 cuts slack 0, 3/1, 5/0 |
| cutlns | `wrap/cutlns.sh`: tools/reorder/cutlns2.py, the cut-opening reorder (n 11-13) | weight 4 with K 2, 4, 8; then the nearest weight-3 cuts, 100, 300, 1000 per side; heaviest or random joins |
| rebase | `wrap/rebase.sh`: word2plan onto the case's `alt_bases` (also the relabelled or reversed image) | one, once per base |
| ils | segins_ils | kick depth 1, 2, 3, then deeper kicks with more time |
| wide | recut_wide --wide, loopscan --wide | joins that overlap in up to n - 1 letters; such a word is kept, its plan is not reused |
| longsa | trailsearch, one long hot run | 3 h kmax 12, 6 h kmax 16 |
| expert12 | `wrap/expert12.sh`, a whole chain (n = 12, only when listed in `--arms`) | trailsearch, segment insertion with 3/4/5 cuts, segins_ils, `tools/pipeline/ils12.sh` rounds, recut, repeated to a fixed point |

`expert12` is the chain that shortened W-0091 from 503 to 440 by hand, run as one arm. The other arms fill the gaps
between such chains or replace them where no chain is known.

## How it chooses the next step

* Population: the best plans of the case (3 at n <= 11, 2 at n = 12, 1 at n >= 13). Expensive rungs run only on
  the best plan.
* Candidates: for each plan and arm, the next setting not yet tried on that plan. A setting that gave 0 on a plan
  is never run again on it (the memo). An arm's higher rung opens once its lower rung has started, so the rungs of an
  arm run side by side. Random tools (ts, ils) run each setting with two seeds before a 0 counts.
* Choice: a bandit (discounted UCB) on letters gained per hour of computing (a GPU hour counts as 8 CPU hours);
  untried arms first, cheap rungs first.
* Plateau rule: a ts, ils, or3 or gpu_or3 run that has gained nothing for a share of its time (60 % for ts, 50 % for
  ils, 25 % otherwise; at least 3 minutes) is stopped; nothing is lost because it gained nothing.
* Fixed point: no candidate left on any plan of the population and nothing running. foreman says so and writes a
  line to `SEARCHED.md` with every arm and rung that gave 0.

Resources: at most `--threads` threads (with `--floor F`, foreman shrinks to F threads while other jobs on the
machine keep the cores busy), the GPU for one job and only when no other program uses it, and memory limits per job
that stay below the free memory (`--gb`, `--reserve`).

## Files

| file | what |
|---|---|
| `foreman.py`, `fm.sh` | command line |
| `fm/arms.py` | the arms and their ladders |
| `fm/sched.py` | the choice of the next step and the scheduler |
| `fm/runner.py` | one run: start, watch the log, plateau stop, delcheck, plan store |
| `fm/db.py`, `fm/report.py` | the SQLite state and the report |
| `fm/config.py`, `config.example.json` | paths and limits |
| `fm/winproc.py` | process tree, suspend / resume, memory and CPU load (Windows and Linux) |
| `wrap/` | arms made of several programs: `expert12.sh` (the n = 12 chain), `cutlns.sh`, `rebase.sh`; `gpu_free.sh` (is the card free?) |
| `recipe/` | the steps and plans of the 429 |
