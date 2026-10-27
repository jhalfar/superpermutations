# Plan-making tools

The words of `recipes/` are written by a generator from a unit plan: a list of units (closed trails of the
construction) in an order, each with its opening. The programs here make those plans. They do not touch a word, only the
plan, so they run in minutes to hours on one thread. The construction is Jay Pantone's, the block is mine (proved in
Lean), and the first n = 15 recipe, whose plan idea I lifted from, is Theo H.'s.

All programs are C, standard library only, and build with `gcc -O3 -march=native -o NAME NAME.c` on Linux. Each
includes the generator of the recipe it works on, by a relative path, so build them where they are.

| program | what | includes |
|---|---|---|
| `uopt.c` | relocation search on an n = 14 unit plan (the version I used for the plans before 405) | `recipes/n14/gen14.c` |
| `uopt15.c` | the same search for n = 14 to 15 (`uopt15 L SEL IN OUT [--time S] [--seed S] [--qmin Q] [--seg L] [--win W]`) | `recipes/n15/gen16.c` |
| `lift16.c` | plan for n = 13 + L from the plan one level down, openings chosen by an exact dynamic programme (`lift16 lift L SEL PLAN OUT`) | `recipes/n15/gen16.c` |
| `lift17.c` | the same for n = 17 (L = 5), also for L = 2 to 4; without a block | `recipes/n17/genBt.c` |
| `liftB.c` | construction B: `liftB liftB 4` makes the n = 16 plan with the block from C's n = 15 plan; `liftB lift L` is `lift17` with the block | `recipes/n17/genBt.c` |
| `blockord.c` | the order of the block's units inside one segment, used by `liftB liftB` (`seg1.order` is its result) | `recipes/n17/genBt.c` |

`SEL` is the text of `arrange/data/n12t-selection.txt.xz` (SHA-256 `4f31dab6...2a1a`). For the block, set
`GENB_BLOCK=proofs/lean/constant305989/data/s103_old2_0.txt`. `lift16`, `lift17` and `liftB` write their back pointers to a
file (`LIFT16_BACK`, `LIFT17_BACK`; about 25 GB for n = 16 and up to 180 GB for n = 17), so give them a disk
with room. The plan files of the recipes were written on Windows and have CR LF line ends; the programs read both, and
the unit lines of a rebuilt plan equal the published ones once the CRs are removed.

## Which plan came from what

The plan of n = 14 with 93,904,804,425 letters (in the git history of `recipes/n14/`) came from my n = 13 plan on
selection C, lifted once and then improved by relocation, an exact re-ordering inside groups and the dynamic
programme (the programs for that are `uopt.c` here and two more that are not published; the start is not rebuilt
here). From that plan on, everything below is rebuilt from files of this repository.

**n = 14, 93,904,804,405** (`recipes/n14/`): one run of `uopt15` on the 425 plan.

    git show df98259:recipes/n14/n14_93904804425_on_selC.uplan.xz | xz -dc > n14_425.uplan
    uopt15 2 sel.txt n14_425.uplan n14_405.uplan --qmin 8 --seed 1

It stops when a whole pass finds nothing (45 seconds, 1.2 GB) and prints `LENGTH 93904804405`. The unit lines
are those of the published plan.

**n = 15, 1,401,325,411,491** (`recipes/n15/`): lift the 425 plan, run `uopt15` for 40 minutes, then for 3 hours
more with another seed.

    lift16 lift 3 sel.txt n14_425.uplan n15_lift.uplan                                # LENGTH 1401325415636, 3 minutes
    uopt15 3 sel.txt n15_lift.uplan n15_654.uplan --time 2400 --qmin 8 --seed 1      # my run: 1401325413654
    uopt15 3 sel.txt n15_654.uplan n15_491.uplan --time 10800 --qmin 8 --seed 2      # my run: 1401325411491

`uopt15` stops by the clock, in the middle of a pass, so another run ends at another length. The plan of
`recipes/n15/` is the result of my two runs on 2026-10-26 and 27 (44 passes in the second, 5.8 GB). The n = 15 plan
published first, 1,401,325,413,744 letters from an earlier 40-minute run, is in the git history; the n = 16 and 17
plans below were lifted from it:

    git show df98259:recipes/n15/n15_1401325413744_on_selC.uplan.xz | xz -dc > n15.uplan

**n = 16, 22,320,795,912,621** (`recipes/n16/`): block order, then `liftB` from that n = 15 plan.

    GENB_BLOCK=block.txt blockord sel.txt n15.uplan seg1.order --run 4 --sweeps 1     # cost 1719, 6.5 minutes
    GENB_BLOCK=block.txt LIFTB_ORDER=seg1.order LIFT17_BACK=back liftB liftB 4 sel.txt n15.uplan nB16a.uplan

`seg1.order` here is the file my run wrote. The second command prints `LENGTH 22320795912621`.

**n = 17, 377,961,971,839,096** (`recipes/n17/`): one more lift, from the n = 16 plan.

    GENB_BLOCK=block.txt GEN17_LAZY=2 LIFT17_BACK=back liftB lift 5 sel.txt nB16a.uplan nB17a.uplan

It prints `LENGTH 377961971839096`. My run took 5.1 hours on one thread (18,403 seconds, 55,463,616 units) and 5.1 GB of
memory; the rebuild in the tests below took about as long. `check.sh predict` in `recipes/n17/` recomputes the length of the
result from the plan and the construction.

The C words for n = 16 and n = 17 (no block) come from the same programs without `GENB_BLOCK`:
`lift16 lift 4` gives 22,320,835,819,119 for n = 16.

## Tests of this folder

Run on 2026-10-26 and 27 under WSL (Ubuntu, gcc 13.3), one thread each, from files of this repository (`recipes/`,
`arrange/`, `proofs/lean/constant305989/data/`) and the 425 plan from the git history. "Units identical" means the
unit lines are the same after the CRs and the `#` lines are removed.

| step | result |
|---|---|
| `uopt15 2` on the 425 plan, `--qmin 8 --seed 1` | `LENGTH 93904804405`, 45 s; units identical to `recipes/n14/` |
| `lift16 lift 3` on the 425 plan | `LENGTH 1401325415636`, units identical to the plan my n = 15 search started from |
| `uopt15 3 --time 2400` on that | `LENGTH 1401325413654` (the start of the second run, see above) |
| `lift16 lift 4` on the 744 plan | `LENGTH 22320835819119` (C without the block), 3,511 s, units identical to my earlier n = 16 plan |
| `lift17 lift 4` on the same, no block | same length and units as `lift16`, 1,268 s |
| `blockord --run 4 --sweeps 1` | cost 1719, 399 s; `seg1.order` identical |
| `liftB liftB 4` with `seg1.order` | `LENGTH 22320795912621`, 1,643 s; **units identical to the plan of `recipes/n16/`** |
| `liftB lift 5` on the plan of `recipes/n16/` | `LENGTH 377961971839096`, 18,531 s, 5.1 GB; **units identical to the plan of `recipes/n17/`** |
| `check.sh predict` of `recipes/n17/` | 377,961,971,839,096, the same length, 35 minutes |

The programs also built and ran on Windows (mingw) for the runs that made the published plans; the Linux build needed
the two small compatibility lines at the top of `lift16.c`, `lift17.c` and `liftB.c` (`fseeko64`, `_putenv`) and nothing else.
