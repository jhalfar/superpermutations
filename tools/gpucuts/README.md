# Segment insertion with the judging on the card

`tsw5g2.c` is the segment-insertion program that ran the GPU passes behind my n = 12 and n = 13 words of November
2026, and `orx.sh` is the script that ran it: one setting after another, each from the best plan so far, with every
word checked by `delcheck`.

| file | what it is |
|---|---|
| `tsw5g2.c` | segment insertion with three to six cuts; the exact gain of every candidate is computed on an NVIDIA card (`--or3-gpu`) |
| `orkern.cu` | its kernel: one thread block per candidate, the same computation as `o3_gain` on the host |
| `orx.sh` | passes with several settings in a row; keeps the best plan and only the best word |

## What it does

A move cuts the sequence of pieces at three to six joins and puts the blocks between the cuts together in another
order, none of them reversed. With three cuts two neighbouring blocks of any length change places. Candidates come
from tables that say what every join is worth when the cuts on both sides may change (a chain search as in the
method of Lin and Kernighan), and each candidate is then judged exactly, with the best cuts of the whole new
sequence. A round takes all shorter moves that do not disturb each other. The tables, the exact values of joins and
the gains of judged candidates are kept from round to round and brought up to date where the moves changed them.

`tsw5g2.c` is an earlier state of [`segins_gpu.c`](../segins_gpu.c): the same segment insertion, with the first
version of the judging on the card. `segins_gpu.c` has a later kernel (`segins_kern.cu`) and three things this one
lacks: moves of equal length (`--or3-eq`), the candidates of a round kept in bounded memory, and cuts at vertices
only. I publish this copy because it is the program the passes of my logs ran. Without `--or3-gpu`, or when
`orkern.ptx` is not found, it judges on the processor and says so in one line of the log.

## Building

    gcc -O2 -mpopcnt -fopenmp -o tsw5g2 tsw5g2.c -lm          # on Linux add -ldl
    nvcc -arch=sm_120 -ptx -o orkern.ptx orkern.cu

The program loads the CUDA driver library at run time (`nvcuda.dll` or `libcuda.so.1`), so the toolkit is needed
only to make the PTX. It looks for `orkern.ptx` next to the program, then in the current directory; `--or3-gpu-ptx
FILE` names it. `sm_120` is the only architecture I tested. With CUDA 13.4 the PTX built from this file is byte for
byte the one my runs loaded. gcc 13.2 (MinGW) compiles `tsw5g2.c` without a warning.

## Running it on one word

It needs a base word and a plan of the word on it (see [the tools README](../README.md)). If you only have the
word, `word2plan` writes the plan:

    word2plan BASE.txt WORD.txt w.plan
    tsw5g2 BASE.txt out.txt --plan-in w.plan --time 0 --threads 6 --or3 3 --or3-slack 0 \
           --or3-maxcand 200000 --or3-gpu --or3-sec 2400 --or3-stop STOP

It writes `out.txt` and `out.txt.plan`, and the plan after every round that made the word shorter, so a run that
stops early leaves its best plan. Then check the word with `delcheck`. `orx.sh` does all this for a list of
settings:

    BASE=BASE.txt TOOLS=bin MAXCAND=200000 bash tools/gpucuts/orx.sh DIR w.plan LENGTH \
        "--or3 3 --or3-slack 0 --or3-gpu|--or3 5 --or3-slack 1 --or3-long 1000 --or3-gpu" 2400 6

`DIR/steps.log` has one line per setting and `DIR/best.txt` the length, plan and word of the best one. `TOOLS` is the
directory that holds `tsw5g2`, `orkern.ptx` and `delcheck`; `TSW` replaces the program, for example by a memory
guard in front of it (`tools/pipeline/tswg.sh`). `touch DIR/STOP` ends the running pass cleanly. If a pass dies
after a round wrote its plan, the script rebuilds the word of that plan and goes on.

## The options

| option | meaning |
|---|---|
| `--or3 C` | cut at 3 to C joins (C at most 6) |
| `--or3-slack S` | a candidate may be worth up to S letters less than the joins it replaces by the tables (default 2); a filter, not a bound: larger values find more and cost much more |
| `--or3-v TH` | list every pair of events whose join is worth at most TH (default 6) |
| `--or3-x T` | also list the pairs across expensive joins, those worth T or more (default 3) |
| `--or3-long Z` | a candidate with Z events or more between all its cuts gains exactly its estimate, so it is judged only if the estimate is 1 or more |
| `--or3-maxcand M` | judge the candidates M at a time, best estimate first (default: all at once; `orx.sh` passes 3000 unless `MAXCAND` says otherwise; with the card I used 200000) |
| `--or3-gpu` | judge on the card; `--or3-gpu-check` judges on both and compares, `--or3-gpu-checkmax K` stops comparing after K |
| `--or3-sec SEC`, `--or3-stop FILE`, `--or3-rounds R` | end the pass cleanly; the word is written |

The settings I ran:

    --or3 3 --or3-slack 0 --or3-gpu                     # the pass inside the n = 12 and n = 13 loops
    --or3 4 --or3-v 5 --or3-x 4 --or3-gpu               # four cuts with narrower pair lists
    --or3 5 --or3-slack 0 --or3-long 600 --or3-gpu      # five cuts
    --or3 5 --or3-slack 1 --or3-long 1000 --or3-gpu     # five cuts, wider

`--or3 4` without narrower lists is a flood of candidates at n = 13. The same options work in `segins_gpu`.

## Measurements

At n = 13 with five cuts and slack 1 (`--or3-long 1000 --or3-maxcand 200000 --or3-gpu --or3-gpu-check
--or3-gpu-checkmax 600`, 8 host threads): 482,343,928 cuts loaded in 2.1 s, 6.3 GB on the card (8.0 GB with the
context), 12.2 GB working set and 18.4 GB committed on the host. The check of the first batch judged 1,360 candidates
and 4,161 join values on both, with no mismatch. Round 1 took 158 s (tables 50 s, chain search 16 s), rounds 2 to 9
took 41 to 54 s each, and the word went from 6,747,916,693 to 6,747,916,657 in 901 s with loading; it passes
`delcheck`. On the processor the same setting took several minutes a round. Five cuts at n = 13 can peak at about
19 GB on the host.

At n = 12 with three cuts and slack 0 on 4 threads: 14.5 million moves found in 8 s, round 1 in 35 s (48 moves, 229
letters), 1.9 GB working set.

With the same kernel in an earlier program, judging on the card took a round of five cuts with slack 1 at n = 12
from 142 s on 4 threads of the processor to 36 s with the card and the same 4 threads, of which the judging itself
was under a second; the rest is the
tables and the chain search, which stay on the host. A search running on the same card dropped to 28 % of its speed
while the judging ran.
