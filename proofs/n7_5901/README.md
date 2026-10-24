# L(7) >= 5,901, a computer-assisted proof

A superpermutation on 7 symbols has at least 5,901 letters. The best bound before was L(7) >= 5,900, whose
written proof is [`../lean/n7_5900/PROOF_5900.md`](../lean/n7_5900/PROOF_5900.md); Lean proves L(7) >= 5,899 in
[`../lean/n7/`](../lean/n7/README.md).

This is a computer-assisted proof. It is not a Lean theorem. The written proof is
[`PROOF_5901.md`](PROOF_5901.md). Lean checks the whole reduction: the theorem `covers_5901_of_search` (level 1,
no `native_decide`, axioms `propext`, `Classical.choice` and `Quot.sound`) says that every word containing all
permutations of 7 symbols has at least 5,901 letters if thirty search equations of defect 16 hold, together with
the search equations of 5,899 and 5,900. Six of the thirty are Lean theorems by `native_decide`. The other
twenty-four rest on searches run by C, C++ and CUDA programs of mine; most of them were run by one program only.
State of 2026-10-24.

## Trust table

One row for each of the thirty search equations of defect 16: the eleven fields of `K16.Evals` (K0 to K10) and
the nineteen fields of `J16.Evals` (the eighteen counted joint runs of Table C and the ring search RX). "kept" is
the number of kept prefixes of the card run (for RX of the three CPU programs). The levels:

- "Lean + two independent programs": the Lean equation is proved by `native_decide`, and two programs that share
  no code (the card program and a second program written from the texts) gave the same counts;
- "two independent programs": no Lean equation yet, two programs with equal counts that share no code;
- "one program, repeated by a program that shares code": a second run with equal counts, but the two programs
  share the code of the rules;
- "one program": one run of one card program.

| search | Lean field | statement | kept | trust |
|---|---|---|---:|---|
| K0 | `k0` | F(0; 65, 96), Rule JS | 497,079,750,869,693 | one program |
| K1 | `k1` | F(1; 55, 90), Rule JS | 755,070,879,353,479 | one program |
| K2 | `k2` | F(2; 51, 84), Rule JS | 375,408,252,302,475 | one program |
| K3 | `k3` | F(3; 48, 78) | 527,651,578,348,368 | one program |
| K4 | `k4` | F(4; 41, 72) | 160,141,566,085,840 | one program |
| K5 | `k5` | F(5; 37, 66) | 23,993,915,746,406 | one program |
| K6 | `k6` | F(6; 37, 60) | 2,569,985,903,558 | one program (the Lean equation is being evaluated, 1 of 16 files done) |
| K7 | `k7` | F(7; 35, 54) | 320,243,136,927 | Lean + two independent programs (see the note below the table) |
| K8 | `k8` | F(8; 35, 48) | 22,732,567,392 | Lean + two independent programs |
| K9 | `k9` | F(9; 35, 42) | 384,081,983 | Lean + two independent programs |
| K10 | `k10` | F(10; 35, 36) | 172,577 | Lean + two independent programs |
| T1 | `t1` | J(S7 S7; 50, 84; 1) | 432,156,242,209,710 | one program |
| T2 8..15 | `t2a` | J(R S7; 46, 89; 1), rings 8..15 | 101,123,384,635,543 | one program |
| T2 16..23 | `t2b` | rings 16..23 | 129,493,336,379,997 | one program |
| T2 24..31 | `t2c` | rings 24..31 | 135,483,427,600,468 | one program |
| T2 32..39 upper | `t2d` | rings 32..39, value >= 17 | 151,457,803,584 | one program |
| T2 32..39 lower | `t2e` | rings 32..39, value <= 16 | 817,008,248,719 | one program |
| T2 40..47 upper | `t2f` | rings 40..47, value >= 20 | 91,979,996,005 | one program |
| T2 40..47 lower | `t2g` | rings 40..47, value <= 19 | 284,267,038,527 | one program |
| T2 48..55 upper | `t2h` | rings 48..55, value >= 23 | 71,260,814,984 | one program, repeated by a program that shares code |
| T2 48..55 lower | `t2i` | rings 48..55, value <= 22 | 174,112,070,351 | one program, repeated by a program that shares code |
| T2 56..89 | `t2j` | rings 56..89 | 28,953,480,015,964 | one program |
| T3' | `t3` | J(R S5 R; 52, 82; 2), rings >= 8 holes | 40,196,474,735,125 | one program |
| T4' | `t4` | J(R S4 S4; 56, 77; 2), rings >= 8 holes | 1,479,145,818,172 | one program |
| T5 | `t5` | J(S3 S3 S3; 60, 72; 2) | 52,379,362,069,149 | one program |
| T6' | `t6` | J(S2 R R R; 58, 75; 3), rings >= 8 holes | 112,728,682,360 | one program (a run of the same program with the rule ORDS, not counted, also found nothing) |
| T7 | `t7` | J(S1 S1 R R; 62, 70; 3) | 1,432,335,917,907 | two independent programs |
| T8 | `t8` | J(S0 S0 S0 R; 66, 65; 2) | 7,126,584,865 | Lean + two independent programs |
| T9' | `t9` | J(S0 R R R R; 64, 68; 4), rings >= 8 holes | 11,105,597 | Lean + two independent programs |
| RX | `rx` | the exact ring row to 63 holes | 1,588,850,620 | three independent programs |

K7 is evaluated as four `native_decide` theorems, one for each quarter of its 64 parts
([`lean/Audit5901/NK7_0.lean`](lean/Audit5901/NK7_0.lean) to `NK7_3.lean`). The short step that puts them
together into the field `k7` (a case split on the part number) is not yet in a compiled file. For K10, K9, K8,
T9' and T8 that step is compiled ([`lean/Audit5901/NEv.lean`](lean/Audit5901/NEv.lean)).

The independent second programs are the second programs of defect 15, written from the texts only:
[`programs/second/k2_s12.cpp`](programs/second/k2_s12.cpp) for K7 to K10 and
[`programs/second/j2_np5.cpp`](programs/second/j2_np5.cpp) for T7, T8 and T9'. The Lean engines count as a third
implementation; on K10, K9, K8, T9' and T8 their counting copies give the counts of the table as well. The
trust levels are explained in [`PROOF_5901.md`](PROOF_5901.md), section 0.4, and the state of each search in
section 7.2.

The proof also rests on things that are not searches of defect 16. The accounting, the cut of a component, the
search rules and the completeness of the engines are proved on paper in `PROOF_5901.md` and in Lean at level 1.
The tables of defect 15 come from [W] (the 5,900 proof), where every statement had two programs that share no
code. The knapsack of section 2.8 was checked by two programs that share no code, and Lean replaces it at level
1 by closed checks.

## How the proof goes

As for 5,900, the exact model turns the bound into a statement about configurations: none has cost at most 136
(defect at most 16). A configuration of that cost gives pieces with total value at least 40 within weight 96. A
finite enumeration over the table of defect 15 leaves 131,436 piece profiles in 20 shapes. Each shape is
excluded by one statement: the kernel alone (K0 to K10, which give a table D16 for sequences of value at most 39)
or one of nine joint statements T1 to T9, the joint ones only for rings with at least 8 holes. The statements
are searched exhaustively with search rules that the defect-15 search did not have (the reversal cut on one
piece, the order of pieces of equal kind, windows of ring holes split by the value of the ring, and Rule JS for
the kernel); sections 3 and 4 prove that each rule keeps a counterexample if there is one. The searches took
about 5.0e15 start vertices for the joint statements and 2.3e15 kept prefixes for the kernel.

## Files

| path | what |
|---|---|
| `PROOF_5901.md` | the written proof |
| `REFEREE_NOTES.md` | my last referee pass over the written proof: what I compared, the discrepancies I found, and the points of my list of open questions |
| `table/TABLE_C16.md` | Table C, the table of the card runs (state of 2026-10-18) |
| `table/capD.txt` | table D, read by every joint run |
| `table/capD_r.txt` | D with the exact ring row RX on 0 to 63 holes (upper halves of the split of T2) |
| `table/lo_32_39_a17.txt`, `lo_40_47_a20.txt`, `capD_r_rv22.txt` | the lowered ring rows of the lower halves of the split of T2 |
| `table/capD16_k.txt`, `capD16u_5_k.txt` to `capD16u_10_k.txt` | the tables of the kernel statements |
| `programs/gk4/` | the kernel-alone search on the card (K3 to K10): host `gk4.c`, kernel `gk5.cu`, part scripts |
| `programs/gkjs/` | the same with Rule JS (K0, K1, K2); `mkgkjs.py` is the diff against `gk4` |
| `programs/gj2/` | the joint search on the card (T1, T2, T3', T4', T6', T9', repeats of T7 and T8); `jr5.c` is a CPU reference |
| `programs/gj3/` | `gj2` with the switch RVMIN (upper halves of T2) |
| `programs/gj/` | the first card program of the joint search (T5, T7, T8) |
| `programs/jr/` | the CPU references of the joint rules (`jr.c`, `jr6.c`), which share the rule code with the card hosts |
| `programs/second/` | the independent second programs `k2_s12.cpp` and `j2_np5.cpp` |
| `programs/rx/` | two of the three programs of RX (`ringx.c`, `ringchk.c`), the 60 witnesses and their checker |
| `programs/knapsack/` | the knapsack by pieces (`knap16.py`) and by items (`acc16.py`, `tabs15.py`), with their logs |
| `audit/partaudit.py`, `audit/partaudit.txt` | the audit of every part file of Table C and its output |
| `audit/second/` | the outputs of the second counts of K10, K9, K8, T9' and T8 |
| `audit/k7second/`, `audit/t7second/` | the second counts of K7 and T7 in parts: scripts, part files, logs |
| `audit/records/` | the part files of the single-part runs K7 and K10 and the stored headers of K8 and K9 |
| `lean/Audit5901/` | the `native_decide` theorems of the evaluated equations (`NK.lean`, `NJ.lean`, `NK7_*.lean`, `NK6_*.lean`), their assembly into fields (`NEv.lean`) and the counting copy of the joint engine (`J16Count.lean`) |
| `lean/Eval/`, `lean/logs/` | the `#eval` runs and the logs of every evaluation, with the `#print axioms` lines |
| `lean/*.sh`, `gen_nk.py`, `nk_order*.txt`, `nk_queue.log` | the build and run scripts, the generator of the K7 and K6 files and the queue log |
| `SHA256SUMS` | SHA-256 of every file of this folder |

The scripts and logs come from my working tree. Where a comment named a file of the research repository I
replaced it by its path here or by "not in this repository". The run scripts change into their own folder;
the Lean scripts of `lean/` take the toolchain and the level-1 build from the variables `LEAN_TOOLCHAIN` and
`LEVEL1`; the Windows batch files name the CUDA and Visual Studio tools where I had them. The logs record the
paths of the runs as they were. The part files of the card runs (about 8,700 small files) are not here;
`audit/partaudit.txt` records what they contain.

The level-1 Lean sources are not in this folder. They are in [`../lean/n7_5901/`](../lean/n7_5901/README.md):
the modules of defect 16 that `LowerBounds/F5901Search.lean` imports, the counting copies `PCount.lean` and
`K16Count.lean`, and kernel tests; `sources.sha256` there lists their hashes, and its `build.sh` builds them.

The files of `lean/` compile against these modules and load the C code of the engines with `--load-dynlib`, as
the level-2 modules of 5,899 and 5,900 do; `lean/build.sh`, `nat.sh` and `nat2.sh` are the scripts I used (with `LEVEL1` pointing at a build of
`proofs/lean`).

## How to check

- The numbers of Table C against the part files: `audit/partaudit.txt` (method in `PROOF_5901.md` 6.3). Every tag
  has all its parts and one statement line, nothing was found, and every sum equals Table C.
- The commands of every run and what their output looks like: `PROOF_5901.md` 6.2 and 6.3. The programs and
  their sources: 6.1.
- The second counts: the files of `audit/second/`, `audit/k7second/summary.txt` and the eight part files of
  `audit/t7second/parts/` (6.2 says how the T7 parts add up).
- The Lean evaluations: `lean/logs/*.log`, which end with the `#print axioms` lines; `PROOF_5901.md` 0.4.
- The tests of the programs and of the rules against brute force on 5 and 6 symbols: `PROOF_5901.md` 6.4.
- The second programs build with any C++17 compiler (`g++ -O2 -std=c++17 -o j2_np5 programs/second/j2_np5.cpp`);
  the card programs need CUDA (`programs/gkjs/build_ptx.bat` has the `nvcc` line; the kernel of `gk4` is
  built with `-DLEARN=1 -DRC=1 -DNR=3 -DLL=6`).

## What is missing

Section 7 of `PROOF_5901.md`. In short: twenty of the thirty searches (K0 to K6, T1, T3', T4', T5, T6' and eight of the
ten runs of T2) have one program only, and T2 48..55 has a second run that shares code. Twenty-four Lean
equations are not evaluated. K6 is running (about 60 hours from 2026-10-24 03:26); the others are out of reach
of the Lean engines at their present speed, or would take up to a day each on 28 threads (T4', T6', T7 and the
six halves of the split of T2). For K7 the step from its four theorems to the field is not yet compiled.

## Credits

The transform that cuts a path through all permutations into components is Zach Hunter and Uku Raudvere's. The
chains of a component and the lemmas about them are Xiaolong Liu's. The bound 5,898 is Justin Lebar's; nothing of
his proof is used here. The model of standard configurations, the proofs of 5,899 and 5,900, the accounting, the
search rules and the programs of defect 16 are mine.
