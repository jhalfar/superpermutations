# A lower bound for n = 7 in Lean: 5,899

A word over 7 symbols that contains every permutation of the 7 symbols as a contiguous part has at least
5,899 letters. With the word of 5,905 letters that `../words` checks, 5,899 <= L(7) <= 5,905.

The proof has two levels, and they do not rest on the same things.

* Level 1 is checked by the Lean kernel and depends on the axioms `propext`, `Classical.choice` and
  `Quot.sound` only. It proves the bound from twelve finite statements about rows of blocks on 7 symbols, and
  it proves each finite statement from an equation that says "this search returns `false`". The search is a
  function defined in Lean, and the proof that its answer means what is claimed is part of level 1.
* Level 2 evaluates the searches. They visit 1.10 * 10^11 nodes, which is out of reach for the kernel, so
  they are run as compiled code by `native_decide`. This is the one place in this package where compiled
  code is trusted. The final theorem depends on the three axioms above and on 22 more, one for each
  evaluated equation, and `#print axioms` names them.

Justin Lebar's Lean proof of 5,898 (github.com/jlebar/superperm7-ge-5898) has the same footing: its README
says that its trust base includes Lean's compiler and native evaluator, with 380 evaluation certificates of
`native_decide` for the main theorem. His proof is not used here.

## The statement

The statements are copied from the Lean files with the symbols spelled in ASCII (`forall`, `exists`, `<=`,
`->`, `/\`, `Nat`, `Not`) and the indices of variables written on the line (`n0` for the `n` with index 0).
`Covers` is the definition of Jay Pantone's `Challenge.lean`: every list of k different letters occurs in
the word as a contiguous part.

```lean
-- Audit5899Native.lean: the theorem, with no definition of this project                      (level 2)
example : forall w : List (Fin 7),
    (forall p : List (Fin 7), p.length = 7 -> p.Nodup -> exists u v : List (Fin 7), w = u ++ p ++ v) ->
    5899 <= w.length

-- LowerBounds/PFinalNative.lean                          (namespace SuperpermLowerBounds; level 2)
theorem covers_lower_bound_7_native : forall w : List (Fin 7), Covers w -> 5899 <= w.length

-- LowerBounds/PTheorem.lean: from the finite statements                                      (level 1)
theorem no_config_134 (hC : Caps) (hF : Profiles) (c : NConfig 7) (hv : c.Valid) : Not (c.cost <= 134)
theorem covers_5899_of_caps (hC : Caps) (hF : Profiles) :
    forall w : List (Fin 7), Covers w -> 5899 <= w.length

-- LowerBounds/PFinal.lean: from twelve search equations                                      (level 1)
def PS.Covered (nt : Nat) (f : Nat -> Nat -> Bool) : Prop :=
  forall tp, tp < nt -> exists pa pb, pa <= tp /\ tp < pb /\ f pa pb = false
theorem covers_5899_of_search (hn0 : 0 < n0) (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3) (hn4 : 0 < n4)
    (hn5 : 0 < n5) (hnR : 0 < nR) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc) (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n0 (PS.seqSearch 7 Ptabs 0 0 84 f0 d0 n0))
    (h1 : PS.Covered n1 (PS.seqSearch 7 Ptabs 1 0 78 f1 d1 n1))
    (h2 : PS.Covered n2 (PS.seqSearch 7 Ptabs 2 0 72 f2 d2 n2))
    (h3 : PS.Covered n3 (PS.seqSearch 7 Ptabs 3 0 66 f3 d3 n3))
    (h4 : PS.Covered n4 (PS.seqSearch 7 Ptabs 4 0 60 f4 d4 n4))
    (h5 : PS.Covered n5 (PS.seqSearch 7 Ptabs 5 0 54 f5 d5 n5))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne)) :
    forall w : List (Fin 7), Covers w -> 5899 <= w.length

-- LowerBounds/NTheorem.lean, NUpper.lean: the model, for every k                             (level 1)
theorem covers_length_gt_of_no_stdConfig (hk : 5 <= k) (D : Nat)
    (h : forall c : NConfig k, c.Valid -> Not (c.cost <= (k - 2).factorial + D)) :
    forall w : List (Fin k), Covers w -> hpv k + D + 1 <= w.length
theorem no_stdConfig_iff (hk : 5 <= k) (D : Nat) :
    (forall c : NConfig k, c.Valid -> Not (c.cost <= (k - 2).factorial + D)) <->
      forall w : List (Fin k), Covers w -> hpv k + D + 1 <= w.length
```

`hpv k` is k! + (k-1)! + (k-2)! + k - 3, as in `../lower`; hpv 7 = 5,884. `Caps` and `Profiles` are the twelve
finite statements, listed below. `PS.Covered nt f` says that a search cut into `nt` parts has been evaluated
in ranges of parts that together contain every part; the arguments `f`, `d` and `n` of a search are its
fuel, the depth at which it is cut and the number of its parts, and the theorem holds for all of them.
`Audit5899.lean` writes the finite statements out and `AuditN.lean` the model. `Audit5899Search.lean` states
level 1 with twelve plain equations as hypotheses.

## What each level trusts

Level 1: the Lean kernel, the three axioms, the definition `Covers` of `Challenge.lean` and the lemmas of
the Hunter-Raudvere library and of Xiaolong Liu's library, which are compiled here from their sources like
everything else. Nothing of level 1 imports a file that uses `native_decide`.

Level 2 adds, for the 22 equations and for nothing else:

* the Lean compiler, which turns `LowerBounds/PSearch.lean` into C;
* the C compiler of the Lean toolchain (`leanc`, which is clang), which turns that C file into a shared
  library;
* the Lean runtime that the library runs on: natural numbers, arrays, byte arrays and tasks;
* that the library which Lean loads when it evaluates an equation is the one built from `PSearch.lean`.
  `build.sh` builds it in the same run and ties it to the hash of the source, but Lean itself does not
  check this.

`native_decide` records each result as an axiom named after the equation,
`SuperpermLowerBounds.PS.f0_0._native.native_decide.ax_1_1` and so on. The 22 equations are in the 17 files
`LowerBounds/P*Native.lean` and in `evaluations.txt`. `build.sh full` fails unless the axioms of
`covers_lower_bound_7_native` are exactly the three standard ones and these 22.

Not trusted at either level: the tables of `LowerBounds/PTables.lean`, the programs outside Lean that found
their numbers and the node counts in this README. A table entry that is too small makes a search return
`true` or an arithmetic check fail, and then the build fails.

## Whose the parts are

* The transform that cuts a path through all permutations into components is Zach Hunter and Uku
  Raudvere's (github.com/urdvr/superpermutations-hunter).
* The pieces and chains of a component, and the lemmas about them, are those of Xiaolong Liu's
  preimage-chain library (github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds). Both
  libraries are used unchanged.
* The previous bound, 5,898, is Justin Lebar's. Nothing of his proof is used. The first 57 entries of the
  table of chains below (0 to 56 holes) agree with the table that his README prints.
* The model of standard configurations with the proof that it is exact, the reductions of components to
  sequences and rings, the knapsack, the search and the proof that the search is complete are new.

## How the proof goes

A block is a permutation followed by its 6 rotations, entered at one of them. A row is a sequence of
1 to 6 blocks joined by steps of weight 2; a row with l blocks has 6 - l holes. Rows follow each other at
seams, and a seam has weight at least 3. A chain is a sequence of rows whose seams all have weight exactly
3 and whose blocks lie in pairwise different rotation classes. This is the model chain of `../lower`
(`IsModelChain`), where a row is called a piece and its holes its deficit.

1. The exact model (`NConfig`, `NCore`, `NPath`, `NTheorem`, `NRules`, `NBlock`, `NT4`, `NT4Config`,
   `NUpper`, with `JLinks`, `JEntryTree`, `JCoverage`, `DCapacity`, `DJunction` for the junctions between
   components). A standard configuration is a kernel, which is a sequence of rows, and hanging components,
   each a sequence of rows attached at one vertex. It is valid if every rotation class is a block exactly
   once; the seams have weight at least 3; the two attachment weights w0 and w1 of every hanging component
   are at least 2; the attachment vertices are pairwise different and obey a slot rule; the attachments
   lead back to the kernel. Its cost is the number of rows, plus the weight less 3 for every seam, plus
   w0 + w1 - 4 for every hanging component. For k >= 5 every word that contains all permutations gives a
   valid configuration c with hpv(k) + cost(c) <= (k-2)! + length, and for k >= 3 a valid configuration of
   cost (k-2)! + D gives such a word of exactly hpv(k) + D letters. So the model loses nothing
   (`no_stdConfig_iff`), and for k = 7 the theorem is: no valid configuration has cost at most
   5! + 14 = 134.
2. The accounting (`PTrails`). For a component with m rows, h holes, seam excess X (the weight less 3,
   summed over its seams) and attachment cost a, put value v = m - (h + 5 (X + a)) and weight
   w = h + 6 (X + a). The
   blocks cover the 720 rotation classes, so 6 (rows) - (holes) >= 720, and cost <= 134 gives: the values
   add up to at least 50 and the weights to at most 84.
3. The cut at heavy seams (`PTrails`, `PGeom`). A seam of weight at least 4 is heavy. Cut at its heavy seams,
   a component falls into chains. The Lean files call these chains trails.
4. No waste (`PFamily`, `PArith`). From the table of chains (F0 below), two arithmetic statements and the
   five profile statements (FF): in a configuration of cost at most 134 every heavy seam has weight exactly
   4, every attachment costs 0 or 1 and no component has more than 5 heavy seams.
5. The reductions (`PJunction`, `PGlue`, `PShapes`, `PHanging`). Every component is turned into one object
   of three kinds: a sequence with s links, which is s + 1 chains joined by s links of weight 4; a ring,
   which is a chain of at least two rows whose last block links to its first with weight 3; or something
   of value at most 0. The kernel with j heavy seams is a sequence with j links. A hanging component with
   attachment cost 1 can have its last or its first row extended by one block, the class of the attachment
   vertex: it then has one hole less and closes with weight 3, so it is a ring if it has no heavy seam, and
   cut at one heavy seam it is a sequence with j - 1 links. In a hanging component with attachment cost 0
   the last and the first row merge through one more block into a single row, which removes one row and 7
   holes: with j >= 1 heavy seams this gives a sequence with j - 1 links, without heavy seams and with at
   least three rows a ring. What is left has value at most 0: a component with attachment cost 0, no heavy
   seam and one or two rows, and a component with attachment cost 1 and a single row.
6. The knapsack (`PArith`, `PTheorem`). With the tables M for chains, P_1 to P_5 for sequences with 1 to 5
   links and PR for rings, the value of every hanging component is at most the value of an item of its
   weight. Let HB(W) be the best total value of items within weight W, and P_0 = M. One inequality between
   table entries, for 0 <= s <= 5 and 0 <= x <= 84 - 6s,

       P_s(x) - (x + 5s) + HB(84 - (x + 6s)) <= 49

   bounds the sum of all values by 49. That contradicts step 2. The arithmetic of steps 4 and 6 is
   checked by `decide +kernel` against helper tables that are part of `PTables.lean`.

The twelve finite statements, all about rows on 7 symbols with pairwise different rotation classes:

| | statement | table | kept prefixes of its search |
|---|---|---|---|
| F0 | a chain with x <= 84 holes has at most M(x) rows | 85 entries | 90,373,570,810 |
| F1 | a sequence with exactly 1 link and x <= 78 holes has at most P_1(x) rows | 79 | 15,136,651,976 |
| F2 | the same with 2 links and x <= 72 | 73 | 3,553,547,989 |
| F3 | the same with 3 links and x <= 66 | 67 | 783,012,378 |
| F4 | the same with 4 links and x <= 60 | 61 | 4,289,217 |
| F5 | the same with 5 links and x <= 54 | 55 | 102,853 |
| FR | a ring with x <= 77 holes has at most PR(x) rows | 78 | 460,113,709 |
| FF | no pairwise disjoint chains with (rows at least, holes at most) = (66, 36), (66, 36) | | 108,741 |
| | the same for (50, 26), (50, 26) | | 27,110 |
| | (63, 34), (34, 16) | | 54,979 |
| | (66, 36), (31, 14) | | 103,034 |
| | (31, 14), (31, 14), (34, 16), (34, 16) | | 405,173 |

A kept prefix is a list of rows whose continuations the search tries. The counts are those of a C program
written from the same rules; a copy of the Lean search that counts gave the same numbers for FF, F5, F4, F3
and FR. Neither program is in this package. The sum is 110,311,987,969.

The search (`PSearch`, 318 lines, no imports) is one depth-first search over lists of rows that begin at
the word 1 2 ... 7. A row is followed by a row that starts at one of the 5 words its exit overlaps with
weight 3, or, where the rule allows it, at one of the 23 with weight 4 or at any entry of an unused class.
The rule is a pair of Boolean functions of the numbers of rows, holes and links so far. That the answer
`false` proves the finite statement is shown in three steps:

* `PSound`, `PSeq`, `PEnc`: the search visits every list of rows all of whose prefixes the rule keeps, for
  every set of tables that satisfies the conditions `PS.Enc`, and both sets of tables in `PSearch` satisfy
  them. One set computes with the codes of words and is small enough for the kernel; the other reads
  everything from tables built at the start and is the one that is compiled.
* `PLevels`: the three rules keep enough. For F0 to F5 take a counterexample with the fewest rows and cut
  it after any row: both parts obey the tables, which bounds the rows of the first part from below, and
  the rule keeps exactly the prefixes that pass this test. For FR a ring may be read from any of its rows,
  and by the cycle lemma one reading has, after every i rows, at most the share i/T of the holes. For FF
  each chain is cut to the required number of rows and the next one starts at any unused class.
* `PRules`, `PFinal`: chains, sequences and rings of the model are such lists of rows, and all of them can
  be relabelled to begin at 1 2 ... 7.

F0 is one search cut at depth 14 into 5,039 parts, evaluated in ten ranges of parts, one file each; F1 is
evaluated in two ranges. That makes 22 equations in 17 files.

Tests of the engine that are part of the build: `PSmallSearch` and `PSmall` evaluate nine searches on 5
symbols in the kernel and derive the finite statements on 5 symbols from them by the same theorems;
`PSmall6Search` evaluates one search on 6 symbols in the kernel; `PTestNative` runs the nine searches again
as compiled code with both sets of tables, and nine searches on 6 and 7 symbols with known answers, among
them tables lowered by one, where the search has to return `true`.

## The files

* `LowerBounds/`: 56 Lean files, described one by one in `../MANIFEST.md`. `N*`, `J*`, `D*` are the model;
  `P*` without `Native` in the name are level 1 and the tests; the 17 files `P*Native.lean` except
  `PTestNative` are the evaluations, and `PFinalNative.lean` is the theorem of level 2.
  The final theorem also imports 17 files of `../lower/LowerBounds` and the bridge of `../words`.
* `Audit5899.lean`, `Audit5899Search.lean`, `Audit5899Native.lean`, `AuditN.lean`: the statements written out.
* `evaluations.txt`: the evaluation modules with their level and their equations.
* `sources.sha256`: the hashes of the 79 Lean files of this package that the theorem is compiled from.
* `build.sh`.

The Lean files are the files of my working directory, unchanged but for one comment line of `AuditN.lean`
and the line ends of 13 files.
Their comments name notes and scripts that are not in this package: `PROOF_5899.md` (the proof on paper;
the section above follows it), `MODEL.md`, `PROOFS_JOINT.md` and `PROOFS_PRICE.md` (the papers behind the
model and the junctions), `scratchP/pproto.c` (the C program of the node counts), `p_native_build.sh` and
`build/native/PSearch.dll` (here: step 2 of `build.sh` and the library in the build directory).

`PTables.lean` is data. Its first three definitions are the tables M, P_1 to P_5 and PR; the other four are
helper tables for the arithmetic, computed from the first three by dynamic programming. The numbers of the
first three were found by searches outside Lean, written in C and Rust: for up to 58 holes M is the largest
number of rows those searches found, and above that the entries are upper bounds, from 62 holes on the
weakest that the arithmetic allows. Only upper bounds are proven here; nothing says that a table is
attained.

## Building

`build.sh` works in the build directory of `../words/build.sh` and `../lower/build.sh` and compiles only
what is missing there. It uses their sources, not their results: the modules of the two libraries, the
bridge and the 17 files of `../lower` that they have not compiled it compiles itself. I ran it after the
two. `../README.md` says how to fetch what a build needs; besides that this part needs `leanc`, which comes
with the Lean toolchain.

```sh
JOBS=8 ./build.sh          # the default level: everything but the 13 long evaluations
JOBS=8 ./build.sh full     # all 17 evaluations, the theorem, its audit
```

The steps, with the settings, are at the top of the script. In short: it compares the sources with
`sources.sha256` and the lists of the two libraries; compiles `PSearch.lean` to C and makes the shared
library with `leanc -shared -O3`; compiles level 1, the proof that the engine is complete and the kernel
tests; runs `PTestNative` and the evaluations, each as one Lean process that loads the library with
`--load-dynlib`; at the level `full` compiles `PFinalNative` and `Audit5899Native`; prints the axioms and
checks them as said above. `JOBS` is the number of threads of the evaluations, all processes together: the
parts of a search are uneven, so the script starts the next module when the running ones leave threads
idle. A finished module is not run again, so the build can be stopped and continued.

Everything here was run on Windows 11 under Git Bash, where the library is `PSearch.dll`. The script has
a branch for Linux (`PSearch.so`, compiled with `-fPIC`) and one for macOS (`PSearch.dylib`). I have run
neither of them.

The C file that Lean 4.31.0 writes from `PSearch.lean` has SHA-256
`55c277e717ac6d6e451577ec3d7be49e138d87f978dc0d502cbd7e672da659a0` in each of my builds; the script prints
it. The library is not the same file from build to build.

## What it costs

Measured on my machine (Ryzen 9 5950X with 16 cores, 32 GB, Windows 11 with Git Bash) on 7 October 2026, in
one run into an empty build directory: `../words/build.sh lower`, then `../lower/build.sh`, then
`JOBS=8 MINFREE_GB=6 MINFREE_BIG_GB=12 ./build.sh full`, with one Lean process at a time outside the
evaluations. In four samples taken during the run, other jobs kept 9 to 16 of the 32 threads busy.

| step of `build.sh full` | modules | Lean time | by the clock | largest working set |
|---|---|---|---|---|
| 2: `PSearch` to C, then `leanc` | 1 | 2 s and 2 s | | |
| 3: the model, `N*`, `J*`, `D*`, `AuditN` | 17 | 387 s | | 3.5 GB |
| 3: level 1, `PModel` to `PTheorem`, `PTables`, `Audit5899` | 11 | 247 s | | 3.5 GB |
| 3: `PArith` | 1 | 60 s | | 5.8 GB, and 10.7 GB committed |
| 3: `PSound` to `PFinal`, `PSmall`, `Audit5899Search` | 8 | 137 s | | 3.4 GB |
| 3: `PSmallSearch` | 1 | 79 s | | 4.2 GB |
| 3: `PSmall6Search` | 1 | 43 s | | 7.5 GB |
| step 3 in all | 39 | 953 s | 17 min | |
| 4: `PTestNative` | 1 | 406 s | 7 min | 0.3 GB |
| 5: the 17 evaluations | 17 | 72,876 s of CPU time | 2 h 52 min | 0.3 GB each |
| 6: `PFinalNative`, `Audit5899Native` | 2 | 291 s | 5 min | 3.4 GB |
| in all | 60 | | 3 h 21 min | |

Before it, `../words/build.sh lower` compiled the 151 modules of the two libraries in 67 minutes with one
process, and `../lower/build.sh` compiled 128 modules in 25 minutes. Of these, `build.sh` here uses 150
modules of the libraries, `Challenge`, the two files of the bridge and 17 files of `../lower`. A module of
step 3 that loads all of Mathlib commits about 8 GB of memory. `PFinalNative` took 268 s of the 291 s
because it was the first module to load Mathlib after the evaluations.

The evaluations, in the order in which they ended:

| module | search | threads | by the clock | CPU time |
|---|---|---|---|---|
| `PProfNative` | FF, five equations | 8 | 10 s | not measured |
| `PF45Native` | F5 and F4 | 8 | 11 s | not measured |
| `PF3Native` | F3 | 8 | 122 s | 548 s |
| `PRingNative` | FR | 4 | 72 s | 209 s |
| `PF2Native` | F2 | 4 | 593 s | 2,318 s |
| `PF1bNative` | F1, second range | 4 | 11 min | 2,659 s |
| `PF1aNative` | F1, first range | 4 | 36 min | 6,714 s |
| `PF0bNative` | F0, range 2 of 10 | 3 | 33 min | 5,597 s |
| `PF0eNative` | F0, range 5 | 3 | 18 min | 2,863 s |
| `PF0fNative` | F0, range 6 | 3 | 24 min | 3,461 s |
| `PF0cNative` | F0, range 3 | 3 | 87 min | 9,946 s |
| `PF0aNative` | F0, range 1 | 4 | 124 min | 11,889 s |
| `PF0gNative` | F0, range 7 | 3 | 45 min | 6,750 s |
| `PF0dNative` | F0, range 4 | 3 | 104 min | 9,643 s |
| `PF0iNative` | F0, range 9 | 3 | 12 min | 1,980 s |
| `PF0hNative` | F0, range 8 | 3 | 42 min | 6,918 s |
| `PF0jNative` | F0, range 10 | 4 | 394 s | 1,381 s |

The CPU time of the 17 is 72,876 s, which is 20.2 thread-hours: 60,428 s for F0, 9,373 s for F1 and the
rest for the others. That is 0.66 microseconds for a kept prefix. The script reads the CPU time of a
process every ten seconds, so the figure of a module is up to ten seconds short and the two shortest
modules have none. The threads of a module are those it was started with; a module uses fewer once only
its largest parts are left, which is why `PF0aNative` took 124 minutes by the clock for 198 minutes of CPU
time. In an earlier run of FR as one part on one thread the search took 181 s, 0.39 microseconds for a
kept prefix.

The build directory held 241 MB after the three scripts, of which 38 MB are the files of this part. The
library is 0.5 MB and the C file 0.6 MB.

## What is not covered

* The evaluations are not checked by the kernel. This is level 2, as said at the top.
* The paper `MODEL.md` and the proof on paper are not part of this package; the Lean files are the proof.
* The node counts of F2, F1 and F0 were not counted again in Lean, only by the C program. The proof does
  not use any count.
* The method has no end-to-end check at n = 6, where the tables alone do not reach the known value 872.
* No file states the lower bound and the word of 5,905 letters in one statement.
* Nothing here says that 5,899 is the length of the shortest word.
* Linux and macOS, as said under "Building".
