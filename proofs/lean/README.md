# Lean proofs

A superpermutation on n symbols is a word that contains every permutation of the symbols as a contiguous
part. This directory holds Lean 4 proofs about how long such a word has to be. Its parts:

* `constant/` proves that for every n >= 13 there is a superpermutation of length at most
  F3(n) + (1771/3456 + o(1)) (n-3)!, where F3(n) = n! + (n-1)! + (n-2)!. Jay Pantone's theorem has 43/80 in
  place of 1771/3456.
* `words/` proves that explicit words for n = 7, 8, 9, 10 and 11 are superpermutations, by letting the kernel
  check each word, and states these upper bounds together with the lower bounds of Xiaolong Liu's Lean
  project.
* `words12/` does the same for a word for n = 12. It is a part of its own because of its size.
* `lower/` proves three lower bounds. With hpv(k) = k! + (k-1)! + (k-2)! + k - 3, a superpermutation on k
  symbols has at least hpv(k) + ceil(2 ((k-2)! - (k-2)) / (k (k-3))) letters for k >= 5 (Theorem A) and at
  least hpv(k) + ceil(2 ((k-2)! - (k-2)) / (k^2 - 4k + 1)) letters for k >= 7 (Theorem B). Theorem C makes
  the denominator smaller by a term that a finite search justifies; the searches are evaluated by the Lean
  kernel for k = 8 to 14.

The bounds proven here for the length L(n) of the shortest superpermutation:

| n | lower: Theorem B | lower: Theorem C | upper: a word or a construction checked here |
|---|---|---|---|
| 7 | 5,895 | | 5,905 |
| 8 | 46,129 | 46,133 | 46,181 |
| 9 | 408,465 | 408,469 | 408,731 |
| 10 | 4,033,329 | 4,033,378 | 4,034,855 |
| 11 | 43,917,793 | 43,917,903 | 43,930,578 |
| 12 | 522,622,030 | 522,622,378 | 522,737,175 |
| 13 | 6,746,615,766 | 6,746,626,957 | 6,747,849,960 |
| 14 | 93,891,107,960 | 93,891,141,008 | 93,905,309,790 |

Jay Pantone announced a table of lower bounds on 29 September 2026: 46,130, 408,468, 4,033,374, 43,917,903,
522,622,378 and 6,746,626,519 for n = 8 to 13. His proof is not public. The proofs here were made without it.
The upper bounds for n = 7 to 12 are literal words; those for n = 13 and 14 are values of the construction of
`constant/`.

The parts state their results with the definitions of Pantone's `Challenge.lean`
(github.com/jaypantone/superperm-upper-43-80): `Covers w` says that every list of K different letters occurs
in the word `w` as a contiguous part, and `HasWord K n` says that such a word with at most `n` letters
exists.

Every proof is checked by the Lean kernel. There is no `native_decide`, no `sorry` and no added axiom. Every
statement listed below depends on `propext`, `Classical.choice` and `Quot.sound` and on nothing else.

What is new here, and what is not:

* The constant. The selection that gives 1771/3456 and its Lean proof are new. The construction is Pantone's,
  and the proof is built on his Lean library, of which one file is replaced by a patched copy.
* The words. The kernel checkers are new, and the words for n = 10, 11 and 12 are mine (they are in `words/`
  at the top of this repository). The words for n = 7, 8 and 9 are by Teodorescu, Pantone and rumstd.
* The bridge between `Covers` and `Hunter.Ssuper`, the quantity of the Hunter-Raudvere library, is new. The
  lower bounds it is used with in `words/` are Xiaolong Liu's, from his preimage-chain project.
* Theorems A and B. The Lean proofs are new; the formulas are not. Zach Hunter wrote the formula of
  Theorem A on 21 October 2019 in the group thread "New Lower Bound"
  (https://groups.google.com/g/superpermutators/c/M-1yQC0Aj44) as a bound he expected to prove, and the note
  of GPT 5.6 Sol and Marin Kisic of 7 August 2026 has a proof on paper that is not formalised. The formula
  of Theorem B is Cole Fritsch's. He posted it on 20 January 2020 in the same thread with an argument that
  he himself called far from rigorous and that Zach Hunter disputed the same day.
* Theorem C, the search behind it and the proof that the search is complete are new. Pantone announced his
  table first, as said above.
* All three lower bounds are built on Liu's library and on the Hunter-Raudvere library, and both libraries
  are used unchanged. [`lower/README.md`](lower/README.md) says in detail which lemma is whose.

## What is proven

The statements are copied from the Lean files, with the symbols spelled in ASCII (`forall`, `exists`, `<=`,
`/\`, `Nat`, `Rat`, `eps`), which Lean reads as the same statements.

### The constant (`constant/`, namespace `SuperpermutationUpperBound1771`)

```lean
theorem word_thirteen : SuperpermutationBounds.HasWord 13 6747849960

theorem finite_bound (m : Nat) (hm : 11 <= m) (a : Nat) (ha : 2 <= a) (ham : a <= m) :
    exists w : List (Fin (m + 2)), SuperpermutationBounds.Covers w /\
      (w.length : Rat) <=
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : Rat)
          + (1771 / 3456 : Rat) * ((m - 1).factorial : Rat)
          + ((a - 2 : Nat) : Rat) * (25 / 1152 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat)
          + ((m - a : Nat) : Rat) *
              min ((25 / 1152 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat))
                (((m + 1).factorial : Rat) / ((a + 1).factorial : Rat))

theorem eventual_bound :
    forall eps : Rat, 0 < eps -> exists N : Nat, 13 <= N /\
      forall K : Nat, N <= K -> exists w : List (Fin K), SuperpermutationBounds.Covers w /\
        (w.length : Rat) <= SuperpermutationBounds.F3 K +
          ((1771 / 3456 : Rat) + eps) * (Nat.factorial (K - 3) : Rat)

theorem hasWord_fourteen : HasWord 14 93905309790
theorem hasWord_fifteen  : HasWord 15 1401331300446
theorem hasWord_sixteen  : HasWord 16 22320908101800
```

`finite_bound` is the bound for every size from n = 13 on (n = m + 2), and `eventual_bound` is its consequence
for large n. `word_thirteen` and the three `hasWord_` lines are values of `finite_bound`. `finite_1771` and
`finiteInteger_1771` state `finite_bound` in the shape of Pantone's `Finite` and `FiniteInteger`.
[`constant/README.md`](constant/README.md) describes the selection and the proof.

### The words (`words/` and `words12/`, namespaces `LiteralSuperperm` and `SuperpermBridge`)

```lean
theorem hasWord_seven  : HasWord 7 5905
theorem hasWord_eight  : HasWord 8 46181
theorem hasWord_nine   : HasWord 9 408731
theorem hasWord_ten_b  : HasWord 10 4034855
theorem hasWord_eleven : HasWord 11 43930578
theorem hasWord_twelve : HasWord 12 522737175

theorem hunter_hasWord_iff {k L : Nat} (hk : 0 < k) : HasWord k L <-> Hunter.Ssuper k <= L
theorem hunter_le_ssuper_iff {k L : Nat} (hk : 0 < k) :
    L <= Hunter.Ssuper k <-> forall w : List (Fin k), Covers w -> L <= w.length

theorem ssuper_seven  : 5892 <= Hunter.Ssuper 7 /\ Hunter.Ssuper 7 <= 5905
theorem ssuper_eight  : 46118 <= Hunter.Ssuper 8 /\ Hunter.Ssuper 8 <= 46181
theorem ssuper_nine   : 408418 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_b  : 4033080 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven : 43916235 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
theorem ssuper_twelve : 522610764 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
```

The lower bounds in the last six lines are the conjuncts of Liu's
`PreimageChain.superperm_numerical_bounds_closed`. [`words/README.md`](words/README.md) has the full list of
statements (among them rumstd's word of 4,034,873 letters for n = 10 and a second proof for n = 9 and 10),
the two checking methods, and where each word file comes from. [`words12/README.md`](words12/README.md) says
what is changed for n = 12.

### The lower bounds (`lower/`, namespaces `SuperpermLowerBounds` and `SuperpermBridge`)

```lean
def hpv (k : Nat) : Nat := k.factorial + (k - 1).factorial + (k - 2).factorial + k - 3
def kisicBound (k : Nat) : Nat :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + k * (k - 3) - 1) / (k * (k - 3))
def boundB (k : Nat) : Nat :=
  hpv k + (2 * ((k - 2).factorial - (k - 2)) + (k * k - 4 * k + 1) - 1) / (k * k - 4 * k + 1)

theorem superperm_kisic_bound (hk : 5 <= k) : kisicBound k <= Ssuper k
theorem superperm_boundB {k : Nat} (hk : 7 <= k) : boundB k <= Ssuper k
theorem covers_length_ge_kisicBound {k : Nat} (hk : 5 <= k) :
    forall w : List (Fin k), Covers w -> kisicBound k <= w.length
theorem covers_length_ge_boundB {k : Nat} (hk : 7 <= k) :
    forall w : List (Fin k), Covers w -> boundB k <= w.length

-- Theorem C: c = cn / q and b = bn / q; HStatement is the window bound for the chains of Liu's library
def boundC (k cn bn q : Nat) : Nat :=
  hpv k + (2 * q * (k - 2).factorial - (2 * q * (k - 2) + bn) + piC k cn q - 1) / piC k cn q
theorem superperm_boundC (hk : 5 <= k) (hcond : ConditionsC k cn bn q) (hH : HStatement k cn bn q) :
    boundC k cn bn q <= Ssuper k

-- Theorem C with the searches evaluated: no hypothesis left
theorem covers_lower_bound_8  : forall w : List (Fin 8),  Covers w -> 46133 <= w.length
theorem covers_lower_bound_9  : forall w : List (Fin 9),  Covers w -> 408469 <= w.length
theorem covers_lower_bound_10 : forall w : List (Fin 10), Covers w -> 4033378 <= w.length
theorem covers_lower_bound_11 : forall w : List (Fin 11), Covers w -> 43917903 <= w.length
theorem covers_lower_bound_12 : forall w : List (Fin 12), Covers w -> 522622378 <= w.length
theorem covers_lower_bound_13 : forall w : List (Fin 13), Covers w -> 6746626957 <= w.length
theorem covers_lower_bound_14 : forall w : List (Fin 14), Covers w -> 93891141008 <= w.length

-- with the literal words
theorem ssuper_eight_boundC  : 46133 <= Hunter.Ssuper 8 /\ Hunter.Ssuper 8 <= 46181
theorem ssuper_nine_boundC   : 408469 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_boundC    : 4033378 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven_boundC : 43917903 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
theorem ssuper_twelve_boundC : 522622378 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
theorem words_twelve_boundC : (exists w : List (Fin 12), Covers w /\ w.length = 522737175) /\
    forall w : List (Fin 12), Covers w -> 522622378 <= w.length
```

`Ssuper` is `Hunter.Ssuper`. The division is that of natural numbers, so the last summands of `kisicBound`,
`boundB` and `boundC` are the ceilings in the formulas. `piC k cn q` is q (k^2 - 4k + 1) - cn (k - 1), and
`ConditionsC` is three inequalities between the constants. The seven `covers_lower_bound_` lines also hold in
the form `46133 <= Ssuper 8` (`ssuper_lower_bound_8` and so on).

Theorem C needs a search for each pair (c, b). The default build of `lower/` checks 22 searches and gives
46,132, 408,469, 4,033,378, 43,917,901, 522,622,378, 6,746,626,601 and 93,891,140,217 for k = 8 to 14;
`lower/build.sh full` checks five large searches more and gives the values of the table.
[`lower/README.md`](lower/README.md) has all statements, the values of the three theorems next to Liu's, how
the bound of Theorem C arises, and the steps of the proofs.

## What is in this directory

* `constant/`: the development for 1771/3456. 11 hand-written Lean files and an audit file, 38 generated
  certificate files, the generator, one patched file of Pantone's library, `build.sh`, a README.
* `words/`: the checkers (the two methods, and three files with the changes for n = 12), the statements for
  n = 7 to 11, the bridge, three generators, three verifiers, `check_word.sh` for a word of your own, the
  generated certificates for n = 7, 8 and 9, lists of hashes, `build.sh`, a README.
* `words12/`: the statements for n = 12, an audit file, the list of hashes of the generated files,
  `build.sh`, a README.
* `lower/`: the proofs of the three lower bounds (31 Lean files), the two-sided statements that use them,
  five audit files, the lists of the certificates of Theorem C, their generators, the list of hashes of the
  generated files, `build.sh`, a README.
* `tools/`: `common.sh` (settings and functions of the build scripts), `order.py` (build order from the
  import lines), `check_hashes.py`.
* `lean-toolchain`: the Lean version.
* `MANIFEST.md`: every file with one line on what it is.
* `SHA256SUMS`: SHA-256 of every file.

## What a build needs

* Lean 4.31.0 (`leanprover/lean4:v4.31.0`).
* Mathlib at commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, compiled (fetched with `lake exe cache get`;
  7.4 GB on disk with the packages it needs).
* Pantone's repository, github.com/jaypantone/superperm-upper-43-80,
  at commit `c8fb7ffdd69be1375580710ae11b47a295b1f0f6`.
* The Hunter-Raudvere library, github.com/urdvr/superpermutations-hunter,
  at commit `d45222190031d162feb1f6f3cf5fe2d11fab726d`.
* Liu's preimage-chain project, github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds,
  at commit `8474c74a15fa59b8ce55bcf6bceaaa23b9a3dca8`.
* Python 3.8 or newer, with numpy for `words/gen11.py` and `words/gen12.py`.
* bash with the usual tools (on Windows: Git Bash).

`constant/` needs Lean, Mathlib and the sources of Pantone's repository. The literal words of `words/` and
`words12/` need Lean, Mathlib and one file of his, `Challenge.lean`. The bridge and the two-sided statements
need the two lower-bound repositories as well. These three repositories pin the same Mathlib commit, so one
compiled Mathlib serves everything; the scripts take it from Pantone's checkout. Of the repositories only
sources are used: the modules of them that a statement imports are compiled here.

`lower/` needs all three repositories.

## How to build

Fetch the repositories into `deps/` and the compiled Mathlib into the first of them:

```sh
mkdir deps && cd deps
git clone https://github.com/jaypantone/superperm-upper-43-80
git -C superperm-upper-43-80 checkout c8fb7ffdd69be1375580710ae11b47a295b1f0f6
(cd superperm-upper-43-80 && lake exe cache get)
git clone https://github.com/urdvr/superpermutations-hunter
git -C superpermutations-hunter checkout d45222190031d162feb1f6f3cf5fe2d11fab726d
git clone https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds
git -C superpermutations-preimage-chain-lower-bounds checkout 8474c74a15fa59b8ce55bcf6bceaaa23b9a3dca8
cd ..
```

Then run the scripts. Each builds its part from sources into a directory under `build/`, in dependency
order, and prints the `#print axioms` lines at the end. `words12/build.sh` continues in the build directory of
`words/build.sh`, so it comes after it. `constant/build.sh` stands alone.
`lower/build.sh` continues in that build directory as well and comes between the two.

```sh
constant/build.sh
words/build.sh
lower/build.sh             # or: lower/build.sh full
words12/build.sh
```

They are shell scripts of at most 230 lines that call `lean` once per module; `tools/common.sh` (170 lines)
holds what they share. They are controlled by environment variables:

| variable | meaning | default |
|---|---|---|
| `LEAN` | the Lean binary | `lean` (with elan: the version named in `lean-toolchain`) |
| `PYTHON` | Python 3 | `python3` |
| `PANTONE_DIR` | checkout of Pantone's repository | `deps/superperm-upper-43-80` |
| `MATHLIB_PACKAGES` | the compiled Mathlib and the packages it needs | `$PANTONE_DIR/.lake/packages` |
| `HUNTER_DIR` | checkout of the Hunter-Raudvere library | `deps/superpermutations-hunter` |
| `PREIMAGE_DIR` | checkout of Liu's preimage-chain project | `deps/` + the name of that repository |
| `SUPERPERM_REPO` | checkout of this repository, for the input files | `../..` |
| `BUILD_DIR` | the build directory | `build/constant`, `build/words` |
| `JOBS` | Lean processes at the same time | 1 |
| `JOBS_BIG` | the same for the modules that import all of Mathlib | 1 |
| `LEAN_THREADS` | threads of one Lean process | 1 |
| `MINFREE_GB` | start a Lean process only while this many GB of memory are free | 0 (no check) |

A build can be stopped (Ctrl-C, or create the file `STOP` in the build directory to let the running modules
finish) and started again with the same command. A module is compiled again only if its source or something
it imports has changed.

To check a word of your own there is one command, `words/check_word.sh WORDFILE`. It goes from a word file
to the Lean theorem `HasWord n L` for that word without any file being edited, for words up to n = 12.
[`words/README.md`](words/README.md) says what it does and what it costs.

Before Lean starts, each script compares the sources it is about to compile with lists of hashes
(`constant/pantone-sources.sha256`, `words/hunter-sources.sha256`, `words/preimage-sources.sha256`), runs the
generators, and compares what they write with the files or hashes in this directory.

## What it costs

Measured on my machine (Ryzen 9 5950X with 16 cores, 32 GB, Windows 11 with Git Bash), each part from an
empty build directory, one thread per Lean process, other jobs running beside the builds:

| script | modules | Lean time | time of the run | peak memory of a Lean process |
|---|---|---|---|---|
| `constant/build.sh` | 145 | 53 min | 60 min, one process | 3.9 GB |
| `words/build.sh`, the literal words | 361 | 3.7 h | | 1.1 GB, one module 1.6 GB |
| `words/build.sh`, the two libraries | 151 | 68 min | | 3.9 GB |
| `words/build.sh`, bridge and two-sided | 9 | 8 min | | 3.4 GB |
| `words/build.sh` in all | 521 | 5.0 h | 3 h 14 min, one to two processes | 3.9 GB |
| `lower/build.sh`, Theorems A and B | 13 | 8 min | | 3.6 GB |
| `lower/build.sh`, Theorem C at the default level | 114 | 39 min | | 2.5 GB in the searches, 3.6 GB else |
| `lower/build.sh full`, what the large certificates add | 347 | 4.6 h | | 2.8 GB in the searches, 3.3 GB else |
| `lower/build.sh full` in all | 474 | 5.3 h | 1 h 50 min, one to four processes | 3.6 GB |
| `words12/build.sh` | 264 | 7.1 h | 70 min, one to ten processes | 1.4 GB, one module 1.7 GB, the last five 3.8 GB |

Lean time is the sum over the Lean processes. Memory is the working set. A process that imports all of
Mathlib (the two libraries, the bridge, the two-sided statements) commits 8 to 9 GB of virtual memory, and it
is slow unless the Mathlib files stay in the file cache; `MINFREE_GB=6` waits for free memory before each
start.
Most modules of `lower/` outside the searches are of this kind. The rows of `lower/` are from several runs
into the build directory of `words/`.
The row of `words12/build.sh` is from three runs: `words/check_word.sh` into an empty build directory, with
three processes for the first 50 modules and ten for the rest, and then the statements with one process.

Disk: the compiled Mathlib 7.4 GB; `build/constant` 0.3 GB; `build/words` 0.5 GB after `words/build.sh`,
0.5 GB more after `lower/build.sh full` and 2.1 GB more after `words12/build.sh`.

The README of each part has the times per group of modules.

## What is trusted and what is not

* Trusted: the Lean kernel; the definitions in `Challenge.lean`, and for the statements about `Hunter.Ssuper`
  the definition of that quantity in the Hunter-Raudvere library; the axioms `propext`, `Classical.choice`
  and `Quot.sound`. `constant/Audit1771.lean`, `words/Audit11.lean` and `words12/Audit12.lean` restate the
  main results with those definitions written out, so that nothing else has to be read to know what is
  claimed.
* `lower/AuditA.lean`, `AuditB.lean`, `AuditC.lean`, `AuditCSmall.lean` and `AuditCFinal.lean` do the same for
  the lower bounds.
* Not trusted: the generators, the certificate data, the tables. They are inputs to kernel checks, and a
  wrong entry makes a check fail.
* The searches of Theorem C are evaluated by the kernel (`decide +kernel`), with its built-in arithmetic on
  natural numbers. No compiled code is trusted. The Python copy of the search only decides where a search is
  cut into lemmas.
* For the literal words, one link is outside Lean: that the number in the Lean files is the word in the
  public file. The theorems say that a word of that length exists. That it is the published word is checked
  by `words/verify_word.py` and `words/verify_blocks.py` and by the hashes, not by the kernel.
* For the constant, the same holds for the two input files: the theorems do not mention them. `gen_cert.py`
  turns them into the certificate that the kernel checks.
* One file of Pantone's library is replaced by a patched copy (`constant/patches/`): one import is changed
  and a section of 30 lines that the development does not use is removed. His unchanged file would pull in
  his certificate for 9 symbols, which needs more memory than my machine has.
* The lower bounds of Liu's project that `words/` uses are his theorems. I compile them from his sources and
  did not review their proofs.
* The three lower bounds of `lower/` use lemmas of his library and of the Hunter-Raudvere library in the same
  way: compiled here from the sources, their proofs not reviewed by me.

## What is not covered

* The constant: nothing is proven for n <= 12, and no rate for the o(1) term.
* The words: n = 13. The shortest word known for n = 13 has 6.7 billion letters and is out of reach for this
  method.
* Nothing here says that any of the words is shortest.
* The lower bounds: Theorem B is not proven for k = 5 and 6, and Theorem C has certificates for k = 8 to 14
  only. Pantone's proofs are not here; they are not public.
