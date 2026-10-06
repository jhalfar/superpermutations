# The word for n = 12 in the Lean kernel

The word of 522,737,175 letters on 12 symbols (`words/superpermutation-12-522737175.txt.xz` at the top of this
repository, my own word) is a superpermutation. The Lean kernel checks the word itself, as in `../words` for
n = 7 to 11. This part is kept apart from `../words` because of its size: 0.9 GB of generated Lean files and
six to seven hours of Lean time.

Every computation is a kernel reduction (`by decide +kernel`). There is no `native_decide` and no `sorry`.
Every statement below depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## The statements

`Covers` and `HasWord` are the definitions of Jay Pantone's `Challenge.lean`. The statements are copied from
the Lean files with the symbols spelled in ASCII.

```lean
-- Superperm/Upper12.lean                                       (namespace LiteralSuperperm)
theorem hasWord_twelve : HasWord 12 522737175
theorem exists_word_twelve : exists w : List (Fin 12), Covers w /\ w.length = 522737175

-- Superperm/UpperHunter12.lean, TwoSided12.lean                (namespace SuperpermBridge)
theorem ssuper_twelve_le : Hunter.Ssuper 12 <= 522737175
theorem ssuper_twelve : 522610764 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
theorem words_twelve : (exists w : List (Fin 12), Covers w /\ w.length = 522737175) /\
    forall w : List (Fin 12), Covers w -> 522610764 <= w.length

-- Superperm/TwoSidedAB12.lean
theorem ssuper_twelve_kisic  : 522614409 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
theorem ssuper_twelve_boundB : 522622030 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
-- and words_twelve_kisic, words_twelve_boundB in the form of words_twelve

-- Superperm/TwoSidedC12.lean
theorem ssuper_twelve_boundC : 522622378 <= Hunter.Ssuper 12 /\ Hunter.Ssuper 12 <= 522737175
theorem words_twelve_boundC : (exists w : List (Fin 12), Covers w /\ w.length = 522737175) /\
    forall w : List (Fin 12), Covers w -> 522622378 <= w.length
```

The lower bound 522,610,764 is Xiaolong Liu's (`PreimageChain.superperm_numerical_bounds_closed`).
The lower bounds 522,614,409, 522,622,030 and 522,622,378 are the values of Theorems A, B and C of `../lower`;
the last one needs one of the small certificates of Theorem C, which the default level of
`../lower/build.sh` checks.
`Audit12.lean` writes `exists_word_twelve` and `words_twelve` out with no definition of this project.

## What differs from n = 11

The method is the second one of `../words/README.md` (`../words/Superperm/Cyc.lean`): one table entry for
every rotation class, and the word as a literal tree of blocks. Three things are changed for this size, each
in a file of its own in `../words/Superperm/`.

* `TreeOk.lean`: the tree is checked block by block. For n = 11 one kernel computation compares the tree
  with the number it spells, and that computation holds the whole word in memory several times. Here `valT`
  defines the number the tree spells and is never evaluated. `okT` checks the shape of the tree, the size of
  every block, and that neighbouring blocks agree on the letters they share; `okT_sound` shows that the tree
  is then the one `build` makes from `valT`. Every block file checks its own subtree, and `Tree.lean` joins
  the results with `okT_node`.
* `Cyc2.lean`: the list of branches of the walk is checked in groups two levels deep (`groupOKj`,
  `hpre_of_groupsj`), and `covers_of_cyc_ok` is the soundness theorem that `Main.lean` uses.
* `Cyc3.lean`: functions with fewer kernel steps (`getR`, `leafF`, `go2`, `go3`, `goF`, `partCycF`), each
  proven equal to the function of `Cyc.lean` it stands for (`partCycF_eq`). The generated part files check
  `partCycF ... = true` and convert.

The generator is `../words/gen12.py`, and `../words/verify_blocks12.py` compares the blocks in the generated
Lean files with the word file. The certificate has 65,536 blocks of 7,977 letters (plus 23 shared) in 128
files, and 39,916,800 table entries in 55,440 kernel checks of 720 entries each, in 124 files.

## The files

* `Superperm/Upper12.lean`, `UpperHunter12.lean`, `TwoSided12.lean`: the statements.
* `Superperm/TwoSidedAB12.lean`, `TwoSidedC12.lean`: the two-sided statements with the lower bounds of
  `../lower`.
* `Audit12.lean`: the statements written out in full.
* `generated.sha256`: SHA-256 of the 255 files that `gen12.py` writes for this word (875 MB).
* `build.sh`: runs `../words/check_word.sh` on the word and builds the statements.

The word file is `words/superpermutation-12-522737175.txt.xz` of github.com/jhalfar/superpermutations. The
unpacked file (the letters and one line feed) has SHA-256
`97ab1d7c37f1a19f9c9c10d8109382f501da1982f1b66bfa1ddd2511f9149cde`, as in `SHA256SUMS` at the top of that
repository. `check_word.sh` runs the generator with

```sh
python3 gen12.py $WORD12 N12 --depth 16 --bpf 512 --gpf 8 --fast --source TEXT --out DIR
```

The generator needs numpy and about 2 GB of memory and runs 6 minutes. It runs all checks itself in Python
before it writes.

## Building

```sh
../words/build.sh
../lower/build.sh
./build.sh
```

`build.sh` works in the build directory of `../words/build.sh` and compiles what is missing there.
`./build.sh word` builds `hasWord_twelve` alone and does not need that script before it. The settings are
listed at the top of the script and in `../tools/common.sh`.

`../lower/build.sh` works in the same build directory. Without it `build.sh` here compiles what
`TwoSidedAB12.lean` needs of `../lower` itself and leaves `TwoSidedC12.lean` out.

Measured on my machine (Ryzen 9 5950X with 16 cores, 32 GB, Windows 11 with Git Bash), one thread per Lean
process. The machine was shared with other jobs the whole time. `../words/check_word.sh` ran into an empty
build directory, the first 50 modules with three Lean processes and the rest with ten. The statements were
compiled after that with one process, in a build directory that held this certificate and the other modules
that the statements import.

| modules | count | Lean time | peak memory of a process |
|---|---|---|---|
| `TreeOk`, `Cyc2`, `Cyc3` | 3 | 7 to 11 s each | 0.8 GB |
| block files of `N12` | 128 | 32 to 42 s each, 83 min in all | 0.8 GB |
| `N12/Tree` | 1 | 9 s | 1.2 GB |
| part files of `N12` | 124 | 101 to 182 s each, 5.6 h in all | 1.3 GB |
| `N12/Main` | 1 | 14 s | 1.7 GB |
| the statement written by `check_word.sh`, `Upper12` | 2 | 8 s and 9 s | 1.4 GB |
| `UpperHunter12`, `TwoSided12`, `Audit12` | 3 | 305 s, 31 s and 30 s | 3.8 GB |
| `TwoSidedAB12`, `TwoSidedC12` | 2 | 31 s each | 3.8 GB |

In all 264 modules and 7.1 hours of Lean time. By the clock the statements took 8 minutes and `check_word.sh`
62 minutes in its two runs, of which the generator took 6. `UpperHunter12` was the first process of its run to
load all of Mathlib; the modules after it took 30 or 31 s each. `check_word.sh` also compiled Pantone's
`Challenge.lean` and the checkers `Literal`, `Groups` and `Cyc` of `../words` (58 s), which the table leaves
out.

Memory is the working set. For the modules that `check_word.sh` compiles it was measured on a sample that I
compiled a second time, one process at a time: `TreeOk`, `Cyc2`, `Cyc3`, two block files, `Tree`, two part
files, `Main` and the statement written by `check_word.sh`. The part files commit 2.7 GB each and the modules
from `UpperHunter12` on, which load all of Mathlib, 9.1 to 9.2 GB. The files for n = 12 take 2.1 GB of the
build directory: 0.9 GB of generated Lean files and 1.2 GB of compiled modules.

## What is trusted

As in `../words`: the Lean kernel, the definitions `Covers` and `HasWord`, for the statements about
`Hunter.Ssuper` the definition of that quantity, and the three axioms. That the blocks in the Lean files are
the word in the public file is checked by `verify_blocks12.py` and by the hashes, not by the kernel.
