# Literal superpermutations for n = 7 to 11 in the Lean kernel

Each theorem here says that a superpermutation of a stated length exists, and each is proven by letting the
Lean kernel check one explicit word. A bridge then turns the words into upper bounds for `Hunter.Ssuper k`,
the least length of a superpermutation as the Hunter-Raudvere library defines it. Xiaolong Liu's
preimage-chain project proves lower bounds for that quantity, so lower and upper bound can stand in one Lean
statement.

New here are the checkers with their generators, the bridge, and `check_word.sh`, one command that takes any
word file to its theorem (see "Checking your own word"). The words for n = 10 and 11 are mine; the words for
n = 7, 8 and 9 are by Teodorescu, Pantone and rumstd. The lower bounds are Liu's, and his library and the
Hunter-Raudvere library are used unchanged.

Every computation is a kernel reduction (`by decide +kernel`). There is no `native_decide`, no `sorry` and no
`Lean.ofReduceBool`. Every statement below depends on the axioms `propext`, `Classical.choice` and
`Quot.sound` only; the single kernel checks depend on `propext` only.

## The statements

`Covers` and `HasWord` are the definitions of Jay Pantone's `Challenge.lean`, imported and not restated:
`Covers w` says that every list of K different letters occurs in `w` as a contiguous part, and `HasWord K n`
says that some `w : List (Fin K)` with `Covers w` has at most `n` letters. The statements are copied from the
Lean files with the symbols spelled in ASCII (`forall`, `exists`, `<=`, `/\`, `<->`, `Nat`).

```lean
-- Superperm/Upper.lean, Upper10.lean, Upper10b.lean, Upper11.lean      (namespace LiteralSuperperm)
theorem hasWord_seven  : HasWord 7 5905
theorem hasWord_eight  : HasWord 8 46181
theorem hasWord_nine   : HasWord 9 408731
theorem hasWord_ten    : HasWord 10 4034873
theorem hasWord_ten_b  : HasWord 10 4034855
theorem hasWord_eleven : HasWord 11 43930578
theorem exists_word_eleven : exists w : List (Fin 11), Covers w /\ w.length = 43930578
-- and exists_word_seven, _eight, _nine, _ten, _ten_b in the same form, with the exact length

-- Superperm/UpperCyc.lean: the words of hasWord_nine and hasWord_ten_b again, by the second method
theorem hasWord_nine_cyc : HasWord 9 408731
theorem hasWord_ten_cyc  : HasWord 10 4034855

-- Superperm/PermForm.lean: permutations as bijections (Equiv.Perm), the form some other Lean projects use
theorem covers_iff_forall_perm {K : Nat} (w : List (Fin K)) :
    Covers w <-> forall p : Equiv.Perm (Fin K), exists before after : List (Fin K),
      w = before ++ List.ofFn p ++ after
```

```lean
-- Superperm/Bridge.lean                                                (namespace SuperpermBridge)
theorem hunter_hasWord_iff {k L : Nat} (hk : 0 < k) : HasWord k L <-> Hunter.Ssuper k <= L
theorem hunter_le_ssuper_iff {k L : Nat} (hk : 0 < k) :
    L <= Hunter.Ssuper k <-> forall w : List (Fin k), Covers w -> L <= w.length
theorem hunter_ssuper_eq_sInf {k : Nat} (hk : 0 < k) :
    Hunter.Ssuper k = sInf {m | exists w : List (Fin k), Covers w /\ w.length = m}

-- Superperm/UpperHunter.lean, UpperHunter10.lean, UpperHunter10b.lean, UpperHunter11.lean
theorem ssuper_seven_le  : Hunter.Ssuper 7 <= 5905
theorem ssuper_eight_le  : Hunter.Ssuper 8 <= 46181
theorem ssuper_nine_le   : Hunter.Ssuper 9 <= 408731
theorem ssuper_ten_le    : Hunter.Ssuper 10 <= 4034873
theorem ssuper_ten_le_b  : Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven_le : Hunter.Ssuper 11 <= 43930578

-- Superperm/TwoSided.lean, TwoSided10.lean, TwoSided10b.lean, TwoSided11.lean
theorem ssuper_seven  : 5892 <= Hunter.Ssuper 7 /\ Hunter.Ssuper 7 <= 5905
theorem ssuper_eight  : 46118 <= Hunter.Ssuper 8 /\ Hunter.Ssuper 8 <= 46181
theorem ssuper_nine   : 408418 <= Hunter.Ssuper 9 /\ Hunter.Ssuper 9 <= 408731
theorem ssuper_ten    : 4033080 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034873
theorem ssuper_ten_b  : 4033080 <= Hunter.Ssuper 10 /\ Hunter.Ssuper 10 <= 4034855
theorem ssuper_eleven : 43916235 <= Hunter.Ssuper 11 /\ Hunter.Ssuper 11 <= 43930578
theorem words_eleven : (exists w : List (Fin 11), Covers w /\ w.length = 43930578) /\
    forall w : List (Fin 11), Covers w -> 43916235 <= w.length
-- and words_seven, _eight, _nine, _ten, _ten_b in the same form
```

The lower bounds are the conjuncts of Liu's `PreimageChain.superperm_numerical_bounds_closed`
(github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds, built on
github.com/urdvr/superpermutations-hunter). The `words_` statements say the same without either library's
own notion of a superpermutation.

`hasWord_ten` is about rumstd's word of 4,034,873 letters and is weaker than `hasWord_ten_b`. I keep it because
it was proven first and because it is someone else's word. `UpperHR.lean` and `UpperHR10.lean` state the
upper bounds for a copy `HR.Ssuper` of the Hunter-Raudvere definition that needs only small parts of Mathlib;
`Bridge.lean` proves `@HR.Ssuper = @Hunter.Ssuper` by `rfl`.

`Audit11.lean` writes the statement for 11 symbols out with no definition of this project.

## How a word is checked

There are two methods, each a hand-written Lean file with a generator in Python. In both, the word is a
natural number `W` whose base-16 digit `i` is letter `i` of the word, and `wordOf K L W` is the list of its
`L` lowest digits as elements of `Fin K`. The certificate is a table of positions. Nothing about the table is
proven: a wrong entry makes a comparison fail, and then `decide` reports that the proposition is false.

### First method: one table entry for every permutation

The files are `Superperm/Literal.lean` and `Groups.lean`; the generator is `gen.py`.

* `part K L mS mK B d W stride pre tbl : Bool` fixes the first choices `pre` and walks the tree of all
  arrangements of the remaining letters. At a leaf it reads a position from the table and compares the K
  digits of `W` at that position with the arrangement it has built.
* `W` is read through a binary tree of blocks (`build`, `get`), so a lookup copies half a block and not the
  whole word. Every function the kernel evaluates uses bare `Nat.add`, `Nat.land`, `Nat.shiftRight`, each
  one big-number operation in the kernel.
* `covers_of_parts` is the soundness theorem: successful runs of `part` for every way of fixing the first
  choices give `Covers (wordOf K L W hK)`. That the list of first choices is complete is itself a kernel check
  (`itemsComplete`, or `tailsComplete` and `groupOK` of `Groups.lean` for 10 symbols).
* One kernel check covers 720 permutations: 7 checks for 7 symbols, 56 for 8, 504 for 9, 5,040 for 10.

### Second method: one table entry for every rotation class

The file is `Superperm/Cyc.lean`, on top of the two files of the first method; the generator is `gen11.py`.
The word is a literal tree of blocks here.

* In the words for n = 8 to 12 named here every rotation class of permutations is visited in one stretch of
  2K - 1 letters, which then contains all K rotations. The table entry of a class is the position of that
  stretch and a rotation number r. The leaf test `leafCyc` compares the 2K - 1 digits at the position with
  digits r to r + 2K - 2 of the class representative written four times. `rot_window` proves that every
  rotation is then a window of the word.
* The word is given as block constants, generated into files `B000.lean` and so on. Neighbouring blocks share
  2K - 1 letters. `Tree.lean` defines the tree over the blocks and `W` from the tree, and one kernel check
  `chkT ... tree W = true` shows that the tree is the one `build` would make from `W`.
* `covers_of_cyc` and `covers_of_cyc_groups` are the soundness theorems (for 8 to 16 symbols).
* For n = 11 this is 3,628,800 leaf checks in 5,040 kernel checks, where the first method would need
  39,916,800. `gen11.py` refuses a word in which some rotation class is split. The word for n = 7 is such a
  word (66 of its 720 classes are visited in two pieces), and the soundness theorem asks for at least 8
  symbols. `build.sh` uses the first method for n = 7 and 8; the word for n = 8 passes the second one as well
  (I ran it through `check_word.sh`).

For n = 12 the second method is changed in three places, each in a file of its own (`Superperm/TreeOk.lean`,
`Cyc2.lean`, `Cyc3.lean`, with the generator `gen12.py`). `../words12/README.md` describes them.

## The word files

| setting | symbols | letters | SHA-256 of the letters and one line feed |
|---|---|---|---|
| `WORD7` | 7 | 5,905 | `37e4177c17d3cd6bed0c2f3932e229656105326e8b877b75d95e67744b103c50` |
| `WORD8` | 8 | 46,181 | `07637d5518101667132847e74add605e9809961d5793342321cb70c3c599c62b` |
| `WORD9` | 9 | 408,731 | `619763367249af17f2815349e939544654b6a0f5443b15be65612c827e185dd0` |
| `WORD10A` | 10 | 4,034,873 | `194241ecc45d9a2445a840240889ba6f3f0054cde58ac9c203f4787db2ca3e12` |
| `WORD10` | 10 | 4,034,855 | `09e2c807aea5f0890d257f97d5d447c0235d41df9589caff8899f01d2016f7f6` |
| `WORD11` | 11 | 43,930,578 | `65ddf4c4a3ebaa69de7bc6be29e0b38ad010055f22ef6abeeffdb4f508176092` |

`inputs.tsv` has the same table with the hash of the letters alone as well. Where the files come from:

* `WORD10` and `WORD11` are `words/superpermutation-10-4034855.txt.xz` and
  `words/superpermutation-11-43930578.txt.xz` of github.com/jhalfar/superpermutations (this repository), my
  own words. The scripts read the `.xz` files directly. The hashes above are those of the unpacked files, as
  in `SHA256SUMS` at the top of that repository.
* `WORD8` is `words/8/superpermutation-8-46181.txt` of Pantone's repository
  (github.com/jaypantone/superperm-upper-43-80, the commit named in `../README.md`).
* `WORD7` is `5905_7_sol1.txt`, the first of four words of 5,905 letters that Teodorescu attached to his
  message of 2026-08-18 in the superpermutators group
  (https://groups.google.com/g/superpermutators/c/D5sKkV2jBuc). It uses the letters 1 to 7. The attachment
  starts with an empty line; the scripts ignore white space around the word.
* `WORD9` is the word of 408,731 letters that the user rumstd added in pull request 1 to Pantone's
  repository (https://github.com/jaypantone/superperm-upper-43-80/pull/1, 2026-10-02).
* `WORD10A` is the word of 4,034,873 letters of rumstd's pull request 3 to the same repository.

The words on 7, 8 and 9 symbols and rumstd's word on 10 symbols are other people's words, and their files are
not in this directory. What is here instead is `generated/`: the Lean certificate files for 7, 8 and 9 symbols
as the generators wrote them (3.1 MB). So `build.sh` works without `WORD7`, `WORD9` and `WORD10A`; it then
uses these files, skips the comparison with a word file, and leaves out the statements about rumstd's word
on 10 symbols.

## The generated files

`build.sh` runs the generators with exactly these arguments (`--source TEXT` and `--out DIR` left out here;
the texts are in `build.sh`):

```sh
python3 gen.py   $WORD7   N7
python3 gen.py   $WORD8   N8
python3 gen.py   $WORD9   N9
python3 gen.py   $WORD10A N10
python3 gen.py   $WORD10  N10b
python3 gen11.py $WORD9   N9cyc  --depth 6 --bpf 16
python3 gen11.py $WORD10  N10cyc
python3 gen11.py $WORD11  N11    --depth 12
```

| directory | files | size | in `generated/` |
|---|---|---|---|
| `Superperm/N7` | 4 | 26 KB | yes |
| `Superperm/N8` | 4 | 220 KB | yes |
| `Superperm/N9` | 12 | 2.2 MB | yes |
| `Superperm/N9cyc` | 8 | 0.7 MB | yes |
| `Superperm/N10` | 93 | 25 MB | no |
| `Superperm/N10b` | 93 | 25 MB | no |
| `Superperm/N10cyc` | 16 | 6.6 MB | no |
| `Superperm/N11` | 125 | 73 MB | no |

`generated.sha256` lists the SHA-256 of all 355 files. The generators are deterministic, and `build.sh` stops
if a generated file differs from that list. Each generator runs all checks itself in Python before it writes
(`gen.py` needs 2 minutes for 10 symbols, `gen11.py` 25 seconds for 11 symbols), and it writes the SHA-256 of
its input into `Word.lean` or `Tree.lean`.

`verify_word.py` (first method) and `verify_blocks.py` (second method) read the numbers back from the
generated Lean files and compare them with the word file. They share no code with the generators.

## Building

`build.sh` does everything, from sources, into `../build/words` (or `BUILD_DIR`). The settings are listed at
the top of the script and in `../tools/common.sh`; `../README.md` says how to fetch what the build needs.

```sh
./build.sh          # everything
./build.sh words    # the literal words only: needs Pantone's Challenge.lean and Mathlib, nothing else
./build.sh lower    # the 151 modules of the two lower-bound libraries only
```

Measured on my machine (Ryzen 9 5950X, 32 GB, Windows 11 with Git Bash; one thread per Lean process, other
jobs running beside it), from an empty build directory:

| what | modules | Lean time | peak memory of a process |
|---|---|---|---|
| `N7`, `N8` | 6 | 1 min | 0.9 GB |
| `N9` | 11 | 4.5 min | 0.9 GB |
| `N10` (4,034,873 letters) | 92 | 71 min, a part file 34 to 58 s | 1.1 GB |
| `N10b` (4,034,855 letters) | 92 | 58 min, a part file 30 to 60 s | 1.1 GB |
| `N9cyc` | 7 | 1.3 min | 0.9 GB |
| `N10cyc` | 15 | 5.7 min | 0.9 GB |
| `N11` | 124 | 79 min, a part file 34 to 56 s | 0.9 GB, `Tree` 1.6 GB |
| checkers and statements | 14 | 2 min | 0.9 GB |
| the two lower-bound libraries | 151 | 68 min, a module 5 to 46 s | 3.9 GB |
| `Bridge`, `UpperHunter*`, `TwoSided*` | 9 | 8 min | 3.4 GB |

In all 521 modules and 5 hours of Lean time. The run took 3 hours 14 minutes: one process for the literal
words and, for part of the time, one for the libraries beside it, then two processes for the words. On the
same word the second method is much the faster: 5.7 against 58 minutes for n = 10.

Memory is the working set of the Lean process. A process that imports all of Mathlib (the last two lines)
commits 8 to 9 GB of virtual memory, and it takes minutes and not seconds when the Mathlib files are not in
the file cache, so keep 6 GB free for it (`MINFREE_GB=6`). The build directory has 0.5 GB, of which 0.13 GB
are generated Lean files.

## Checking your own word

```sh
./check_word.sh WORDFILE [--jobs N] [--minfree GB] [--out DIR] [--yes]
```

This one command goes from a word file to the Lean theorem for that word. The file holds the word with one
symbol per character, as `.txt` or `.txt.xz`; any 2 to 16 different characters will do, and they are ranked
in ASCII order. The command needs what `./build.sh words` needs: Lean, Mathlib, Pantone's `Challenge.lean`,
and Python with numpy. No file has to be edited.

1. It reads the word and prints the number of symbols n, the length L and the SHA-256 of the file.
2. It chooses the method (`word_info.py` looks at the word; nothing is generated before this) and says which.
   If every rotation class is visited in one stretch, it takes the second method: `gen11.py` for
   n = 8 to 11, and `gen12.py` with the three files `TreeOk.lean`, `Cyc2.lean` and `Cyc3.lean` for n = 12
   (`../words12/README.md` says what these change). Otherwise, if n <= 10 and every permutation occurs, it
   takes the first method. Otherwise it stops and says why.
3. It prints an estimate of Lean time, disk and memory. A run above 30 minutes of Lean time needs `--yes`.
4. It generates the certificate into a build directory of its own, `../build/check-n-L` (or `--out DIR`),
   and lets Lean check it, `--jobs` processes at a time.
5. It writes the statement for this word, `Checked_n_L.lean`, and compiles it. The file holds `HasWord n L`,
   the same statement written out with no definition of this project, and `#print axioms`. The command
   fails unless the axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
6. It compares the numbers in the generated Lean files with the word file, with `verify_word.py`,
   `verify_blocks.py` or `verify_blocks12.py`, none of which uses the generator.
7. It prints a summary: the statement, the axioms, the hash, the time, where the files are.

It stops at the first step that fails, says which step, and returns 0 only if every step passed. A run that
was interrupted continues when the same command is given again.

What the theorem says: some list over `Fin n` with exactly L letters contains every list of n different
letters as a contiguous part. Only the letters of the word are checked. How the word was built plays no
part, and no plan or selection behind it is looked at. As for the words above, that the word in the Lean files
is the word in your file is checked by step 6 and not by the kernel.

The limits:

* The second method needs every rotation class of permutations in one stretch of 2n - 1 letters. The words
  on 8 to 12 symbols named in this directory have that; the word on 7 symbols does not.
* Without that structure a word can be checked up to n = 10, with one table entry for every permutation.
* n = 13 is out of reach. It would take about 60 hours of Lean time for the 479 million rotation classes
  and about 11 GB of generated Lean files, and every Lean process would have to load the whole word, about
  6.7 GB of compiled blocks.

What it costs, measured on the machine named above, each run into an empty build directory (so the compile
of the checkers is included: about half a minute, and 83 s in the run for n = 12):

| word | method | Lean time | time of the run |
|---|---|---|---|
| n = 7, 5,905 letters | first | 1 min | 1 min 8 s, one process |
| n = 8, 46,181 letters | second | 1.6 min | 1 min 43 s, one process |
| n = 9, 408,731 letters | second | 2.4 min | 2 min 35 s, one process |
| n = 10, 4,034,855 letters | second | 8.8 min | 5 min 33 s, two processes |
| n = 11, 43,930,578 letters | second | about 80 min | not run through this command |
| n = 12, 522,737,175 letters | second, with the changes for n = 12 | 7.0 h | 62 min, three and ten processes |

The line for n = 11 is the time of `N11` in `build.sh`, which runs the same generator and the same modules.
The run for n = 12 shared the machine with other jobs. It was stopped after 50 modules and continued with the
same command, with three processes before and ten after.
With the first method a word for n = 10 takes about an hour (`N10`, `N10b` above). A Lean process needs about
1 GB, for n = 12 up to 1.4 GB and one module 1.7 GB. The build directory takes 2 to 20 MB up to n = 10, 0.2 GB
for n = 11 and 2.1 GB for n = 12.

Two damaged copies of the word for n = 9 stop at step 2 with the count: with one letter changed 362,872 of
the 362,880 permutations occur, without the last letter 362,879.

## What is trusted

* The Lean kernel, the definitions `Covers` and `HasWord` of `Challenge.lean`, the definitions of
  `Hunter.Ssuper` and of the lower-bound theorem in the two libraries, and the three axioms.
* Not proven in Lean: that the number `W` in the Lean files is the word in the public file. The theorem says
  that some word of that length covers; which word it is follows from `verify_word.py` and `verify_blocks.py`
  and from the hashes, that is, from scripts and not from the kernel.
* The generators and the tables need no trust. A wrong table or a wrong block makes a kernel check fail.

## What is not here

* The statements for n = 12. They are in `../words12`; the three Lean files and the generator that this
  size needs (`Superperm/TreeOk.lean`, `Cyc2.lean`, `Cyc3.lean`, `gen12.py`, `verify_blocks12.py`) are here,
  because `check_word.sh` uses them, and `../words12/README.md` describes them.
* A word for n = 13. See "Checking your own word".
* The negative tests of the kernel checks (a changed table digit, a changed letter in one block, a changed
  shared letter). I ran them when the checkers were written; they are not part of this directory.
* A Lake project. The modules are compiled one by one by `build.sh`.
