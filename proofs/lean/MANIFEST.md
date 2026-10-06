# Files of this directory

Every file, with its size and one line on what it is. "generated" means written by a script of this
directory from public input files; the build scripts write these files again and compare.

## Scripts that are run directly

These files should have the executable bit (mode 755) in the repository. Everything else is read by
them, by `python3` or by Lean, and needs mode 644 only.

* `constant/build.sh`
* `words/build.sh`
* `words/check_word.sh`
* `words12/build.sh`

## Top level

* `.gitattributes` (344 B): keeps LF line ends in text files, so that the hashes hold on every system
* `MANIFEST.md`: this list
* `README.md` (14.5 KB): what is proven, what a build needs, how to build, what it costs, what is trusted
* `SHA256SUMS`: SHA-256 of every other file of this directory
* `lean-toolchain` (25 B): the Lean version, `leanprover/lean4:v4.31.0`

## constant/

* `constant/Audit1771.lean` (3.2 KB): the results restated with the definitions of `Challenge.lean` only
* `constant/README.md` (15.9 KB): the theorems, the selection, the files, the patch, how to build
* `constant/SuperpermutationUpperBound1771/AllSizes.lean` (9.1 KB): the level on k + 12 symbols for every k;
  `Cert.word_ledger`
* `constant/SuperpermutationUpperBound1771/Certificate/Big00.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big01.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big02.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big03.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big04.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big05.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big06.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big07.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big08.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big09.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big10.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big11.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big12.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Big13.lean` (3.5 KB): generated: cycle pointers for eight of
  the 112 long trails, `BigOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Cert.lean` (10.2 KB): generated: `Certificate.cert : Cert`
* `constant/SuperpermutationUpperBound1771/Certificate/Checks.lean` (11.0 KB): the decidable checks (`WalkOK`,
  `GroupOK`, `BigOK`, ...) and their soundness
* `constant/SuperpermutationUpperBound1771/Certificate/Chunks9.lean` (156.6 KB): generated: the rows of the two trails
  in chunks of 64
* `constant/SuperpermutationUpperBound1771/Certificate/Circles.lean` (6.2 KB): generated: the 203 connector cycles on
  12 symbols, with their checks
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9.lean` (2.0 KB): generated: the completeness check on
  9 symbols assembled
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_1.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_2.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_3.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_4.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_5.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_6.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Complete9_7.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/D9.lean` (7.9 KB): generated: the 336 2-loops without a row on
  9 symbols
* `constant/SuperpermutationUpperBound1771/Certificate/Groups.lean` (3.9 KB): generated: the 48 groups assembled
* `constant/SuperpermutationUpperBound1771/Certificate/Groups00.lean` (142.7 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups01.lean` (142.7 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups02.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups03.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups04.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups05.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups06.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/Groups07.lean` (142.8 KB): generated: six of the 48 groups
  (trails, loops without a row, pointers), `GroupOK`
* `constant/SuperpermutationUpperBound1771/Certificate/WalkA.lean` (71.7 KB): generated: one of the two closed trails
  on 9 symbols, with its checks
* `constant/SuperpermutationUpperBound1771/Certificate/WalkB.lean` (76.2 KB): generated: one of the two closed trails
  on 9 symbols, with its checks
* `constant/SuperpermutationUpperBound1771/Certificate/Walks9.lean` (1.3 KB): generated: the two trails as a level
* `constant/SuperpermutationUpperBound1771/Certificate/modules.txt` (300 B): generated: the generated modules in the
  order in which they are written
* `constant/SuperpermutationUpperBound1771/Corollaries.lean` (3.4 KB): `finite_1771`, `finiteInteger_1771`,
  `hasWord_fourteen`, `_fifteen`, `_sixteen`
* `constant/SuperpermutationUpperBound1771/GenericBounds.lean` (10.9 KB): the rational bound and the epsilon argument
* `constant/SuperpermutationUpperBound1771/Hybrid.lean` (14.1 KB): the certificate as a structure (`Cert`); the levels
  on 10, 11 and 12 symbols
* `constant/SuperpermutationUpperBound1771/Levels.lean` (14.2 KB): a level as a list of closed trails; transport,
  completion, cycle cover of a level
* `constant/SuperpermutationUpperBound1771/Main.lean` (2.8 KB): `finite_bound` and `eventual_bound`
* `constant/SuperpermutationUpperBound1771/Main13.lean` (1.2 KB): `word_thirteen : HasWord 13 6747849960`
* `constant/SuperpermutationUpperBound1771/Repeat.lean` (6.1 KB): a closed trail written m times, its transport and
  inventory
* `constant/SuperpermutationUpperBound1771/Thirteen.lean` (9.1 KB): the counts, the 7,875 connector cycles and the
  word on 13 symbols
* `constant/SuperpermutationUpperBound1771/WordOfLevel.lean` (6.1 KB): `word_of_level`: one completion and the
  connector cycles give a word with its ledger
* `constant/build.sh` (4.1 KB): builds the whole development from sources and prints the axioms
* `constant/gen_cert.py` (18.3 KB): writes the 38 generated certificate files from the two public input files
* `constant/pantone-sources.sha256` (11.3 KB): SHA-256 of the 94 files of Pantone's repository that are compiled
  unchanged and of the original of the patched one
* `constant/patches/SuperpermutationUpperBound/Assembly/SupportedStates.lean` (3.2 KB): patched copy of Pantone's file
  of that name (Apache License 2.0): one import changed, one section removed
* `constant/patches/SupportedStates.diff` (2.4 KB): the same change as a unified diff against his file

## tools/

* `tools/check_hashes.py` (1.5 KB): compares files with a list of SHA-256 hashes, or writes such a list
* `tools/common.sh` (7.9 KB): settings and shell functions shared by the two build scripts
* `tools/order.py` (3.4 KB): build order of Lean modules from their import lines, with a stamp per module

## words/

* `words/Audit11.lean` (1.2 KB): the statement for 11 symbols written out with no definition of this project
* `words/README.md` (19.8 KB): the statements, the two checking methods, the word files, how to build
* `words/Superperm/Bridge.lean` (1.7 KB): the restated definitions are the library's own (`rfl`); the bridge for
  `Hunter.Ssuper`
* `words/Superperm/BridgeCore.lean` (8.4 KB): the Hunter-Raudvere definitions restated (`HR.Ssuper`) and the bridge to
  `Covers`
* `words/Superperm/Cyc.lean` (18.5 KB): second method: `chkT`, `leafCyc`, `partCyc`, `covers_of_cyc`,
  `covers_of_cyc_groups`
* `words/Superperm/Cyc2.lean` (6.6 KB): for n = 12: the list of branches checked in groups two levels deep;
  `covers_of_cyc_ok`
* `words/Superperm/Cyc3.lean` (8.4 KB): for n = 12: functions with fewer kernel steps, proven equal to those of
  `Cyc.lean`
* `words/Superperm/Groups.lean` (3.2 KB): the list of first choices checked group by group: `covers_of_groups`
* `words/Superperm/Literal.lean` (17.1 KB): first method: `wordOf`, `part`, the block tree, `covers_of_parts`
* `words/Superperm/PermForm.lean` (4.4 KB): `Covers` in terms of `Equiv.Perm`; the words on 7, 8, 9 symbols in that
  form
* `words/Superperm/TreeOk.lean` (7.0 KB): for n = 12: the tree of blocks checked block by block: `valT`, `okT`,
  `okT_sound`
* `words/Superperm/TwoSided.lean` (2.5 KB): lower and upper bound in one statement, 7 to 9 symbols
* `words/Superperm/TwoSided10.lean` (848 B): the same for 10 symbols with rumstd's word
* `words/Superperm/TwoSided10b.lean` (881 B): the same for 10 symbols with the word of 4,034,855 letters
* `words/Superperm/TwoSided11.lean` (1.1 KB): the same for 11 symbols
* `words/Superperm/Upper.lean` (1.9 KB): `hasWord_seven`, `hasWord_eight`, `hasWord_nine` and the exact lengths
* `words/Superperm/Upper10.lean` (641 B): `hasWord_ten : HasWord 10 4034873` (rumstd's word)
* `words/Superperm/Upper10b.lean` (779 B): `hasWord_ten_b : HasWord 10 4034855`
* `words/Superperm/Upper11.lean` (1.0 KB): `hasWord_eleven : HasWord 11 43930578`
* `words/Superperm/UpperCyc.lean` (981 B): `hasWord_nine_cyc`, `hasWord_ten_cyc`: 9 and 10 symbols by the second
  method
* `words/Superperm/UpperHR.lean` (1.0 KB): upper bounds for `HR.Ssuper`, 7 to 9 symbols
* `words/Superperm/UpperHR10.lean` (387 B): upper bound for `HR.Ssuper 10` from rumstd's word
* `words/Superperm/UpperHunter.lean` (956 B): `Hunter.Ssuper k <= ...` for 7, 8, 9 symbols
* `words/Superperm/UpperHunter10.lean` (377 B): `Hunter.Ssuper 10 <= 4034873`
* `words/Superperm/UpperHunter10b.lean` (394 B): `Hunter.Ssuper 10 <= 4034855`
* `words/Superperm/UpperHunter11.lean` (430 B): `Hunter.Ssuper 11 <= 43930578`
* `words/build.sh` (9.7 KB): generates the certificates, builds everything from sources and prints the axioms
* `words/check_word.sh` (10.5 KB): one command from a word file to the Lean theorem for that word
* `words/gen.py` (11.4 KB): generator of the first method: one table entry for every permutation
* `words/gen11.py` (17.0 KB): generator of the second method: one table entry for every rotation class
* `words/gen12.py` (20.3 KB): generator of the second method for n = 12 (blocks checked one by one, groups two levels
  deep)
* `words/generated.sha256` (32.1 KB): SHA-256 of all 355 files that the generators write
* `words/generated/Superperm/N7/Main.lean` (1.3 KB): generated by `gen.py`: `hasWord` for 7 symbols
* `words/generated/Superperm/N7/P000.lean` (18.0 KB): generated by `gen.py`: position tables and kernel checks, 7
  symbols
* `words/generated/Superperm/N7/Word.lean` (6.5 KB): generated by `gen.py`: the word on 7 symbols as a number
* `words/generated/Superperm/N7/modules.txt` (15 B): generated by `gen.py`: the modules of this directory in build
  order
* `words/generated/Superperm/N8/Main.lean` (1.2 KB): generated by `gen.py`: `hasWord` for 8 symbols
* `words/generated/Superperm/N8/P000.lean` (171.9 KB): generated by `gen.py`: position tables and kernel checks, 8
  symbols
* `words/generated/Superperm/N8/Word.lean` (46.7 KB): generated by `gen.py`: the word on 8 symbols as a number
* `words/generated/Superperm/N8/modules.txt` (15 B): generated by `gen.py`: the modules of this directory in build
  order
* `words/generated/Superperm/N9/Main.lean` (1.8 KB): generated by `gen.py`: `hasWord` for 9 symbols
* `words/generated/Superperm/N9/P000.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P001.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P002.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P003.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P004.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P005.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P006.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P007.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/P008.lean` (203.2 KB): generated by `gen.py`: position tables and kernel checks, 9
  symbols
* `words/generated/Superperm/N9/Word.lean` (409.5 KB): generated by `gen.py`: the word on 9 symbols as a number
* `words/generated/Superperm/N9/modules.txt` (55 B): generated by `gen.py`: the modules of this directory in build
  order
* `words/generated/Superperm/N9cyc/B000.lean` (103.7 KB): generated by `gen11.py`: blocks of the word on 9 symbols
* `words/generated/Superperm/N9cyc/B001.lean` (103.7 KB): generated by `gen11.py`: blocks of the word on 9 symbols
* `words/generated/Superperm/N9cyc/B002.lean` (103.7 KB): generated by `gen11.py`: blocks of the word on 9 symbols
* `words/generated/Superperm/N9cyc/B003.lean` (103.7 KB): generated by `gen11.py`: blocks of the word on 9 symbols
* `words/generated/Superperm/N9cyc/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 9 symbols
* `words/generated/Superperm/N9cyc/P000.lean` (245.7 KB): generated by `gen11.py`: tables and kernel checks, 9 symbols
* `words/generated/Superperm/N9cyc/Tree.lean` (1.1 KB): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 9 symbols
* `words/generated/Superperm/N9cyc/modules.txt` (35 B): generated by `gen11.py`: the modules of this directory in
  build order
* `words/hunter-sources.sha256` (6.8 KB): SHA-256 of the 75 files of the Hunter-Raudvere library that are compiled
* `words/inputs.tsv` (983 B): the six word files: symbols, letters, SHA-256
* `words/preimage-sources.sha256` (8.0 KB): SHA-256 of the 76 files of the preimage-chain project that are compiled
* `words/verify_blocks.py` (2.7 KB): checks that the blocks of a `gen11.py` certificate spell a word file
* `words/verify_blocks12.py` (3.2 KB): checks that the blocks of a `gen12.py` certificate spell a word file
* `words/verify_word.py` (2.6 KB): checks that the number `W` of a `gen.py` certificate spells a word file
* `words/word_info.py` (4.6 KB): symbols, length, hash and run structure of a word, for `check_word.sh`

## words12/

* `words12/Audit12.lean` (1.8 KB): the statements for n = 12 written out with no definition of this project
* `words12/README.md` (6.7 KB): the statements for n = 12, what differs from n = 11, how to build
* `words12/Superperm/TwoSided12.lean` (1.1 KB): lower and upper bound in one statement for n = 12, with Liu's lower
  bound
* `words12/Superperm/Upper12.lean` (1.3 KB): `hasWord_twelve : HasWord 12 522737175`
* `words12/Superperm/UpperHunter12.lean` (433 B): `Hunter.Ssuper 12 <= 522737175`
* `words12/build.sh` (4.1 KB): runs `check_word.sh` on the word for n = 12, builds the statements, prints the axioms
* `words12/generated.sha256` (23.0 KB): SHA-256 of the 255 files that `gen12.py` writes for this word
