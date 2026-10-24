# Files of this directory

Every file, with its size and one line on what it is. "generated" means written by a script of this
directory from public input files; the build scripts write these files again and compare.

## Scripts that are run directly

These files should have the executable bit (mode 755) in the repository. Everything else is read by
them, by `python3` or by Lean, and needs mode 644 only.

* `asym/build.sh`
* `constant/build.sh`
* `constant305989/build.sh`
* `constant43586371/build.sh`
* `constant61937/build.sh`
* `lower/build.sh`
* `lower/certificates/C14_843_63334_16000/build.sh`
* `n7/build.sh`
* `n8/build.sh`
* `n8_46134/build.sh`
* `n8struct/build.sh`
* `words/build.sh`
* `words/check_word.sh`
* `words12/build.sh`

## Top level

* `.gitattributes` (344 B): keeps LF line ends in text files, so that the hashes hold on every system
* `MANIFEST.md`: this list
* `README.md` (31.4 KB): what is proven, what a build needs, how to build, what it costs, what is trusted
* `SHA256SUMS`: SHA-256 of every other file of this directory
* `lean-toolchain` (25 B): the Lean version, `leanprover/lean4:v4.31.0`

## asym/

* `asym/ConstAsym/Bridge.lean` (6.4 KB): `Covers` of Pantone stated for `Hunter.IsPermWord`, `Hunter.IsSuperperm` and
  `Hunter.Ssuper`: `ssuper_le_length`, `ssuper_eq_sInf`
* `asym/ConstAsym/Main.lean` (6.5 KB): `shortest_superpermutation_coefficient`, `two_sided`, `coefficient_limit_rat`,
  `L_eq_ssuper`, `hunter_lower_L`
* `asym/ConstAsym/Remainder.lean` (3.8 KB): `remainder_order`: for n >= 2^14 the remainder L(n) - F3(n) lies between
  (n-4)! - 2(n-5)! and 9(n-4)!
* `asym/ConstAsym/Remainder8.lean` (8.3 KB): `remainder_order8`, `lower2_L`, `remainder_limit8`: the bounds 2(n-4)! -
  2(n-5)! and 41/5 (n-4)!, the constant in [2, 8]
* `asym/README.md` (6.7 KB): the shortest superpermutation: the limit of the coefficient, the order of the remainder,
  its constant in [2, 8]; how to build; the axiom audit
* `asym/build.sh` (2.0 KB): builds Pantone's library, the Hunter modules, the needed part of `../constant43586371` and
  the two files here from sources, and prints the axioms

## constant/

* `constant/Audit1771.lean` (3.2 KB): the results restated with the definitions of `Challenge.lean` only
* `constant/README.md` (15.8 KB): the theorems, the selection, the files, the patch, how to build
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

## constant305989/

* `constant305989/README.md` (7.9 KB): the block step, the theorems, the files, how to build, the axiom audit
* `constant305989/SuperpermutationUpperBound305989/AllSizes.lean` (9.1 KB): the level on k + 12 symbols for every k;
  `Cert.word_ledger`
* `constant305989/SuperpermutationUpperBound305989/AllSizesB.lean` (8.3 KB): the level on k + 16 symbols for every k;
  `word_ledgerB`
* `constant305989/SuperpermutationUpperBound305989/BlockB.lean` (22.4 KB): the block lemma: `above3`, the inventory of
  repeated walks, `BlockData`, `BlockOK`, the block above every loop
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big00.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big01.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big02.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big03.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big04.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big05.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big06.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big07.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big08.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big09.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big10.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big11.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big12.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Big13.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/BlockCert.lean` (1.5 KB): generated: the block
  certificate (data, checks, pointers, assembly)
* `constant305989/SuperpermutationUpperBound305989/Certificate/BlockChecks.lean` (2.0 KB): generated: the block
  certificate (data, checks, pointers, assembly)
* `constant305989/SuperpermutationUpperBound305989/Certificate/BlockData.lean` (69.8 KB): generated: the block
  certificate (data, checks, pointers, assembly)
* `constant305989/SuperpermutationUpperBound305989/Certificate/BlockPorts16a.lean` (3.1 KB): generated: the block
  certificate (data, checks, pointers, assembly)
* `constant305989/SuperpermutationUpperBound305989/Certificate/BlockPorts16b.lean` (3.1 KB): generated: the block
  certificate (data, checks, pointers, assembly)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Cert.lean` (10.4 KB): generated: `Certificate.cert :
  Cert`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Checks.lean` (10.9 KB): the decidable checks (`WalkOK`,
  `GroupOK`, `BigOK`, `smallPortsB`, ...) and their soundness
* `constant305989/SuperpermutationUpperBound305989/Certificate/Chunks9.lean` (156.6 KB): generated: the rows of the two
  trails in chunks of 64
* `constant305989/SuperpermutationUpperBound305989/Certificate/Circles.lean` (5.9 KB): generated: the 155 connector
  cycles on 12 symbols that the long trails use, with their checks
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9.lean` (2.0 KB): generated: the completeness
  check on 9 symbols assembled
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_1.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_2.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_3.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_4.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_5.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_6.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/Complete9_7.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/D9.lean` (7.9 KB): generated: the 336 2-loops without a
  row on 9 symbols
* `constant305989/SuperpermutationUpperBound305989/Certificate/GCircles13.lean` (8.9 KB): generated: the 288 connector
  cycles on 13 symbols that cover the short walks of the groups
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups.lean` (7.2 KB): generated: the 48 groups assembled
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups00.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups01.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups02.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups03.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups04.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups05.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups06.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Groups07.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small00.lean` (5.6 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small01.lean` (5.7 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small02.lean` (5.7 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small03.lean` (5.9 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small04.lean` (5.9 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small05.lean` (5.9 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small06.lean` (5.9 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/Small07.lean` (5.9 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant305989/SuperpermutationUpperBound305989/Certificate/WalkA.lean` (71.7 KB): generated: one of the two closed
  trails on 9 symbols, with its checks
* `constant305989/SuperpermutationUpperBound305989/Certificate/WalkB.lean` (76.2 KB): generated: one of the two closed
  trails on 9 symbols, with its checks
* `constant305989/SuperpermutationUpperBound305989/Certificate/Walks9.lean` (1.3 KB): generated: the two trails as a
  level
* `constant305989/SuperpermutationUpperBound305989/Certificate/modules.txt` (375 B): generated: the generated modules in
  the order in which they are written
* `constant305989/SuperpermutationUpperBound305989/CorollariesB.lean` (3.1 KB): `finite_305989`, `finiteInteger_305989`,
  `hasWord_sixteen_B`, `hasWord_seventeen_B`
* `constant305989/SuperpermutationUpperBound305989/Fifteen.lean` (16.1 KB): the level on 15 symbols: core walks and the
  block above each of the 6,048 loops; the counts
* `constant305989/SuperpermutationUpperBound305989/GenericBoundsB.lean` (11.2 KB): the rational bound and the epsilon
  argument with 305989/604800 and 23333/2217600
* `constant305989/SuperpermutationUpperBound305989/Hybrid.lean` (14.7 KB): the certificate as a structure (`Cert`, with
  `gcircles` and `smallPorts`); the levels on 10, 11 and 12 symbols
* `constant305989/SuperpermutationUpperBound305989/Levels.lean` (14.2 KB): a level as a list of closed trails;
  transport, completion, cycle cover of a level
* `constant305989/SuperpermutationUpperBound305989/MainB.lean` (3.1 KB): `finite_bound16` and `eventual_bound16`
* `constant305989/SuperpermutationUpperBound305989/Relabel.lean` (11.9 KB): relabelling lemma for transport, completion,
  ports, charts and cycle covers; `relab d0 d`
* `constant305989/SuperpermutationUpperBound305989/Repeat.lean` (6.1 KB): a closed trail written m times, its transport
  and inventory
* `constant305989/SuperpermutationUpperBound305989/Thirteen.lean` (9.4 KB): the counts, the 7,731 connector cycles and
  the word on 13 symbols
* `constant305989/SuperpermutationUpperBound305989/WordOfLevel.lean` (6.1 KB): `word_of_level`: one completion and the
  connector cycles give a word with its ledger
* `constant305989/block_checks_body.lean` (1.1 KB): the text of `BlockChecks.lean` after its header, read by
  `gen_blockB.py`
* `constant305989/build.sh` (4.3 KB): builds the whole development from sources and prints the axioms
* `constant305989/data/cyc_s103_old2_0.txt` (145 B): the connector cycles of the block on 15 symbols (checked by
  `gen_blockB.py` only)
* `constant305989/data/cyc_t_s103_old2_0_n16.txt` (459 B): the 26 connector cycles of the block on 16 symbols
* `constant305989/data/s103_old2_0.txt` (21.5 KB): the block on 14 symbols: closed walks and loops without a row, lines
  `x T`
* `constant305989/gen_blockB.py` (12.2 KB): writes the five generated `Block*` certificate files from the three files in
  `data/`
* `constant305989/gen_cert.py` (24.4 KB): writes the generated certificate files shared with `constant61937` from the
  two public input files

## constant43586371/

* `constant43586371/PROOF.md` (11.7 KB): the limit theorem on paper: construction, lemmas, bounds
* `constant43586371/PROOF_R.md` (8.6 KB): the family R'(m) of blocks at every level, on paper
* `constant43586371/README.md` (17.3 KB): the nested block levels, the theorems, the files, how to build, the axiom
  audit
* `constant43586371/REFEREE.md` (13.6 KB): report of an independent check of the limit theorem
* `constant43586371/SuperpermutationUpperBound43586371/AllSizes.lean` (9.1 KB): the level on k + 12 symbols for every k;
  `Cert.word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/AllSizesG.lean` (8.6 KB): a closed level to every size; counts as
  ratios to factorials; the word with the finite-bound ledger
* `constant43586371/SuperpermutationUpperBound43586371/BlockG.lean` (26.7 KB): the block lemma with the frame as a
  parameter: `BlockData`, `BlockOK`, `BlockPorts`, `BlockCert`, the block above every loop
* `constant43586371/SuperpermutationUpperBound43586371/BlockUp.lean` (7.2 KB): the block lemma with the connector cycles
  chosen one level up (`BlockCertUp`)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big00.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big01.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big02.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big03.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big04.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big05.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big06.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big07.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big08.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big09.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big10.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big11.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big12.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Big13.lean` (3.5 KB): generated: cycle pointers for
  eight of the 112 long trails, `BigOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockB73.lean` (1.7 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockB73Cover.lean` (5.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockB73Data.lean` (20.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockB73Up0.lean` (1.7 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockB73Walks.lean` (1.9 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockD73.lean` (1.7 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockD73Cover.lean` (5.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockD73Data.lean` (21.9 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockD73Up0.lean` (1.5 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockD73Walks.lean` (2.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103.lean` (2.1 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Cover.lean` (11.5 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Data.lean` (68.5 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Up0.lean` (2.2 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Up1.lean` (2.2 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Up2.lean` (2.3 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Up3.lean` (1.7 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS103Walks.lean` (2.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133.lean` (1.4 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133Cover.lean` (23.5 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133Data.lean` (162.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133Ports.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133U.lean` (3.2 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UCyc.lean` (1.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp0_0.lean` (1.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp0_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp1_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp1_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp2_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp2_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp3_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp3_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp4_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133UUp4_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS133Walks.lean` (2.4 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163.lean` (1.4 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover.lean` (3.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover0.lean` (3.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover1.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover10.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover11.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover12.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover13.lean` (3.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover14.lean` (3.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover15.lean` (3.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover16.lean` (2.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover2.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover3.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover4.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover5.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover6.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover7.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover8.lean` (3.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Cover9.lean` (3.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Data.lean` (333.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Ports.lean` (8.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163U.lean` (2.7 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UCyc.lean` (3.5 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp0.lean` (1.9 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp1.lean` (1.9 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp10.lean` (2.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp11.lean` (2.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp2.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp3.lean` (1.9 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp4.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp5.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp6.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp7.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp8.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163UUp9.lean` (2.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockS163Walks.lean` (3.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103.lean` (1.4 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103Cover.lean` (11.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103Data.lean` (67.0 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103Ports.lean` (3.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103U.lean` (2.0 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UCover.lean` (11.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UData.lean` (67.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UUp0.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UUp1.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UUp2.lean` (2.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103UWalks.lean` (2.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW103Walks.lean` (2.4 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133.lean` (1.4 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133Cover.lean` (23.7 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133Data.lean` (161.1 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133Ports.lean` (3.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133U.lean` (2.8 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UCyc.lean` (1.4 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp0_0.lean` (1.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp0_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp1_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp1_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp2_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp2_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp3_0.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133UUp3_1.lean` (1.3 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockW133Walks.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103.lean` (1.4 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103Cover.lean` (11.4 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103Data.lean` (65.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103Ports.lean` (3.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103U.lean` (2.0 KB): generated: a part of the
  certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UCover.lean` (11.5 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UData.lean` (65.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UUp0.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UUp1.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UUp2.lean` (2.2 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103UWalks.lean` (2.8 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/BlockX103Walks.lean` (2.6 KB): generated: a part of
  the certificate of one block (data, walks, cover, cycle pointers, assembly)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Cert.lean` (10.4 KB): generated: `Certificate.cert :
  Cert`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Checks.lean` (10.9 KB): the decidable checks
  (`WalkOK`, `GroupOK`, `BigOK`, `smallPortsB`, ...) and their soundness
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Chunks9.lean` (156.6 KB): generated: the rows of the
  two trails in chunks of 64
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Circles.lean` (5.9 KB): generated: the 155 connector
  cycles on 12 symbols that the long trails use, with their checks
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9.lean` (2.1 KB): generated: the completeness
  check on 9 symbols assembled
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_1.lean` (6.6 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_2.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_3.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_4.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_5.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_6.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Complete9_7.lean` (6.7 KB): generated: one seventh of
  the completeness check on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/D9.lean` (7.9 KB): generated: the 336 2-loops without
  a row on 9 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/GCircles13.lean` (8.9 KB): generated: the 288
  connector cycles on 13 symbols that cover the short walks of the groups
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups.lean` (7.3 KB): generated: the 48 groups
  assembled
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups00.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups01.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups02.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups03.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups04.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups05.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups06.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Groups07.lean` (138.8 KB): generated: six of the 48
  groups (trails, loops without a row), `GroupOK`
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small00.lean` (5.6 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small01.lean` (5.7 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small02.lean` (5.7 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small03.lean` (5.9 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small04.lean` (5.9 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small05.lean` (5.9 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small06.lean` (5.9 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Small07.lean` (5.9 KB): generated: pointers of the
  group cycles for the short walks (1,440 in all over eight files)
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/WalkA.lean` (71.8 KB): generated: one of the two
  closed trails on 9 symbols, with its checks
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/WalkB.lean` (76.2 KB): generated: one of the two
  closed trails on 9 symbols, with its checks
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/Walks9.lean` (1.3 KB): generated: the two trails as a
  level
* `constant43586371/SuperpermutationUpperBound43586371/Certificate/modules.txt` (375 B): generated: the generated
  modules in the order in which they are written
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesC.lean` (3.2 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesD.lean` (3.2 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesE.lean` (3.2 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesF.lean` (3.2 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesG.lean` (3.3 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesH.lean` (3.2 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesI.lean` (3.1 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/CorollariesJ.lean` (3.3 KB): the bound in the shape of
  `Finite`/`FiniteInteger` and two `HasWord` values, for one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsC.lean` (11.4 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsD.lean` (11.4 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsE.lean` (11.6 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsF.lean` (11.4 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsG.lean` (11.5 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsH.lean` (11.4 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsI.lean` (11.3 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/GenericBoundsJ.lean` (11.6 KB): the rational bound and the
  epsilon argument with the constants of this level
* `constant43586371/SuperpermutationUpperBound43586371/Hybrid.lean` (14.7 KB): the certificate as a structure (`Cert`,
  with `gcircles` and `smallPorts`); the levels on 10, 11 and 12 symbols
* `constant43586371/SuperpermutationUpperBound43586371/Levels.lean` (14.2 KB): a level as a list of closed trails;
  transport, completion, cycle cover of a level
* `constant43586371/SuperpermutationUpperBound43586371/MainC.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainD.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainE.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainF.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainG.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainH.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainI.lean` (2.9 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/MainJ.lean` (3.0 KB): `finite_bound…` and `eventual_bound…` of
  one of the eight constants
* `constant43586371/SuperpermutationUpperBound43586371/Nested2.lean` (3.0 KB): two block levels: the counts and
  `word_ledgerC`
* `constant43586371/SuperpermutationUpperBound43586371/Nested2b.lean` (2.6 KB): two block levels with other blocks or
  cycles one level up: the counts and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/Nested2c.lean` (2.4 KB): two block levels with other blocks or
  cycles one level up: the counts and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/Nested3.lean` (3.3 KB): three block levels: the counts and
  `word_ledgerD`
* `constant43586371/SuperpermutationUpperBound43586371/Nested3b.lean` (2.5 KB): three block levels with cycles one level
  up: the counts and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/NestedN1.lean` (2.5 KB): no selection, then blocks: the counts
  and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/NestedN2.lean` (2.6 KB): no selection, then blocks: the counts
  and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/NestedN3.lean` (2.8 KB): no selection, then blocks: the counts
  and `word_ledger`
* `constant43586371/SuperpermutationUpperBound43586371/NoSeed.lean` (3.9 KB): `Stage.noSeed`: a level with no selection,
  the pending loops are all arrangements
* `constant43586371/SuperpermutationUpperBound43586371/PortsSplit.lean` (2.0 KB): the cycle pointers of a trail split
  into parts
* `constant43586371/SuperpermutationUpperBound43586371/Relabel.lean` (11.9 KB): relabelling lemma for transport,
  completion, ports, charts and cycle covers; `relab d0 d`
* `constant43586371/SuperpermutationUpperBound43586371/Repeat.lean` (6.1 KB): a closed trail written m times, its
  transport and inventory
* `constant43586371/SuperpermutationUpperBound43586371/Stage.lean` (20.4 KB): `Stage`, `Stage.advance`, `Stage.close`: a
  level with pending loops, a block above each, charts for the rest
* `constant43586371/SuperpermutationUpperBound43586371/Thirteen.lean` (9.4 KB): the counts, the 7,731 connector cycles
  and the word on 13 symbols
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RArith.lean` (4.8 KB): the key arithmetic of disjointness
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RAudit.lean` (436 B): `#print axioms` of 12 theorems of the
  UniR files
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RAudit8.lean` (333 B): `#print axioms` of the theorems of
  `RRate8`
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RBlock.lean` (8.5 KB): R'(m) as a block for every m >= 7:
  `rData_ok`, `rData_safe`, `rFam`
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RBlockRows.lean` (17.3 KB): all rows of the block R'(m) are
  distinct; the loops of the block; their count
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RDistinct.lean` (21.1 KB): arrangements and keys of the
  rows; rows by index
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RIterate.lean` (5.0 KB): the count recursion `cntR` and the
  closed levels `closedR`
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RLoops.lean` (9.3 KB): the loops above the canonical loop
  for a walk; the descriptors `Dl`, `Setting`
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RMain.lean` (2.2 KB): `kappaR`, `gammaR`, `finite_boundR`
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RPorts.lean` (19.7 KB): exit shifts and orbits of the ports;
  the shared cycles cover every walk
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RRate.lean` (15.1 KB): the normalised recursion and
  `rate_R`: length at most F3 n + (9/n)(n-3)! for n >= 2^14
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RRate8.lean` (15.3 KB): `rate_R8`, `rate_R8_eventually`: F3
  n + (41/5)(n-4)! for n >= 2^14, and (8 + eps)(n-4)! eventually
* `constant43586371/SuperpermutationUpperBound43586371/UniR/RWalk.lean` (17.0 KB): the walk W(m, g, roles, s) for every
  gap g: closed trail, bases, length, charge
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Arith.lean` (7.6 KB): the invariants of the counts
  through one double step
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Audit.lean` (631 B): `#print axioms` of 17 lemmas of the
  limit theorem
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Block.lean` (6.9 KB): the walk as a block (`famS`), the
  empty block
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Bounds.lean` (9.9 KB): from a closed level to the finite
  bound and to the epsilon statement
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Canon.lean` (9.9 KB): canonical forms of the loops above
  the canonical loop; their count
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Distinct.lean` (21.6 KB): the rows of the walk are
  pairwise different loops
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Iterate.lean` (10.6 KB): the stages for all levels:
  `closed_level`
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Main.lean` (6.1 KB): `small_coefficient`,
  `coefficient_tends_to_zero`
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Ports.lean` (10.6 KB): exit and orbit of the ports of the
  walk; the single cycle covers it
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/Walk.lean` (22.5 KB): the walk W(m): a closed trail, its
  bases, length and charge
* `constant43586371/SuperpermutationUpperBound43586371/Uniform/WalkLoops.lean` (14.7 KB): the loops of the walk:
  injectivity, membership, length
* `constant43586371/SuperpermutationUpperBound43586371/WordOfLevel.lean` (6.1 KB): `word_of_level`: one completion and
  the connector cycles give a word with its ledger
* `constant43586371/bound_R.py` (2.9 KB): prints the exact value of `finite_boundR` at a given n, minimised over its
  parameters
* `constant43586371/build.sh` (5.2 KB): builds the whole development from sources and prints the axioms
* `constant43586371/data/b73_dw_0.txt` (6.8 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/block_7_3_enum14_0.txt` (6.8 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/blocks.names` (68 B): the names of the blocks (or of the constants) that the generators
  write, in order
* `constant43586371/data/bounds.names` (16 B): the names of the blocks (or of the constants) that the generators
  write, in order
* `constant43586371/data/cyc_s133_0.txt` (104 B): the connector cycles of a block
* `constant43586371/data/cyc_s163_old2_0_ref.txt` (190 B): the connector cycles of a block
* `constant43586371/data/cyc_t_b73_dw_0_n13.txt` (165 B): the connector cycles of a block
* `constant43586371/data/cyc_t_block_7_3_enum14_0_n13.txt` (142 B): the connector cycles of a block
* `constant43586371/data/cyc_t_s103_old2_0_n16.txt` (459 B): the connector cycles of a block
* `constant43586371/data/cyc_t_w103_0.4795_0_n16.txt` (389 B): the connector cycles of a block
* `constant43586371/data/cyc_t_w103_0.6245_1_n16.txt` (389 B): the connector cycles of a block
* `constant43586371/data/cyc_up_s133_0_alph.txt` (272 B): the connector cycles of a block
* `constant43586371/data/cyc_up_s163_old2_0_alph.txt` (990 B): the connector cycles of a block
* `constant43586371/data/cyc_up_w133_0_alph.txt` (203 B): the connector cycles of a block
* `constant43586371/data/cyc_w103_0.4795_0.txt` (147 B): the connector cycles of a block
* `constant43586371/data/cyc_w103_0.6245_1.txt` (147 B): the connector cycles of a block
* `constant43586371/data/cyc_w133_0.txt` (104 B): the connector cycles of a block
* `constant43586371/data/s103_old2_0.txt` (21.5 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/s133_0.txt` (52.2 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/s163_old2_0.txt` (108.2 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/w103_0.4795_0.txt` (21.5 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/w103_0.6245_1.txt` (21.5 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/data/w133_0.txt` (52.2 KB): a block (closed walks and loops without a row), lines `x T`
* `constant43586371/gen_blocks.py` (28.1 KB): writes the `Block*` certificate files of the five nested blocks from the
  files in `data/`
* `constant43586371/gen_bounds.py` (11.7 KB): writes `GenericBounds`, `Main` and `Corollaries` (C, D) from the files of
  `constant305989` by text substitution
* `constant43586371/gen_cert.py` (23.2 KB): writes the generated certificate files shared with `constant61937` from the
  two public input files
* `constant43586371/ledgerC.py` (8.2 KB): the ledger of the nested levels with exact fractions: charge, cycles, charts,
  finite values

## constant61937/

* `constant61937/README.md` (7.7 KB): the cycle re-choice, the theorems, the files, how to build, the axiom audit
* `constant61937/SuperpermutationUpperBound61937/AllSizes.lean` (9.1 KB): the level on k + 12 symbols for every k;
  `Cert.word_ledger`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big00.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big01.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big02.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big03.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big04.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big05.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big06.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big07.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big08.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big09.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big10.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big11.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big12.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Big13.lean` (3.5 KB): generated: cycle pointers for eight
  of the 112 long trails, `BigOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Cert.lean` (10.3 KB): generated: `Certificate.cert : Cert`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Checks.lean` (10.9 KB): the decidable checks (`WalkOK`,
  `GroupOK`, `BigOK`, `smallPortsB`, ...) and their soundness
* `constant61937/SuperpermutationUpperBound61937/Certificate/Chunks9.lean` (156.6 KB): generated: the rows of the two
  trails in chunks of 64
* `constant61937/SuperpermutationUpperBound61937/Certificate/Circles.lean` (5.9 KB): generated: the 155 connector cycles
  on 12 symbols that the long trails use, with their checks
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9.lean` (2.0 KB): generated: the completeness check
  on 9 symbols assembled
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_1.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_2.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_3.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_4.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_5.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_6.lean` (6.7 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/Complete9_7.lean` (6.6 KB): generated: one seventh of the
  completeness check on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/D9.lean` (7.9 KB): generated: the 336 2-loops without a row
  on 9 symbols
* `constant61937/SuperpermutationUpperBound61937/Certificate/GCircles13.lean` (8.9 KB): generated: the 288 connector
  cycles on 13 symbols that cover the short walks of the groups
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups.lean` (7.2 KB): generated: the 48 groups assembled
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups00.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups01.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups02.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups03.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups04.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups05.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups06.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Groups07.lean` (138.8 KB): generated: six of the 48 groups
  (trails, loops without a row), `GroupOK`
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small00.lean` (5.6 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small01.lean` (5.7 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small02.lean` (5.7 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small03.lean` (5.8 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small04.lean` (5.8 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small05.lean` (5.8 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small06.lean` (5.8 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/Small07.lean` (5.8 KB): generated: pointers of the group
  cycles for the short walks (1,440 in all over eight files)
* `constant61937/SuperpermutationUpperBound61937/Certificate/WalkA.lean` (71.7 KB): generated: one of the two closed
  trails on 9 symbols, with its checks
* `constant61937/SuperpermutationUpperBound61937/Certificate/WalkB.lean` (76.2 KB): generated: one of the two closed
  trails on 9 symbols, with its checks
* `constant61937/SuperpermutationUpperBound61937/Certificate/Walks9.lean` (1.3 KB): generated: the two trails as a level
* `constant61937/SuperpermutationUpperBound61937/Certificate/modules.txt` (375 B): generated: the generated modules in
  the order in which they are written
* `constant61937/SuperpermutationUpperBound61937/Corollaries.lean` (3.4 KB): `finite_61937`, `finiteInteger_61937`,
  `hasWord_fourteen`, `_fifteen`, `_sixteen`
* `constant61937/SuperpermutationUpperBound61937/GenericBounds.lean` (11.0 KB): the rational bound and the epsilon
  argument
* `constant61937/SuperpermutationUpperBound61937/Hybrid.lean` (14.7 KB): the certificate as a structure (`Cert`, with
  `gcircles` and `smallPorts`); the levels on 10, 11 and 12 symbols
* `constant61937/SuperpermutationUpperBound61937/Levels.lean` (14.2 KB): a level as a list of closed trails; transport,
  completion, cycle cover of a level
* `constant61937/SuperpermutationUpperBound61937/Main.lean` (2.8 KB): `finite_bound` and `eventual_bound`
* `constant61937/SuperpermutationUpperBound61937/Main13.lean` (1.2 KB): `word_thirteen : HasWord 13 6747847656`
* `constant61937/SuperpermutationUpperBound61937/Repeat.lean` (6.1 KB): a closed trail written m times, its transport
  and inventory
* `constant61937/SuperpermutationUpperBound61937/Thirteen.lean` (9.4 KB): the counts, the 7,731 connector cycles and the
  word on 13 symbols
* `constant61937/SuperpermutationUpperBound61937/WordOfLevel.lean` (6.1 KB): `word_of_level`: one completion and the
  connector cycles give a word with its ledger
* `constant61937/build.sh` (3.7 KB): builds the whole development from sources and prints the axioms
* `constant61937/gen_cert.py` (24.4 KB): writes the 47 generated certificate files and `modules.txt` from the two public
  input files

## lower/

* `lower/AuditA.lean` (3.0 KB): Theorem A written out with no definition of this project
* `lower/AuditB.lean` (2.7 KB): Theorem B written out with no definition of this project
* `lower/AuditC.lean` (4.2 KB): Theorem C, as a statement with its hypothesis, written out with no definition of this
  project
* `lower/AuditCFinal.lean` (3.8 KB): the seven best bounds of Theorem C (all 27 certificates) written out by hand
* `lower/AuditCSmall.lean` (4.2 KB): the seven best bounds of Theorem C from the small certificates written out by
  hand
* `lower/LowerBounds/ChainCapacityB.lean` (15.0 KB): the capacity bound with slope k - 3 as arithmetic,
  `chain_capacity_slope3`
* `lower/LowerBounds/ChainCapacityC.lean` (30.0 KB): Theorem C: windows (`IsWindow`, `WindowBound`) and the capacity
  of a list of deficits
* `lower/LowerBounds/ComponentCapacityB.lean` (20.6 KB): the capacity bound for the chains and components of Liu's
  library
* `lower/LowerBounds/ComponentCapacityC.lean` (21.3 KB): Theorem C: `HStatement` and the capacity bound for chains and
  components
* `lower/LowerBounds/DeficitOne.lean` (18.6 KB): the deficit-one lemma, `partition_unit_after_full_next_large`
* `lower/LowerBounds/LemmaZ.lean` (18.0 KB): the lemma about junctions of cost zero, `lemma_Z`
* `lower/LowerBounds/LemmaZC.lean` (9.1 KB): Theorem C: the junction lemma with the sum of the two deficits
* `lower/LowerBounds/SBridge.lean` (4.3 KB): bridge: `hStatement_of_model : ModelStatement k cn bn q -> HStatement k
  cn bn q`
* `lower/LowerBounds/SBridgeChain.lean` (9.9 KB): bridge: a chain of Liu's library as a chain of entries
* `lower/LowerBounds/SBridgeModel.lean` (13.7 KB): bridge: the model loses nothing (model chains are chains of
  entries)
* `lower/LowerBounds/SBridgePath.lean` (12.9 KB): bridge: the entries of the blocks of a path, doors and seams
* `lower/LowerBounds/SBridgeRelabel.lean` (7.9 KB): bridge: relabelling of model chains
* `lower/LowerBounds/SBridgeTheoremC.lean` (1.9 KB): Theorem C with the model in place of the window hypothesis
* `lower/LowerBounds/SCut.lean` (8.7 KB): lemmas that put a search together from parts, `S.ref_of_cover`,
  `S.search_false`; no Mathlib
* `lower/LowerBounds/SDec.lean` (2.4 KB): the tree of used classes written as a list of large numbers, `S.trOf`; no
  Mathlib
* `lower/LowerBounds/SLit.lean` (3.4 KB): states of a search written out and compared by evaluation, `S.St.eq_of_beq`;
  no Mathlib
* `lower/LowerBounds/SModel.lean` (3.0 KB): `modelStatement_of_search`: from a search that returns false to
  `ModelStatement`
* `lower/LowerBounds/SModelDef.lean` (4.2 KB): the model that the search works on: `IsModelChain`, `ModelStatement`
* `lower/LowerBounds/SRun.lean` (1.2 KB): the run check evaluated by the kernel: `S.runSearch k = false` for k = 5 to
  15
* `lower/LowerBounds/SSearch.lean` (14.8 KB): the window search on natural numbers, `S.search`, `S.runSearch`; no
  Mathlib
* `lower/LowerBounds/SSound.lean` (46.6 KB): the search is complete: `S.wstatement_of_search`
* `lower/LowerBounds/SWord.lean` (18.1 KB): words and their codes: what the arithmetic of the search means on words
* `lower/LowerBounds/TheoremA.lean` (25.9 KB): Theorem A: `kisicBound`, `superperm_kisic_bound`, the values for k = 5
  to 14
* `lower/LowerBounds/TheoremAWords.lean` (2.4 KB): Theorem A for covering words over `Fin k`
* `lower/LowerBounds/TheoremB.lean` (5.1 KB): Theorem B: `superperm_boundB`, the values for k = 7 to 14
* `lower/LowerBounds/TheoremBCore.lean` (26.6 KB): `boundB` and the assembly of Theorem B from two lemmas taken as
  hypotheses
* `lower/LowerBounds/TheoremBWords.lean` (2.1 KB): Theorem B for covering words over `Fin k`
* `lower/LowerBounds/TheoremC.lean` (10.5 KB): Theorem C from the window hypothesis: `superperm_boundC`
* `lower/LowerBounds/TheoremCCore.lean` (29.3 KB): Theorem C: `boundC`, `ConditionsC` and the assembly
* `lower/LowerBounds/TheoremCWords.lean` (3.6 KB): Theorem C from the window hypothesis, for covering words over `Fin
  k`
* `lower/LowerBounds/WindowSlackC.lean` (3.5 KB): Theorem C: the window bound in the form with the slack of intervals
  and runs
* `lower/README.md` (29.1 KB): the three lower bounds, their values, whose the parts are, the steps of the proofs, how
  to build
* `lower/Superperm/TwoSidedA.lean` (2.9 KB): Theorem A and the literal words in one statement, n = 9, 10, 11
* `lower/Superperm/TwoSidedB.lean` (2.9 KB): Theorem B and the literal words in one statement, n = 9, 10, 11
* `lower/Superperm/TwoSidedC.lean` (3.2 KB): Theorem C and the literal words in one statement, n = 8, 9, 10, 11
* `lower/build.sh` (11.6 KB): generates the certificates of Theorem C, builds what it finds in `LowerBounds/`,
  `Audit*.lean` and `Superperm/`, checks the axioms
* `lower/certificates-large.txt` (829 B): the large certificates that `build.sh full` adds
* `lower/certificates.txt` (2.2 KB): the small certificates of Theorem C, checked at the default level: generator, k,
  cn, bn, q, options
* `lower/certificates/C14_843_63334_16000/Final_C14_843_63334_16000.lean` (1.9 KB): `covers_length_ge_93891141126`,
  `ssuper_ge_93891141126`
* `lower/certificates/C14_843_63334_16000/README.md` (3.1 KB): the certificate 14 843 63334 16000 (93,891,141,126) as
  a recipe: files, statement, axioms, cost
* `lower/certificates/C14_843_63334_16000/build.sh` (4.8 KB): generates the Lean files, checks them against
  `generated.sha256`, compiles them, writes and checks the final statement
* `lower/certificates/C14_843_63334_16000/fix_imports.py` (3.0 KB): makes each generated part import only the data
  files it uses
* `lower/certificates/C14_843_63334_16000/generated.sha256` (512.4 KB): SHA-256 of the 5,347 Lean files that
  `build.sh` generates
* `lower/certificates/C14_843_63334_16000/make_final.py` (3.1 KB): writes the final statement of a certificate from
  the head file of the generator
* `lower/generated.sha256` (45.9 KB): SHA-256 of the 435 Lean files that the generators write into the build directory
* `lower/tools/s_certs.py` (5.4 KB): writes the generated files that state the certificates (`SCertW*.lean`,
  `SCertificates*.lean`)
* `lower/tools/s_final.py` (6.0 KB): writes the generated files with the bounds (`SFinal*.lean`)
* `lower/tools/s_ksim.py` (4.7 KB): Python copy of `SSearch.lean`, used by the generators to decide where to cut
* `lower/tools/s_plan.py` (12.5 KB): generator: one search cut into lemmas for the kernel, states given as paths
* `lower/tools/s_plan2.py` (16.5 KB): generator: the same with the state of every part written out, for deep searches

## n7/

* `n7/Audit5899.lean` (5.5 KB): level 1 written out: the twelve finite statements unfolded, and the theorem from them
* `n7/Audit5899Native.lean` (1.9 KB): level 2: the final statement with no definition of this project, and the axioms
  of both levels
* `n7/Audit5899Search.lean` (4.9 KB): level 1 from twelve search equations as hypotheses, the conclusion with no
  definition of this project
* `n7/AuditN.lean` (13.1 KB): the model of standard configurations written out, and that it is exact in both
  directions
* `n7/LowerBounds/DCapacity.lean` (16.0 KB): chain lines and the capacity of a component with end prices,
  `component_capacity_D`
* `n7/LowerBounds/DJunction.lean` (19.5 KB): the prices at a junction, `junction_le_D`, and the line inequality
  `lineD_reduced`
* `n7/LowerBounds/DSearch.lean` (7.5 KB): an earlier compiled search on numbers; `PSound.lean` uses its arithmetic on
  codes of words; no imports
* `n7/LowerBounds/DSound.lean` (33.1 KB): that search is complete; `PSound.lean` uses its lemmas about class indices
  and marks
* `n7/LowerBounds/JCoverage.lean` (24.9 KB): junctions: blocks and rotation classes, free junctions, the inequality
  `budget`
* `n7/LowerBounds/JEntryTree.lean` (14.0 KB): junctions: the components of a path form a tree by their first vertices,
  `parentComp`
* `n7/LowerBounds/JLinks.lean` (16.1 KB): junctions: the cost of a junction is an overlap offset between two
  components, `theoremL`
* `n7/LowerBounds/NBlock.lean` (26.9 KB): the model on the level of blocks, `BValid`, `toConfig_valid`
* `n7/LowerBounds/NConfig.lean` (15.7 KB): the model: rows, hanging components, `NConfig`, `NConfig.Valid`,
  `NConfig.cost`
* `n7/LowerBounds/NCore.lean` (24.3 KB): the model: from the data of a path (`JoinData`) to a valid configuration
* `n7/LowerBounds/NPath.lean` (25.4 KB): the model: the components and junctions of a Hamiltonian path as `JoinData`
* `n7/LowerBounds/NRules.lean` (13.3 KB): the model: rules of every valid configuration (`free_attachment`,
  `attachment_cost_one`, `len_le`)
* `n7/LowerBounds/NT4.lean` (36.2 KB): the model: seams of type T4 are never needed, by surgery on block
  configurations
* `n7/LowerBounds/NT4Config.lean` (13.5 KB): the same as a statement about valid configurations, `exists_noT4`
* `n7/LowerBounds/NTheorem.lean` (5.5 KB): the model, lower direction: `exists_stdConfig`,
  `covers_length_gt_of_no_stdConfig`
* `n7/LowerBounds/NUpper.lean` (41.1 KB): the model, upper direction: a valid configuration is a word, `exists_word`,
  `no_stdConfig_iff`
* `n7/LowerBounds/PArith.lean` (10.3 KB): the arithmetic on the tables, by `decide +kernel`: `profile_of_family`,
  `many_chains`, the knapsack `kern`
* `n7/LowerBounds/PEnc.lean` (13.1 KB): both sets of tables of the engine satisfy `PS.Enc`: `stmt_of_searchA`,
  `stmt_of_searchB`
* `n7/LowerBounds/PF0aNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0bNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0cNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0dNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0eNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0fNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0gNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0hNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0iNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF0jNative.lean` (1.6 KB): evaluation by `native_decide`: chains, one of ten ranges of parts
* `n7/LowerBounds/PF1aNative.lean` (1.6 KB): evaluation by `native_decide`: sequences with 1 link of weight 4, one of
  two ranges of parts
* `n7/LowerBounds/PF1bNative.lean` (1.6 KB): evaluation by `native_decide`: sequences with 1 link of weight 4, one of
  two ranges of parts
* `n7/LowerBounds/PF2Native.lean` (1.5 KB): evaluation by `native_decide`: sequences with 2 links of weight 4
* `n7/LowerBounds/PF3Native.lean` (1.6 KB): evaluation by `native_decide`: sequences with 3 links of weight 4
* `n7/LowerBounds/PF45Native.lean` (1.8 KB): evaluation by `native_decide`: sequences with 5 and with 4 links of
  weight 4
* `n7/LowerBounds/PFamily.lean` (9.9 KB): families of trails: `family_le_49`, and `family_le_44` for seven or more
  trails
* `n7/LowerBounds/PFinal.lean` (9.3 KB): level 1 from search equations: `PS.Covered`, `caps_of_search`,
  `profiles_of_search`, `covers_5899_of_search`
* `n7/LowerBounds/PFinalNative.lean` (4.1 KB): level 2: `covers_lower_bound_7_native`, from the 22 evaluated equations
* `n7/LowerBounds/PGeom.lean` (14.0 KB): rows and their links: extension of a row, merge of two rows, trails, rotation
  of a list of trails
* `n7/LowerBounds/PGlue.lean` (6.9 KB): gluing trails through a junction: `path_glue`, `ring_glue`
* `n7/LowerBounds/PHanging.lean` (14.4 KB): hanging components: the family of a component `famH_spec`, its knapsack
  item `hanging_item`
* `n7/LowerBounds/PJunction.lean` (8.9 KB): the two reductions at an attachment as one notion: `junction_extLast`,
  `junction_extFirst`, `junction_merge`
* `n7/LowerBounds/PLevels.lean` (23.0 KB): the three rules are complete: shortest counterexample `seqCap_level`,
  `cycle_lemma`, `ringCap_of_stmt`, `prof_rule`
* `n7/LowerBounds/PModel.lean` (15.6 KB): the objects of the finite statements: `IsFamily`, `IsPath`, `IsRing`,
  `ChainCap`, `PathCap`, `RingCap`, `NoProfile`
* `n7/LowerBounds/PProfNative.lean` (2.3 KB): evaluation by `native_decide`: the five profile searches
* `n7/LowerBounds/PRingNative.lean` (1.6 KB): evaluation by `native_decide`: rings
* `n7/LowerBounds/PRules.lean` (29.4 KB): from a search that returns false to the finite statements:
  `seqCap_of_search`, `ringCapT_of_search`, `noProfileK_of_search`
* `n7/LowerBounds/PSearch.lean` (15.2 KB): the engine: the search on numbers and tables, `seqSearch`, `ringSearch`,
  `profSearch`; no imports; compiled to C
* `n7/LowerBounds/PSeq.lean` (15.6 KB): sequences of rows on words, `PS.IsSeq`, and what a search proves about them,
  `PS.PStmt`
* `n7/LowerBounds/PShapes.lean` (13.8 KB): the shapes of a component; the hypotheses `Caps`; `glue_path_bound`,
  `glue_ring_bound`
* `n7/LowerBounds/PSmall.lean` (2.4 KB): test: the finite statements on 5 symbols from those searches, by the theorems
  used for 7
* `n7/LowerBounds/PSmall6Search.lean` (618 B): test: one search on 6 symbols evaluated by the kernel (7.3 GB of
  memory); no Mathlib
* `n7/LowerBounds/PSmallSearch.lean` (2.9 KB): test: nine searches on 5 symbols evaluated by the kernel; no Mathlib
* `n7/LowerBounds/PSound.lean` (30.7 KB): the engine is complete for every set of tables that satisfies `PS.Enc`:
  `not_ruleAlong_of_search`
* `n7/LowerBounds/PTables.lean` (7.0 KB): generated data: the seven tables of the finite statements and four tables
  for the arithmetic; no imports
* `n7/LowerBounds/PTestNative.lean` (4.6 KB): test: 27 small searches by `native_decide`, the kernel's nine among them
  and nine with known answers
* `n7/LowerBounds/PTheorem.lean` (7.6 KB): level 1: `no_config_134` and `covers_5899_of_caps`, from the finite
  statements
* `n7/LowerBounds/PTrails.lean` (13.3 KB): the cut at heavy seams, `cutRows_spec`; at least 720 blocks; the accounting
  `acc_value`, `acc_weight`
* `n7/README.md` (23.1 KB): 5,899 for n = 7: the statement, the two levels and what each trusts, the proof, the files,
  how to build, costs
* `n7/build.sh` (17.7 KB): builds level 1, the engine and its shared library, runs the evaluations, builds the
  theorem, checks the axioms
* `n7/evaluations.txt` (952 B): the 17 evaluation modules: level of the build and the 22 equations they prove by
  `native_decide`
* `n7/sources.sha256` (7.6 KB): SHA-256 of the 79 Lean files the final theorem is compiled from (60 here, 17 of
  `lower/`, 2 of `words/`)

## n8/

* `n8/.gitattributes` (127 B): keeps LF line ends in `NOTICE.echols`
* `n8/NOTICE.echols` (3.5 KB): the `NOTICE` file of Echols's repository, unchanged
* `n8/README.md` (10.0 KB): the three variants, what replaces `native_decide`, licences, how to build
* `n8/build.sh` (7.1 KB): puts each variant together from Echols's checkout, builds it, checks the axioms
* `n8/echols-sources.sha256` (3.3 KB): SHA-256 of the 36 Lean files of Echols's repository at commit 893ab2d
* `n8/kernel/Superperm8/KCode.lean` (29.2 KB): new: codes of permutations, rotation classes and insertion blocks as
  indices
* `n8/kernel/Superperm8/KSearch.lean` (9.6 KB): new: the search on natural numbers, `K.fsearch`
* `n8/kernel/Superperm8/KSound.lean` (31.4 KB): new: `K.affine_bound_nat`, soundness of the search, and
  `K.ref_of_cover`
* `n8/tools/ksim.py` (4.8 KB): Python mirror of `KSearch.lean`, used by `plan.py`
* `n8/tools/plan.py` (10.6 KB): cuts a search into parts for the kernel and writes the Lean files
* `n8/variants/v46130k/Plain.lean` (677 B): new top file: the bound 46130 for covering words in plain form
* `n8/variants/v46130k/changes.diff` (14.3 KB): changes to Echols's files for the bound 46130, as a diff against his
  commit
* `n8/variants/v46130k/files.sha256` (3.4 KB): SHA-256 of the 38 hand-written Lean files of the variant for 46130 (his
  with the changes, and the new ones)
* `n8/variants/v46130k/generated.sha256` (271 B): SHA-256 of the parts of the search that `plan.py` writes for 46130
* `n8/variants/v46131k/Plain.lean` (677 B): new top file: the bound 46131 for covering words in plain form
* `n8/variants/v46131k/changes.diff` (35.0 KB): changes to Echols's files for the bound 46131, as a diff against his
  commit
* `n8/variants/v46131k/files.sha256` (3.4 KB): SHA-256 of the 38 hand-written Lean files of the variant for 46131 (his
  with the changes, and the new ones)
* `n8/variants/v46131k/generated.sha256` (448 B): SHA-256 of the parts of the search that `plan.py` writes for 46131
* `n8/variants/v46132bk/Plain.lean` (677 B): new top file: the bound 46132 for covering words in plain form
* `n8/variants/v46132bk/changes.diff` (35.4 KB): changes to Echols's files for the bound 46132, as a diff against his
  commit
* `n8/variants/v46132bk/files.sha256` (3.4 KB): SHA-256 of the 38 hand-written Lean files of the variant for 46132
  (his with the changes, and the new ones)
* `n8/variants/v46132bk/generated.sha256` (8.7 KB): SHA-256 of the parts of the search that `plan.py` writes for 46132

## n8_46134/

* `n8_46134/AuditD.lean` (3.5 KB): both levels restated with the definitions of `Challenge.lean` and of the
  preimage-chain library
* `n8_46134/LowerBounds/D8.lean` (8.4 KB): k = 8: `covers_boundD_8` from the three hypotheses about chains
* `n8_46134/LowerBounds/DFinal.lean` (1.9 KB): `covers_boundD_8_of_search`: the bound from the three search equations
  (level 1)
* `n8_46134/LowerBounds/DFinalNative.lean` (3.3 KB): `covers_lower_bound_8_native`, `ssuper_lower_bound_8_native`
  (level 2)
* `n8_46134/LowerBounds/DLine1Native.lean` (1.7 KB): evaluation by `native_decide`: the line 4 r <= 9 δ + 56
* `n8_46134/LowerBounds/DLine2Native.lean` (1.8 KB): evaluation by `native_decide`: the line 17 r <= 38 δ + 264
* `n8_46134/LowerBounds/DModel.lean` (8.9 KB): the hypotheses for model chains, and from them for the chains of the
  preimage-chain library
* `n8_46134/LowerBounds/DSmall.lean` (1.5 KB): `ssuper_ge_153_D`: Theorem D on 5 symbols with the kernel search
* `n8_46134/LowerBounds/DSmallSearch.lean` (631 B): a search on 5 symbols, evaluated by the kernel
* `n8_46134/LowerBounds/DTestNative.lean` (2.6 KB): small searches by the kernel and by `native_decide`, and searches
  with known answers
* `n8_46134/LowerBounds/DTheorem.lean` (5.9 KB): Theorem D for every k >= 5: `theoremD_pathwise`, `superperm_boundD`,
  `covers_length_ge_boundD`
* `n8_46134/LowerBounds/DZoneNative.lean` (2.0 KB): evaluation by `native_decide`: the zone statement
* `n8_46134/README.md` (7.0 KB): L(8) >= 46,134: the two levels, the statements and axioms, the argument, the files,
  how to build
* `n8_46134/build.sh` (10.1 KB): builds the engine, level 1, the three evaluations, the theorem and the audit; checks
  the axioms

## n8struct/

* `n8struct/N8Struct/Classify.lean` (5.8 KB): `packing_classification`: every packing is a renaming of K0 or K1
* `n8struct/N8Struct/Definitions.lean` (8.4 KB): the definitions: states, loops, rows, walks, `Q`, ports, renaming,
  reversal
* `n8struct/N8Struct/Orbits.lean` (1.1 KB): `K0_not_K1`, `stab_K0`, `stab_K1`
* `n8struct/N8Struct/PackBase.lean` (21.7 KB): placements and packings, literal tables, `placement_closed_all`,
  `placement_injective`
* `n8struct/N8Struct/Partners.lean` (3.5 KB): `partners_complete`: the 21 placements disjoint from the identity
  placement
* `n8struct/N8Struct/Published.lean` (4.0 KB): the packing of `selection-46174.txt`, its loops, the Klein group
* `n8struct/N8Struct/Reversal.lean` (3.0 KB): reversal maps the packing to the other class
* `n8struct/N8Struct/Symmetry.lean` (8.7 KB): renaming lemmas; facts about all 720 states through `forall_stateP`
* `n8struct/N8Struct/Walk27.lean` (3.1 KB): the 27-walk: closed, `Q = 16`, one closed trail of 178 slices
* `n8struct/README.md` (8.6 KB): the two facts, the definitions, the theorems with their axioms, what is not proved,
  how to build
* `n8struct/build.sh` (3.6 KB): checks Pantone's sources, runs `gen.py` and compares, builds the nine files, checks
  the axioms
* `n8struct/gen.py` (7.5 KB): recomputes the finite data with the model of `words/n8/tools` and asserts the counts
* `n8struct/gen_out.txt` (5.2 KB): output of `gen.py`: the tables, in Lean syntax
* `n8struct/gen_out2.txt` (11.5 KB): output of `gen.py`: the walk of the identity, the partner table, the covered
  loops

## tools/

* `tools/check_hashes.py` (1.5 KB): compares files with a list of SHA-256 hashes, or writes such a list
* `tools/common.sh` (8.0 KB): settings and shell functions shared by the two build scripts
* `tools/order.py` (3.4 KB): build order of Lean modules from their import lines, with a stamp per module

## words/

* `words/Audit11.lean` (1.2 KB): the statement for 11 symbols written out with no definition of this project
* `words/README.md` (20.6 KB): the statements, the two checking methods, the word files, how to build
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
* `words/Superperm/Upper8k.lean` (6.5 KB): `hasWord_eight_k : HasWord 8 46174` and `exists_word_eight_k`, and the same
  with the suffix `_<hash12>` for each of the seven ties
* `words/Superperm/UpperCyc.lean` (981 B): `hasWord_nine_cyc`, `hasWord_ten_cyc`: 9 and 10 symbols by the second
  method
* `words/Superperm/UpperHR.lean` (1.0 KB): upper bounds for `HR.Ssuper`, 7 to 9 symbols
* `words/Superperm/UpperHR10.lean` (387 B): upper bound for `HR.Ssuper 10` from rumstd's word
* `words/Superperm/UpperHunter.lean` (956 B): `Hunter.Ssuper k <= ...` for 7, 8, 9 symbols
* `words/Superperm/UpperHunter10.lean` (377 B): `Hunter.Ssuper 10 <= 4034873`
* `words/Superperm/UpperHunter10b.lean` (394 B): `Hunter.Ssuper 10 <= 4034855`
* `words/Superperm/UpperHunter11.lean` (430 B): `Hunter.Ssuper 11 <= 43930578`
* `words/build.sh` (10.3 KB): generates the certificates, builds everything from sources and prints the axioms
* `words/check_word.sh` (10.5 KB): one command from a word file to the Lean theorem for that word
* `words/gen.py` (11.4 KB): generator of the first method: one table entry for every permutation
* `words/gen11.py` (17.0 KB): generator of the second method: one table entry for every rotation class
* `words/gen12.py` (20.3 KB): generator of the second method for n = 12 (blocks checked one by one, groups two levels
  deep)
* `words/generated.sha256` (36.2 KB): SHA-256 of all 395 files that the generators write
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
* `words/generated/Superperm/N8k/B000.lean` (47.1 KB): generated by `gen11.py`: blocks of a word on 8 symbols of
  46,174 letters
* `words/generated/Superperm/N8k/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols, 46,174 letters
* `words/generated/Superperm/N8k/P000.lean` (27.2 KB): generated by `gen11.py`: tables and kernel checks, 8 symbols
* `words/generated/Superperm/N8k/Tree.lean` (881 B): generated by `gen11.py`: the tree of blocks, `W` and `tree_ok`, 8
  symbols
* `words/generated/Superperm/N8k/modules.txt` (20 B): generated by `gen11.py`: the modules of this directory in build
  order
* `words/generated/Superperm/N8k_1746523ff629/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_1746523ff629/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_1746523ff629/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_1746523ff629/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_1746523ff629/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_24efc13a6b92/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_24efc13a6b92/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_24efc13a6b92/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_24efc13a6b92/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_24efc13a6b92/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_3677542ddb4f/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_3677542ddb4f/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_3677542ddb4f/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_3677542ddb4f/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_3677542ddb4f/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_510faf236ad6/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_510faf236ad6/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_510faf236ad6/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_510faf236ad6/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_510faf236ad6/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_6b1c42e70199/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_6b1c42e70199/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_6b1c42e70199/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_6b1c42e70199/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_6b1c42e70199/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_b9001a0c8fdf/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_b9001a0c8fdf/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_b9001a0c8fdf/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_b9001a0c8fdf/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_b9001a0c8fdf/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
* `words/generated/Superperm/N8k_e45fecc9625b/B000.lean` (47.2 KB): generated by `gen11.py`: blocks of a word on 8
  symbols of 46,174 letters
* `words/generated/Superperm/N8k_e45fecc9625b/Main.lean` (1.3 KB): generated by `gen11.py`: `hasWord` for 8 symbols,
  46,174 letters
* `words/generated/Superperm/N8k_e45fecc9625b/P000.lean` (27.3 KB): generated by `gen11.py`: tables and kernel checks,
  8 symbols
* `words/generated/Superperm/N8k_e45fecc9625b/Tree.lean` (941 B): generated by `gen11.py`: the tree of blocks, `W` and
  `tree_ok`, 8 symbols
* `words/generated/Superperm/N8k_e45fecc9625b/modules.txt` (20 B): generated by `gen11.py`: the modules of this
  directory in build order
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
* `words/inputs8k.tsv` (1.7 KB): the eight words of 46,174 letters: certificate name, word file, SHA-256 of the
  letters and of the file
* `words/preimage-sources.sha256` (8.0 KB): SHA-256 of the 76 files of the preimage-chain project that are compiled
* `words/verify_blocks.py` (2.7 KB): checks that the blocks of a `gen11.py` certificate spell a word file
* `words/verify_blocks12.py` (3.2 KB): checks that the blocks of a `gen12.py` certificate spell a word file
* `words/verify_word.py` (2.6 KB): checks that the number `W` of a `gen.py` certificate spells a word file
* `words/word_info.py` (4.6 KB): symbols, length, hash and run structure of a word, for `check_word.sh`

## words12/

* `words12/Audit12.lean` (1.8 KB): the statements for n = 12 written out with no definition of this project
* `words12/README.md` (8.8 KB): the statements for n = 12, what differs from n = 11, how to build
* `words12/Superperm/TwoSided12.lean` (1.1 KB): lower and upper bound in one statement for n = 12, with Liu's lower
  bound
* `words12/Superperm/TwoSidedAB12.lean` (2.1 KB): the same with the lower bounds of Theorems A and B
* `words12/Superperm/TwoSidedC12.lean` (1.4 KB): the same with the lower bound of Theorem C
* `words12/Superperm/Upper12.lean` (1.3 KB): `hasWord_twelve : HasWord 12 522737175`
* `words12/Superperm/UpperHunter12.lean` (433 B): `Hunter.Ssuper 12 <= 522737175`
* `words12/build.sh` (4.7 KB): runs `check_word.sh` on the word for n = 12, builds the statements, prints the axioms
* `words12/generated.sha256` (23.0 KB): SHA-256 of the 255 files that `gen12.py` writes for this word
