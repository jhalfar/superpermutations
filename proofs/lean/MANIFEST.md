# Files of this directory

Every file, with its size and one line on what it is. "generated" means written by a script of this
directory from public input files; the build scripts write these files again and compare.

## Scripts that are run directly

These files should have the executable bit (mode 755) in the repository. Everything else is read by
them, by `python3` or by Lean, and needs mode 644 only.

* `constant/build.sh`
* `lower/build.sh`
* `n8/build.sh`
* `words/build.sh`
* `words/check_word.sh`
* `words12/build.sh`

## Top level

* `.gitattributes` (344 B): keeps LF line ends in text files, so that the hashes hold on every system
* `MANIFEST.md`: this list
* `README.md` (23.7 KB): what is proven, what a build needs, how to build, what it costs, what is trusted
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
* `lower/README.md` (28.7 KB): the three lower bounds, their values, whose the parts are, the steps of the proofs, how
  to build
* `lower/Superperm/TwoSidedA.lean` (2.9 KB): Theorem A and the literal words in one statement, n = 9, 10, 11
* `lower/Superperm/TwoSidedB.lean` (2.9 KB): Theorem B and the literal words in one statement, n = 9, 10, 11
* `lower/Superperm/TwoSidedC.lean` (3.2 KB): Theorem C and the literal words in one statement, n = 8, 9, 10, 11
* `lower/build.sh` (11.6 KB): generates the certificates of Theorem C, builds what it finds in `LowerBounds/`,
  `Audit*.lean` and `Superperm/`, checks the axioms
* `lower/certificates-large.txt` (829 B): the large certificates that `build.sh full` adds
* `lower/certificates.txt` (2.2 KB): the small certificates of Theorem C, checked at the default level: generator, k,
  cn, bn, q, options
* `lower/generated.sha256` (45.9 KB): SHA-256 of the 435 Lean files that the generators write into the build directory
* `lower/tools/s_certs.py` (5.4 KB): writes the generated files that state the certificates (`SCertW*.lean`,
  `SCertificates*.lean`)
* `lower/tools/s_final.py` (6.0 KB): writes the generated files with the bounds (`SFinal*.lean`)
* `lower/tools/s_ksim.py` (4.7 KB): Python copy of `SSearch.lean`, used by the generators to decide where to cut
* `lower/tools/s_plan.py` (12.5 KB): generator: one search cut into lemmas for the kernel, states given as paths
* `lower/tools/s_plan2.py` (16.5 KB): generator: the same with the state of every part written out, for deep searches

## n8/

* `n8/.gitattributes` (127 B): keeps LF line ends in `NOTICE.echols`
* `n8/NOTICE.echols` (3.5 KB): the `NOTICE` file of Echols's repository, unchanged
* `n8/README.md` (10.1 KB): the three variants, what replaces `native_decide`, licences, how to build
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
* `words12/README.md` (7.9 KB): the statements for n = 12, what differs from n = 11, how to build
* `words12/Superperm/TwoSided12.lean` (1.1 KB): lower and upper bound in one statement for n = 12, with Liu's lower
  bound
* `words12/Superperm/TwoSidedAB12.lean` (2.1 KB): the same with the lower bounds of Theorems A and B
* `words12/Superperm/TwoSidedC12.lean` (1.4 KB): the same with the lower bound of Theorem C
* `words12/Superperm/Upper12.lean` (1.3 KB): `hasWord_twelve : HasWord 12 522737175`
* `words12/Superperm/UpperHunter12.lean` (433 B): `Hunter.Ssuper 12 <= 522737175`
* `words12/build.sh` (4.7 KB): runs `check_word.sh` on the word for n = 12, builds the statements, prints the axioms
* `words12/generated.sha256` (23.0 KB): SHA-256 of the 255 files that `gen12.py` writes for this word
