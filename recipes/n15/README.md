# A superpermutation on 15 symbols from selection C (a recipe)

A word of 1,401,325,413,744 letters on the alphabet `0123456789ABCDE` that contains all 1,307,674,368,000
permutations of 15 symbols. SHA-256 of the word (no line feed):
`63cc507edaf413cfe3cda781be892688a33127b961aa22958b6bc740e9e82eaf`.

Theo H. (Tholsh) published the first recipe for n = 15 on 2026-10-25, a word of 1,401,326,497,322 letters
(github.com/Tholsh), by lifting my n = 14 plan with fewer choices for the openings. This word lifts the same plan, with the openings chosen at every full row by an exact dynamic programme and
a relocation search on top. It is 1,083,578 letters shorter than his.

The word would take 1.4 TB, so it is not stored. `gen16.c` writes it from three things:

* the selection C on 11 symbols, the same file as for n = 14 (`arrange/data/n12t-selection.txt.xz` of this
  repository; `check.sh` checks the SHA-256 of its text,
  `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`);
* `n15_1401325413744_on_selC.uplan.xz`, the unit plan: 792,000 lines, one per closed trail on 14 symbols (SHA-256 of
  the unpacked text `dec5081dc99e37c316fcad828e3ae6a273e47a6d7f16f7491ec75ff01fd3047f`);
* `gen16.c`, the generator (C, standard library only; `gen16 plan 3 SEL PLAN` is n = 12 + 3). It builds the walks of
  the selection, transports them three times and completes them (Jay Pantone's construction), then writes the
  closed trails unit by unit in the order and with the cuts of the plan, and overlaps consecutive units as far as
  their letters agree (at most 12 letters).

The plan was made from my n = 14 plan of 93,904,804,425 letters (the earlier recipe in `recipes/n14/`, in the git
history): its order of the closed trails became the order of the n = 15 units, every opening was chosen again by an
exact dynamic programme (1,401,325,415,636 letters), and my relocation search then ran for 40 minutes
(1,892 letters fewer).

```sh
bash check.sh            # generates the word and checks every permutation (gen16c, 2 check workers)
bash check.sh check 4    # the same with 4 check workers
bash check.sh count      # length and SHA-256 only (gen16, one thread)
```

`check` needs gcc, xz and about 6 GB of memory. `gen16c` spells the word block by block and hands the blocks to the
group check without storing them. It does not keep a table of all 15! permutations. Every permutation belongs to one
group (a 2-loop of the construction with a fixed satellite letter), there are 13! groups, and a group's bit is set
only after all 15 * 14 of its members have been seen among the windows of the word. The word contains every
permutation exactly when all 13! bits are set. Nothing about the construction or the plan is trusted. On the words
for n = 10 to 14 this check agrees with a plain one, and it fails on every word with one permutation removed.

My run (2026-10-25, 4 threads: the generator, a SHA-256 thread and 2 check workers): length 1,401,325,413,744, the
SHA-256 above, 1,307,674,368,000 distinct permutations, none missing, 1,307,909,433,600 permutation windows (so
235,065,600 repeats), 1,302 seconds, 5.6 GB. The run of `check.sh` in this folder, under Linux (WSL) with 4 threads,
printed the same length, SHA-256 and counts, `"valid":true` and the final OK line, in 924 seconds.

Plan lines: `D d g a j` is a small unit (loop d without a row, in file order; letter 10 inserted before its letter
g, letter 11 before position a; its 12 small trails cut at the rotations j to j+11). `W w i0 way` is a walk unit
(walk w of the three transports, in the order: walks of the selection by first row, transport orbits by first port,
three times; cut at its full row i0, way 0 or 1). Length = sum R + 12 + 11 per small unit + 12 per walk unit + the
sum over joins of (12 - overlap), with sum R = 15! + 14! + 13! + 235,065,600 = 1,401,314,745,600.

| file | what |
|---|---|
| `check.sh` | builds, checks the hashes of the selection and the plan, generates the word and checks it |
| `n15_1401325413744_on_selC.uplan.xz` | the unit plan (623 KB) |
| `gen16.c` | the streaming generator (n = 12 + L for L = 0..4) |
| `gen16c.c`, `gcore.h` | generator and group check in one process |
| `gpusink.h` | optional card path of `gen16c` (`--gpu I/K`); `check.sh` does not use it |
| `SHA256SUMS` | hashes of the files above |

The construction (slices, transport, completion, closed trails) is Jay Pantone's
(jaypantone/superperm-upper-43-80, Apache License 2.0). William Echols first published the 2-lift of a selection as a
recipe, and Theo H. the first recipe for n = 15. Selection C, the n = 14 plan, the lift and the plan of this word
are mine. The code was written with Claude in Claude Code.
