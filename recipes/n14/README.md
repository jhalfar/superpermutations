# A superpermutation on 14 symbols from selection C (a recipe)

A word of 93,904,804,405 letters on the alphabet `0123456789ABCD` that contains all 87,178,291,200 permutations of
14 symbols. SHA-256 of the word (no line feed):
`5eebd12aa5f4fcf1851bfbcfb0aa0ffeb860b68d265fb1be9c3321a121357a92`. It is 111 letters shorter than William
Echols's word of 93,904,804,516 letters (2026-10-19) and 131,627 shorter than his earlier 93,904,936,032
(2026-10-17). I found the plan on 2026-10-25 by running my relocation search (the block move of Echols and Theo H. on
the units, with the openings chosen again) on my earlier plan, which gave 93,904,804,425: 20 letters fewer, in 48
seconds. That earlier recipe is no longer in this folder (it is in the git history).

The word would take 94 GB, so it is not stored here. `gen14.c` writes it from three things:

* the selection C on 11 symbols (362,880 loops: 267,792 with a full row, 89,040 with a short row, 6,048 without a row). This is the
  file `arrange/data/n12t-selection.txt.xz` of this repository; `decode.sh` checks the SHA-256 of its text,
  `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`.
* `n14_93904804405_on_selC.uplan.xz`, the unit plan: 72,000 lines, one per closed trail on 13 symbols, and a line
  `# expect length L sha256 H` that `gen14` checks after it has written the word.
* `gen14.c`, the generator (C, standard library only). It builds the walks of the selection, transports them twice
  and completes them (Jay Pantone's construction). Then it writes the closed trails unit by unit in the order and
  with the cuts of the plan, and overlaps consecutive units as far as their letters agree (at most 11 letters).

```sh
bash decode.sh n14_93904804405_on_selC.uplan.xz check      # streams the word into vfast
bash decode.sh n14_93904804405_on_selC.uplan.xz word.txt   # writes the word (94 GB); "-" writes to standard output
```

`check` needs gcc, xz and 11 GB of memory, and takes about an hour on one thread (66 minutes in my last run, which printed MATCH). The alphabet is
`0123456789ABCD`; `--alpha` in `gen14` changes it. `vfast.c` is my streaming checker with the atomic operations
taken out (one thread, batched prefetch). It marks every window of 14 distinct symbols in a table of 14! bits and
exits with 0 only if all 87,178,291,200 permutations occur.

I no longer ship the `splan/1` file of my checker bot (github.com/jhalfar/superpermutations-bot) for this word; I have
not made one for it. The unit plan above is the recipe.

Plan lines: `D d g j` is a small unit (loop d without a row, in file order; letter 10 inserted before its letter g;
its 11 small trails cut at the rotations j to j+10). `W w i0 way` is a walk unit (walk w of the two transports, in
the order: walks of the selection by first row, transport orbits by first port, twice; cut at its full row i0, way
0 or 1). Length = 93,903,902,400 + 11 + 10 per small unit + 11 per walk unit + the sum over joins of
(11 - overlap).

The construction (slices, transport, completion, closed trails) is Jay Pantone's
(jaypantone/superperm-upper-43-80). William Echols first published the 2-lift of a selection as a recipe, and the
words of 93,904,936,032 and 93,904,804,516 letters that this one is compared with are his; `gen14 echols` writes the
first exactly (SHA-256 `b45da5102bfd8397fa88e77a17eebe03e29a10f70bd61c35ef42b1723feece13`). Selection C and the order of
the units, taken from my n = 12 and n = 13 plans on C, are mine.
