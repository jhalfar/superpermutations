# A superpermutation on 14 symbols from selection C (a recipe)

A word of 93,904,804,425 letters on the alphabet `0123456789ABCD` in which every one of the 87,178,291,200
permutations of 14 symbols occurs. SHA-256 of the word (no line feed):
`3b1470a204854ce09654b9d9a811b8455308212b29585accc29d0263e423ab6f`. It is 91 letters shorter than William
Echols's word of 93,904,804,516 letters (2026-10-19), and 131,607 shorter than his earlier 93,904,936,032
(2026-10-17). I found it on 2026-10-18.

The word is not stored here, it would take 94 GB. `gen14.c` writes it from three things:

* the selection C on 11 symbols (362,880 rows: 267,792 full, 89,040 short, 6,048 loops without a row). It is the
  file `arrange/data/n12t-selection.txt.xz` of this repository; `decode.sh` checks the SHA-256 of its text,
  `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a`.
* `n14_93904804425_on_selC.uplan.xz`: the unit plan, 72,000 lines, one per closed trail on 13 symbols, with a line
  `# expect length L sha256 H` that `gen14` checks after it has written the word.
* `gen14.c`: the generator (C, standard library only). It builds the walks of the selection, transports them twice
  and completes them (Jay Pantone's construction), then writes the closed trails unit by unit in the order and with
  the cuts of the plan, overlapping consecutive units as far as their letters agree (at most 11 letters).

```sh
bash decode.sh n14_93904804425_on_selC.uplan.xz check      # streams the word into vfast
bash decode.sh n14_93904804425_on_selC.uplan.xz word.txt   # writes the word (94 GB); "-" writes to standard output
```

`check` needs gcc, xz and 11 GB of memory, and takes about an hour (56 minutes on my machine). The alphabet is `0123456789ABCD`; `--alpha`
in `gen14` changes it. `vfast.c` is `src/verify_stream.c` without atomic operations (one thread, batched
prefetch): it marks every window of 14 distinct symbols in a table of 14! bits and exits with 0 only if all
87,178,291,200 permutations occur.

Plan lines: `D d g j` is a small unit (loop d without a row, in file order; letter 10 inserted before its letter g;
its 11 small trails cut at the rotations j to j+10), `W w i0 way` a walk unit (walk w of the two transports, in the
order: walks of the selection by first row, transport orbits by first port, twice; cut at its full row i0, way 0
or 1). Length = 93,903,902,400 + 11 + 10 per small unit + 11 per walk unit + the sum over joins of
(11 - overlap).

Credits. The construction (slices, transport, completion, closed trails) is Jay Pantone's
(jaypantone/superperm-upper-43-80). Publishing the 2-lift of a selection as a recipe, and the word of
93,904,936,032 letters that this one is compared with, are William Echols's (2026-10-17); `gen14 echols` writes his
word exactly (SHA-256 `b45da5102bfd8397fa88e77a17eebe03e29a10f70bd61c35ef42b1723feece13`). Selection C and the order
of the units, taken from my n = 12 and n = 13 plans on C, are mine.
