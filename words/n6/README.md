# All minimal superpermutations on 6 symbols

`minimal-6-872.txt.xz` has 45,116 lines. Each is a word of 872 letters over `123456` that starts with `123456` and
contains all 720 permutations. Every minimal superpermutation for n = 6 (L(6) = 872) is one of these words after its
letters are renamed, and these are all of them. SHA-256 of the unpacked list (LF line ends):
`6683584162fbb8acbefeebf46c50c136b4613c0b110e9ef0c1192def74358b5f`.

| count | |
|---|---:|
| up to relabelling (the lines) | 45,116 |
| all strings | 32,483,520 |
| up to reversal alone | 16,241,760 |
| up to relabelling and reversal | 22,560 |
| words equal to their own reversal up to relabelling | 4 |
| palindromes | 0 |
| words with a repeated permutation | 40 (36 with one permutation twice, 4 with two) |

In each of the 40 words with a repeat, the two copies of a repeated permutation are 6 letters apart.

The list contains all 44,120 words of Robin Houston's four classes (Greg Egan's files `872-treelike`, `-slack1`,
`-slack2` and `872-nonstandard`: 42,288, 772, 36 and 1,024 words) and 996 words that are in none of them: 956 without
a repeat and the 40 with one. The list is the same as Vlad Gheorghe's provisional
census of 11 August 2026 (the canonical catalogue in his attachment to the group thread, 45,116 words): every word of
either list is in the other after relabelling, so the counts 45,116, 22,560 and 40 (36 + 4) agree too.

```sh
python3 check_n6.py      # each line is a superpermutation of length 872; prints the counts above and the SHA-256
```

`check_n6.py` checks the words, but it cannot check that the list is complete. Completeness is the following
argument.

## How the list was made

A minimal word is the spelling of a Hamiltonian path through the 720 permutations of total weight 866. In my
model (the one behind the Lean lower bounds of `proofs/lean/n7/`), such a path gives a standard configuration with the
same blocks, entries and rows and defect at most 5. The defect part of that statement is in Lean
(`exists_stdConfig_of_covers`). The part about keeping the same entries and rows is proved on paper only. The
enumeration then has two stages:

1. every set of chains and loops that a configuration of defect at most 5 can have, up to relabelling, pruned with
   exact capacity tables and a bound on the links between chains (46,798 candidates);
2. for each candidate, a depth-first search over all Hamiltonian paths with those entries and rows and weight at
   most 866.

The second stage found 45,116 distinct words. Two separate programs did the work. Program A (a stage 1 and a
stage 2 in C) and program B (a stage 1 in Python, written independently from the model, and a separate stage 2 in
C) give the same 45,116 words. At n = 4 and n = 5 the same programs give 1 and 8 words, as known. The programs and the
written reduction are not in this repository yet. They will come with the Lean version of this enumeration.

The work was done with Claude in Claude Code (2026-10-26 and 27).
