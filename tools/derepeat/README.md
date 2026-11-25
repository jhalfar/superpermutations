# derepeat

`derepeat` removes eligible repeated permutation windows from a
superpermutation without changing its length. This C implementation applies the local move
to adjacent pairs `p p` when a compatible window is available. The JSON
report gives the remaining repeat count as `extra_copies`. A result is
repeat-free when that count is zero.

## Build and run

Build with GCC and OpenMP on a 64-bit POSIX system or on Windows with
MinGW-w64. Run these commands from the repository root.

```sh
gcc -std=c11 -O3 -Wall -Wextra -Wpedantic -fopenmp -o derepeat tools/derepeat/derepeat.c
./derepeat 9 012345678 word.txt result.txt --threads 4
./derepeat 9 012345678 result.txt --check --threads 4
```

Input is a regular file with the raw letters on one line. An optional final
LF or CRLF is ignored. Give the alphabet explicitly and use a new output
path. The tool checks complete coverage, equal length and the expected
reduction in repeat count before keeping the output. The supported range
is n = 3 through 14. Memory scales with the
number of permutations and repeated types. For n = 14, the two permutation
bitmaps alone take about 20.3 GiB, in addition to the mapped input and
working data. The tool reads raw words. Decode Detour archives first.

## How the move works

Write a repeated permutation as $`p=aub`$, with a middle $`u`$ of length
$`n-2`$. Look for an occurrence of $`u`$ with left flank different from
$`a`$ and right flank different from $`b`$. Keep at least one copy of the
opposite permutation $`bua`$. If the two copies of $`p`$ are adjacent, the
tool moves letters from the second copy to the compatible occurrence.
The number of letters stays fixed and one copy of $`p`$ disappears.

There is also an exact criterion for the broader fixed-factor problem.
Let $`m(p)`$ count the copies of $`p`$ and $`S(p)`$ count the occurrences
of $`u`$ with both flank conditions. At an endpoint, a missing flank
counts as different. A repeat-free word with the same counts of factors
of lengths $`n-2`$ and $`n-1`$ is possible exactly when
$`S(p) \ge m(p)`$ for every repeated permutation. Fixing the
length-$`(n-1)`$ factor counts and one length-$`(n-2)`$ endpoint also
fixes the length-$`(n-2)`$ factor counts. The C program applies the
adjacent-pair case of the construction. A residual repeat in its output
may require three separated occurrences of the middle or a different
choice of edit.

The endpoint matters. The n = 3 words `00102101120120` and
`20120010210112` have the same length and the same two-letter factor
counts. The first repeats `120` and fails the fixed-factor test. The
second contains all six permutations exactly once.

The C program reproduces these published repeat-free words byte for byte.

| Input | Output | Extra copies removed |
| --- | --- | ---: |
| [W-0078](https://superpermutations.com/w/W-0078), Tholsh | [W-0080](https://superpermutations.com/w/W-0080) | 56 |
| [W-0038](https://superpermutations.com/w/W-0038), rumstd | [W-0081](https://superpermutations.com/w/W-0081) | 336 |
| [W-0062](https://superpermutations.com/w/W-0062), Jakub Halfar | [W-0082](https://superpermutations.com/w/W-0082) | 2,349 |
| [W-0160](https://superpermutations.com/w/W-0160), Jay Pantone | [W-0163](https://superpermutations.com/w/W-0163) | 177,567 |

Jay Pantone published the first three repeat-free words in this table.

For the distinction between a repeat-free word and the overlap-graph representation, see
[Robin Houston's October 2018 explanation](https://groups.google.com/g/superpermutators/c/j5y24bOemiM/m/vSE2s7y5BQAJ)
and the [January 2020 discussion](https://groups.google.com/g/superpermutators/c/_J3ikawWiMI).
