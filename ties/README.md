# Words of record length

For n = 7, 8, 9 and 10 more than one word of the shortest known length has been published. This directory lists the
ones I know, says which of them are the same word written differently, and measures how far apart the others are.

| n | length | different words | first published by |
|---|---|---|---|
| 7 | 5,905 | 98 | Andrei Teodorescu 12, Theo H. 1, this repository 85 |
| 8 | 46,181 | 26 published, 1,223 with all rotations | Jay Pantone 1, Theo H. 25 |
| 9 | 408,731 | 1 | rumstd |
| 10 | 4,034,855 | 2 | this repository 1, Theo H. 1 |

For n = 8 the table is about 46,181, the record length of early October. Shorter words have been found since: my
46,174 with seven ties ([`../words/n8/`](../words/n8/README.md)) and Theo H.'s 46,173. They are not in this
directory.

Two words count as the same if one becomes the other after renaming the symbols, reversing the word or both. I
call such a set of words a class.

## Files

| file | content |
|---|---|
| `classes.tsv` | one line per class: who published it first and when, the counts described below, and the SHA-256 of its canonical word |
| `sources.tsv` | every published file I compared (58 files): its class, where it is and the SHA-256 of the word in it |
| `7/` | the 85 words on 7 symbols that are first published here, one per file, in canonical form |
| `neighbours-7.tsv` | for every pair of the 98 classes on 7 symbols: the number of steps in which they differ |
| `rotations-8-46181.tsv` | the 1,223 classes on 8 symbols: canonical hash, the closed path it comes from and its class if it has been published |
| `classes.py`, `neighbours.c`, `summary.py`, `rotations.py`, `cmp10.py` | the programs that made the tables |

Words of other people are not copied here. `sources.tsv` gives the place and a hash for each of them.

The canonical word of a class: rename the symbols to 1, 2, 3, ... in order of first appearance, do the same for the
reversed word, and keep the one whose SHA-256 is smaller. The files in `7/` hold exactly that word, so the hash in
`classes.tsv` is the hash of the file without its line end.

## How two words are compared

A word visits the n! permutations in the order of their first occurrence. A step is a pair of consecutive
permutations in that order, and its weight is the number of letters the second one adds. Two words on the same
symbols differ in d steps if d steps of one are not steps of the other. `neighbours.c` tries every renaming and both
directions and reports the smallest d.

For each class `classes.tsv` also gives the number of steps of each weight, the lengths of the runs of weight-1
steps and the number of windows that repeat a permutation.

## n = 7: 98 words in 8 groups

Andrei Teodorescu posted four words of 5,905 letters on 18 August 2026. They are two classes: the third file is the
first one reversed and renamed, and the fourth is the second. On 24 August he posted ten more, made from the first
two by moving a block of 7 letters, which repeats a permutation. Theo H. added one class on 8 October 2026 in a pull
request to the superpermutators corpus. The other 85 come from a search of mine that replaces the first or the
last chain of the kernel of Teodorescu's words and keeps the length. Inside the kernel that search found nothing to
replace.

All 98 are close to one another. Every word has another one at 3 steps, and the two farthest differ in 217 of
5,039 steps. Linking words that differ in at most 12 steps gives 8 groups, named A to H in `classes.tsv`. Different
groups are at least 55 steps apart:

|   | A | B | C | D | E | F | G | H |
|---|---|---|---|---|---|---|---|---|
| words | 25 | 25 | 10 | 10 | 10 | 10 | 4 | 4 |
| A | . | 96 | 151 | 55 | 55 | 151 | 208 | 112 |
| B | 96 | . | 55 | 151 | 151 | 55 | 112 | 208 |
| C | 151 | 55 | . | 210 | 96 | 114 | 57 | 153 |
| D | 55 | 151 | 210 | . | 114 | 96 | 153 | 57 |
| E | 55 | 151 | 96 | 114 | . | 210 | 153 | 57 |
| F | 151 | 55 | 114 | 96 | 210 | . | 57 | 153 |
| G | 208 | 112 | 57 | 153 | 153 | 57 | . | 96 |
| H | 112 | 208 | 153 | 57 | 57 | 153 | 96 | . |

Teodorescu's first word and five of his variants are in A, his second word and the other five in B, and Theo's
word is in A. The groups pair up: A with B, C with E, D with F and G with H are each 96 steps apart and have the
same number of steps of each weight. Groups of different pairs are at least 55 steps apart. The words have
between 0 and 4 repeated permutations.

None of these words can be read as a closed path at the same length: joining the last permutation to the first
costs 6 or 7 letters, and no step of the words weighs more than 4.

## n = 8: closed paths and their rotations

The last permutation of Jay Pantone's word of 46,181 letters is joined to the first by a step of weight 3. So his
path is closed, and cutting it at any of its 815 steps of weight 3 gives another word of the same length. These 816
words are 408 classes, each met twice.

Theo H. published 25 further classes on 8 October 2026. 23 of them are rotations of Pantone's closed path. His
word 26 is another closed path, with 813 steps of weight 3 where Pantone's has 815, and its rotations are 814
classes. His word 16 differs from Pantone's word in 3 steps and is not a rotation of it; its own rotations are the
408 classes again. That makes 408 + 814 + 1 = 1,223 classes of 46,181 letters. `rotations-8-46181.tsv` lists
them, and `rotations.py` writes them out from the three published words.

The words for n = 9 and n = 10 do not close: the closing step costs 8 and 10 letters, more than any step in them.

## n = 9 and n = 10

For n = 9 there is one class, rumstd's word of 2 October 2026. The corpus of Theo H. holds it twice with the symbols
1 to 9. One of the two files has my name in its file name, but it is rumstd's word.

For n = 10 there are two classes. Theo's second word of 4,034,855 letters is the word of this repository with three
steps exchanged: steps of weight 3, 3 and 5 are replaced by steps of weight 3, 4 and 4. `cmp10.py` shows it.

## Running the programs

```
python classes.py LIST.tsv OUT.tsv                  # LIST.tsv: n <tab> label <tab> file
gcc -O3 -fopenmp -o neighbours neighbours.c
./neighbours 7 WORDS.txt > PAIRS.txt                # WORDS.txt: one word per line, symbols 1 to 7
python summary.py 7 PAIRS.txt NAMES.tsv OUT.tsv     # NAMES.tsv: class <tab> label, one line per word
python rotations.py 8 WORD.txt --classes            # closing step, equal cuts and their classes
python cmp10.py A.txt B.txt                         # the steps in which two words on 10 symbols differ
```

`neighbours` took 21 minutes on 4 threads for the 4,753 pairs on 7 symbols.
