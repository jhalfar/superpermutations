# n = 9: 408,731 cannot be beaten with Pantone's trails in three families of words

rumstd's n = 9 word has 408,731 letters. It is made of the 52 closed trails of Jay Pantone's word of 408,732
letters, cut and joined in another way. The two scripts here check, by exhaustive computation in integers, that no
word made from these 52 trails is shorter, in three families of words:

| family | cuts | overlap of two pieces | script | time |
|---|---|---|---|---|
| one cut per trail | at steps of weight 3 or 2, or dropping one occurrence of a duplicated permutation | at most n - 3 = 6 letters | `check9s.py` | 10 s |
| one cut per trail, cuts inside a 1-cycle allowed | at any step | at most n - 1 = 8 letters | `check9s.py --wide` | 3 min |
| any number of cuts per trail (a trail may be written in several parts) | as in the first row | at most 6 letters | `check9m.py` | 3 s |

rumstd's word belongs to all three families, so in each of them 408,731 is the optimum. The scripts call the first
two families "single-port", narrow and wide, and the third "multi-port".

This is a statement about one construction. It says that the tools in this repository, which only cut and join
Pantone's trails in these ways, cannot find a shorter n = 9 word. It is not a lower bound for superpermutations.
The fourth family, several cuts per trail together with the long overlaps, is open, and so is every set of trails
other than Pantone's.

The result is checked by computation and by me. Nobody else has read the argument or written the search a second
time. Please treat it as unrefereed.

## Running the checks

    python check9s.py superpermutation-9-408732.txt [superpermutation-9-408731.txt]
    python check9s.py superpermutation-9-408732.txt [superpermutation-9-408731.txt] --wide
    python check9m.py superpermutation-9-408732.txt [superpermutation-9-408731.txt]

The first argument is Pantone's word, `words/9/superpermutation-9-408732.txt` in his repository (SHA-256
`6b5f22010b002373c6cc1db3ed4e3e9d10fe48a4cfca19568f87253c6e846a96`). The optional second argument is a word of the
family, rumstd's for example. The script then checks that it is made of the same trails and that its length is the
bound.

The scripts need Python 3 and `numpy`. They use no solver and no other file of this repository. Each prints the
facts it verifies and ends with the line that states the bound.

## The argument

It is written out in full at the top of each script. In short, for one cut per trail:

Count in half letters. For two cuts x and y of different trails let W(x, y) be twice the cost of joining the piece
that ends at x to the piece that starts at y, plus the costs of the two cuts. Twice the cost of a word is the sum of
W over its joins, plus the cut costs at the two ends.

The 52 trails are 48 small ones with 56 cuts each and 4 big ones. The script verifies, over all pairs of cuts:

1. W is at least 6 between two small trails.
2. A sequence of small trails with W at most 7 between neighbours has at most 6 trails.
3. A block of big trails between two small trails costs at least 8 in total, and at least 1 at an end of the word.

So the 48 small trails fall into at least 8 runs, the joins inside runs cost at least 6 each and the joins between
runs at least 8 each. That gives twice the cost at least 296, so the cost is at least 148 and the word has at least
408,730 letters.

Equality would force exactly 8 runs of 6 trails with W = 6 inside, W = 8 between them, and every block of big
trails at exactly 8. The script lists all such runs (336 of them, on 56 sets of 6 trails), finds the 56 ways to
split the 48 small trails into 8 of these sets, and searches every order of every split with the big trails placed
between them. No order exists. So the cost is at least 149 and the word has at least 408,731 letters.

The case with several cuts per trail (`check9m.py`) needs more: joins between two parts of the same trail, and two
potential functions on the cuts of the big trails. The script states and verifies each step.

`test_b.py` compares the fast computations of `check9m.py` with plain matrices on a sample, and `test_e4.py` checks
that the final search does find solutions as soon as one of its conditions is dropped. Both take the base word as
their only argument and must lie next to `check9m.py`.

## What it means for the tools

Relocation, segment insertion and loop moves as they are in `tools/` produce words of the third family. At n = 9
they cannot go below 408,731. A shorter n = 9 word from Pantone's construction needs the long overlaps together
with trails written in several parts, or a different set of trails.

For n = 10 and n = 11 the same method gives bounds that are not tight: at least 4,034,835 letters against rumstd's
4,034,873, and at least 43,930,420 against my 43,930,614 for one cut per trail (43,930,373 with several). Those
computations are not in this directory.
