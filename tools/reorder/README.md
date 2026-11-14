# The cut-opening reorder

This is my rebuild of the move Jay Pantone describes in his notes to W-0107 and W-0108 on the Superpermutation
Almanac (12 November 2026): cut the word into pieces, open a few more cuts near some joins, and find the best order
of all pieces exactly. Repeated round after round, it shortened words that the trail tools could no longer shorten.
The idea is his; the code here is mine and may differ from his in the details.

| file | what it is |
|---|---|
| `steps.c` | lists every step of weight GMIN or more between consecutive permutation windows of a word, into a binary file |
| `cutlns2.py` | the rounds: which cuts to open, the exact order, keep or undo |
| `net.py` | the exact solver of the order, one Gurobi model kept across rounds |
| `reN.sh` | six one-thread lines of `cutlns2.py` with different settings side by side, then `gdelcheck` on every word |

## What it does

The word is cut at every step of weight `--gbase` or more (default 5); these cuts stay open. A round picks `--K` joins of
the current order (with `--heavy 1` the heaviest joins not yet tried first, then random ones), opens the cuts of
weight `--gopen` .. `--gbase` - 1 in the `--nb` pieces on each side of each join, and with `--gfine G` also the
`--Rfine` cuts of weight G .. `--gopen` - 1 nearest to the join. Then it solves the order of all pieces exactly as a
maximum-weight path cover, where the weight of a join is the overlap of the two pieces. A gain is kept, anything
else is undone, and every opened cut whose two sides stay neighbours with their natural overlap is closed again.

The solver (`net.py`) keeps one LP across rounds. A round switches off the pieces it splits and switches on their
parts, then solves again from the previous basis, and every subtour cut found so far stays in the model. Overlaps of
`--k0` letters or more (default 4) are direct arcs between pieces; smaller ones go through one node per string. If
the LP is fractional and its bound does not prove that nothing is better, a MIP copy with lazy cuts decides.

With `--chain 1` runs of pieces away from the chosen joins (no join of weight `--wbreak` or more inside) are
contracted, and only pieces within `--D` places of a chosen join are free. The round is then exact only over that
smaller model. I needed this at n = 14: there the full model has an integrality gap of about 209 letters that the
MIP did not close in 120 to 300 s, while the contracted model found 59 letters at once.

A reordered word can hold a letter that can be deleted. Two of my words did. Every word must go through
`gdelcheck` or `delcheck`, and a deletable letter has to be removed and the word checked again.

## Building and requirements

    gcc -O2 -o steps steps.c

`cutlns2.py` needs Python 3 with numpy, scipy and gurobipy, and a Gurobi licence that allows models of this size
(the free licence does not). I ran it at n = 10 to 14. At n = 10 use `--k0 2`.

## Running it on one word

    steps WORD.txt 13 3 st.bin                                    # steps of weight 3 or more
    python cutlns2.py WORD.txt 13 st.bin out --gfine 3 --K 4 --Rfine 1000 --threads 1 --time 10800 --seed 1

`steps` takes the smallest weight that any `--gopen` or `--gfine` of the runs will use. `out/run.log` has one line a
round, `out/state.npz` the open cuts and the order whenever the length drops, and with `--write 1` (the default)
`out/w.txt` is the word at the end. `--resume out/state.npz` goes on from a state, and `--resume STATE --rounds 0
--solve0 0` only writes the word of a state. `--stop FILE` ends the run cleanly when the file exists.

`reN.sh` runs the six settings I used, one thread each:

    TOOLS=bin PYTHON=python bash tools/reorder/reN.sh 13 WORD.txt LENGTH DIR 10800

    --K 4 --Rfine 1000                                --K 2 --Rfine 1000
    --K 4 --Rfine 300                                 --K 4 --Rfine 3000 --chain 1 --wbreak 6 --D 3
    --K 2 --Rfine 3000 --chain 1 --wbreak 6 --D 3     --K 6 --Rfine 1000 --heavy 0

all with `--gfine 3` and seeds 1 to 6. `DIR/re.log` ends with `END best LENGTH word W`, the shortest word that
`gdelcheck` passes. `TOOLS` holds `steps` and `gdelcheck` (from [`gpucheck/`](../gpucheck/README.md)), and `GUARD`
puts a memory guard in front of each line (I used 8 GB per line).

## The options

| option | meaning |
|---|---|
| `--gbase G` | the backbone: cuts of weight G or more are always open (default 5) |
| `--gopen G` | open the cuts of weight G .. gbase - 1 in the pieces next to a chosen join (default 4) |
| `--gfine G`, `--Rfine R` | also open the R cuts of weight G .. gopen - 1 nearest to the join on each side (default off, R = 100) |
| `--K K` | joins chosen per round (default 4) |
| `--heavy 0/1` | 1: heaviest untried joins first, then random; 0: random (default 1) |
| `--chain 1`, `--wbreak W`, `--D D` | contract runs of pieces away from the chosen joins; chains break at joins of weight W or more (default 8); pieces within D places of a chosen join stay free (default 2) |
| `--time SEC`, `--rounds R`, `--stop FILE` | end of the run |
| `--seed S`, `--threads T` | random choices of the joins; Gurobi threads (default 2) |
| `--neutral 1` | also keep a different order of equal length |

The other options (`--noise`, `--miptime`, `--lpit`, `--stallmax`, `--fthr`, `--mipparams`, `--k0`, `--maxchain`,
`--R`, `--far`, `--nb`, `--wmin`, `--rebuild`, `--resume`, `--solve0`, `--write`) are listed with their defaults
in the argument list at the top of `cutlns2.py`.

## What it gave

From Pantone's n = 13 word W-0107 the gains came with the number of rounds: 9 letters after 10 rounds, 15 after 30,
42 after 100, 55 after 300, 73 after 1,000 and 81 after 1,570 (1 to 3 s a round on one thread), with `--Rfine 100`
and `300` and `--K 4`. Then `--Rfine 1000 --K 2` and the chain mode with `--Rfine 3000 --wbreak 6 --D 3` gave more,
which is why `reN.sh` runs these settings side by side. At n = 12 gains were rarer: 2 in 3,200 rounds with
`--Rfine 1000`. On my own n = 10 and n = 11 words it found nothing.
