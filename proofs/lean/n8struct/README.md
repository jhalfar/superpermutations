# The 27-walk and the packing of four 27-walks at n = 8

[`words/n8/README.md`](../../../words/n8/README.md) says two things about the selection of the word of 46,174
letters:

* the closed walk of 27 loops with row lengths `266646664666466466646664666` costs Q = 16 and is a single trail;
* four copies of it fit into the 120 loops without meeting, and up to renaming the symbols and reversal there is
  exactly one way to do this.

This directory proves both in Lean 4, with the Lean kernel checking every step. There is no `native_decide`.
It uses Pantone's library for rows, slices and closed trails and does not import Mathlib directly.

## Definitions

`N8Struct/Definitions.lean` mixes Pantone's definitions with my own. Its header lists every definition next to
the function of `words/n8/tools/n8lib/model.py` that it mirrors.

Pantone's definitions, where they hold at 8 symbols without his hypotheses (his construction needs m >= 9):

* A row (x, v) is his `Row` `⟨x, 6, v⟩`, and its cost is `Row.charge`.
* The slices of a row are `Completion.completeRows ⟨x,6,v⟩ 7`. These are exactly model.py `option_slices`:
  lift row j = `i_j`, repair row j = `r_j`.
* The slice word is `Row.word`, which is model.py `spell`.
* An overlap of 5 letters is `Row.Compatible`, and a closed trail is `ClosedTrail`.

My own definitions, for what his library does not have:

* `State` (an ordering of 0..5), `canon` (the loop), `gstep`, `walkRows`/`walkEnd`.
* `ClosedWalk` (model.py `walks.placements`) and `Q` (model.py `q_of`).
* `port`/`portTrails` (model.py `port`/`port_trails`).
* Renaming `relabel` (model.py `pack.relabel`), disjointness `Disj`, and reversal `revRow`.

`SingleClosedTrail rs` means: some ordering of all slices of `rs` is a Pantone `ClosedTrail`, and the slice heads
are pairwise different. Then the overlap-5 successor is unique, and model.py `trail_cycles` has exactly this one
cycle. A placement is the 27-walk started at a state g. It is determined by g, since its only row of length 2 is
at g. A packing is four placements with pairwise disjoint loops (`IsPacking`). Packings are compared as sets of
start states, which is the same as comparing sets of placements (`placement_injective`).

## The 27-walk: `Walk27.lean`

| theorem | statement | `#print axioms` |
|---|---|---|
| `walk27_closed` | `ClosedWalk id6 vs27`: the walk returns to 012345, every v is in 1..6, and its 27 loops are distinct | none |
| `walk27_pantone_compatible` | `CyclicallyCompatible walk27` (Pantone's level-7 compatibility) | none |
| `walk27_Q` | `Q walk27 = 16` | none |
| `walk27_port_perm` | the port map is a permutation of the 5 strands | propext, Classical.choice, Quot.sound |
| `walk27_portTrails` | `portTrails vs27 = 1` (the rule of the tool) | none |
| `walk27_single_trail` | `SingleClosedTrail walk27`: all 178 slices form one closed trail | propext, Classical.choice, Quot.sound |

## The packing

| theorem | statement | axioms |
|---|---|---|
| `placement_closed_all` | every one of the 720 states starts a closed 27-walk, by renaming `walk27_closed` | propext, Quot.sound |
| `placement_injective` | different states give different placements, so there are 720 | propext |
| `partners_complete`, `partners_disj` | the identity placement misses exactly the 21 placements `partners` | propext, Quot.sound |
| `triples_complete` | the triples of partners that complete the identity placement to a packing (12 ordered triples) | propext, Quot.sound |
| `packing_classification` | every packing (`IsPacking g1 g2 g3 g4`) is σ·K0 or σ·K1 for a state σ | propext, Classical.choice, Quot.sound |
| `relabel_packing`, `K0_packing`, `K1_packing` | conversely, every σ·K0 and every σ·K1 is a packing | propext, Quot.sound |
| `K0_not_K1` | no renaming maps K0 to K1, so there are 2 classes up to renaming | propext, Classical.choice, Quot.sound |
| `stab_K0`, `stab_K1` | each stabiliser is an explicit list of 4 renamings | propext, Classical.choice, Quot.sound |
| `Pstar_class` | the packing of `selection-46174.txt` is `[0,2,1,5,4,3]`·K1 | propext, Classical.choice, Quot.sound |
| `Pstar_rows` | its rows are exactly the 108 rows of the selection file | propext, Classical.choice, Quot.sound |
| `Pstar_loops`, `leftover_spec`, `all_loops_covered` | 108 distinct loops are covered; the 12 loops without a row are the rest of the 120 | none / propext, Quot.sound / propext, Quot.sound |
| `V4_stabilises` | V4 = {id, (25)(34), (01)(34), (01)(25)} maps the packing to itself | propext, Classical.choice, Quot.sound |
| `V4_swaps`, `V4_swaps_rows` | each element other than the identity swaps the four walks in pairs | propext |
| `V4_leftover`, `V4_leftover_orbits`, `V4_leftover_no_fixed` | V4 maps the 12 loops without a row onto themselves, in three orbits of four, and no element other than the identity fixes any of them | propext, Classical.choice, Quot.sound / propext / propext |
| `rev_slices`, `rev_rowless` | word level: the slices of each reversed row (and of each reversed loop without a row) are the reversed slices | propext, Classical.choice, Quot.sound |
| `rev_packing`, `PstarRev_class` | reversal maps the packing to `PstarRev` = `[0,3,4,5,1,2]`·K0, which is in the other class | propext, Classical.choice, Quot.sound |

So there are exactly two packings up to renaming, and reversal swaps them: up to renaming and reversal there is
one packing.

`propext`, `Classical.choice` and `Quot.sound` are Lean's standard axioms. They come from library lemmas such as
the decidability of `List.Perm` and `simp`. There is no `sorryAx` and no `Lean.ofReduceBool`.

## What is not proved

* The counts 7,560 and 360 are not proved as counts. They follow from the proved facts by arithmetic that is not
  formalised: 720 placements, each disjoint from exactly 21 others, give 720·21/2 = 7,560 pairs; two classes,
  each with a stabiliser of order 4, give 2·720/4 = 360 packings. `gen.py` confirms both numbers by direct
  enumeration.
* The link between `revRow` and reading a whole word backwards is checked at the level of slices (each slice set
  is reversed exactly), and only for the 120 options of this selection. That the order and the joins of a word
  reverse as well is clear, but it is not formalised.
* Only the finite facts are formalised. The length formula 46,085 + Q + J and the word itself are not; the word
  is checked by the kernel in [`../words/`](../words/README.md) (`hasWord_eight_k`).

## Files

| file | what |
|---|---|
| `N8Struct/Definitions.lean` | the definitions |
| `N8Struct/Walk27.lean` | the 27-walk |
| `N8Struct/Symmetry.lean` | renaming lemmas; facts about all 720 states through `forall_stateP` |
| `N8Struct/PackBase.lean` | placement, packing, literal tables, `placement_closed_all`, `placement_injective` |
| `N8Struct/Partners.lean` | `partners_complete`, split into 6 kernel checks of 120 states each |
| `N8Struct/Classify.lean` | `packing_classification`, `relabel_packing`, `K0_packing`, `K1_packing` |
| `N8Struct/Orbits.lean` | `K0_not_K1`, `stab_K0`, `stab_K1` |
| `N8Struct/Published.lean` | the packing of `selection-46174.txt`, its loops, the Klein group |
| `N8Struct/Reversal.lean` | reversal at word level and at selection level |
| `gen.py`, `gen_out.txt`, `gen_out2.txt` | recomputes the tables with the model of `words/n8/tools` and asserts 720 placements, 7,560 compatible pairs, 360 packings, 2 classes and the reversal; its output |
| `build.sh` | builds everything from sources |

The Lean files do not trust `gen.py`: every table is tied to the definitions by a kernel `decide`.

## Building

```sh
./build.sh
```

It needs what `../constant/build.sh` needs (Lean 4.31.0, Pantone's repository with Mathlib fetched; see
[`../README.md`](../README.md)). It checks Pantone's sources against `../constant/pantone-sources.sha256`, runs
`gen.py` and compares its output with the two files here, compiles the modules of Pantone's library that are
needed and the nine files of `N8Struct/`, and fails if a `#print axioms` line names an axiom other than the
three standard ones.

From an empty build directory, with one Lean process on one thread: 15 modules (the nine files and six of
Pantone's library), 3 minutes 6 s of wall time, at most 4.2 GB of committed memory for the whole run. Reversal
takes 62 s, Symmetry 48 s, the others 1 to 27 s. A first attempt evaluated whole walks inside 720-fold kernel decisions and
grew to about 28 GB before I stopped it; the files here tie literal tables to the definitions once and then
decide only on those tables.
