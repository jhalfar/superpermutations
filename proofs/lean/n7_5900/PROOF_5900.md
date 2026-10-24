# L(7) >= 5,900: the written proof

State of 2026-10-24. A superpermutation on 7 symbols is a word that contains every permutation of the
symbols as a contiguous subword, and L(7) is the least length of one. This document is the written proof of
L(7) >= 5,900. It rests on the Lean theorem L(7) >= 5,899 with its exact model, on arguments written out here
and on a list of exhaustive computations (Table C in section 0.3). All of them have ended and none found a
violation. Every one has two complete runs by programs that share no code, with equal counts.

The bound is also a Lean theorem at level 2: `covers_lower_bound_7_5900_native`, assembled on 2026-10-24.
The arguments of sections 3 to 6 are proved in Lean with the search equations as hypotheses, and every search
equation of Table C has been evaluated by compiled code (section 0.1). The Lean files are in
`proofs/lean/n7_5900/`, on top of the Lean proof of 5,899 in `proofs/lean/n7/`.

Notation and terms are those of the written proof of 5,899 (not in this repository; its Lean form is
`proofs/lean/n7/`), cited below as [P]. Formulas are in plain ASCII: `sum` for a sum, `eps` for the excess,
`sigma`, `tau2`, `rho`, `phi` for the maps and the potential.

## 0. The theorem and what it rests on

*Theorem.* Every word over 7 symbols that contains each of the 5,040 permutations of the symbols as a
contiguous subword has at least 5,900 letters.

By the exact model (L1 below) the theorem is equivalent to

    (*)  no valid standard configuration on 7 symbols has cost at most 135.

A configuration of cost 120 + D has defect D, so (*) says "no configuration of defect at most 15". The proof of
(*) has four parts.

1. Accounting (section 3). A configuration of cost at most 135 gives a kernel and hanging components whose
   values add up to at least 45 within total weight 90. Every component of positive value is one object: a
   sequence with links or a ring. A finite check over the tables leaves 6,429 profiles in 69 shapes.
2. Kernel alone (section 4). No sequence with s links has value at least 45 within weight 90. This removes the
   9 shapes with one piece (125 profiles).
3. Joint statements (section 5). Five statements about two or three pieces remove the other 60 shapes (6,304
   profiles).
4. Conclusion (section 6).

The proof of 5,899 ended with one knapsack over tables of single objects. At defect 15 that is not possible:
3,823 of the 6,429 profiles consist of pieces that each exist on their own, for example a chain with 85 rows and
49 holes next to a closed chain with 57 rows and 41 holes. So I need statements about several disjoint pieces,
and I prove them by search.

### 0.1 What is in Lean

The Lean proof of 5,899 is in `proofs/lean/n7/` (its README is `proofs/lean/n7/README.md`, its files are in
`proofs/lean/n7/LowerBounds/`). Level 1 is checked by the Lean kernel with the axioms `propext`,
`Classical.choice` and `Quot.sound`. Level 2 adds 22 search equations evaluated by compiled code
(`native_decide`).

- (L1) The model, level 1. `covers_length_gt_of_no_stdConfig (hk : 5 <= k) (D : Nat)`: if no valid
  configuration on k symbols has cost at most (k - 2)! + D, then every word that contains all permutations has
  at least hpv k + D + 1 letters. Here hpv 7 = 5,884, so k = 7 and D = 15 give 5,900 from (*).
  `no_stdConfig_iff` says that the two sides are equivalent: the model loses nothing.
- (L2) The tables of set B, level 2. The finite statements F0 (chains, table M to 84 holes), F1 to F5
  (sequences with 1 to 5 links, tables P_1 to P_5), FR (rings, table PR to 77 holes) and FF (five profile
  statements) of [P] section 8. In Lean they are `Caps` and `Profiles`, obtained by `caps_of_search` and
  `profiles_of_search` from the 22 evaluated equations. The theorem of 5,899 is `covers_lower_bound_7_native`.
- (L3) Lemmas of level 1 that do not mention the cost. I use them in their Lean form:
  `entries_length_ge` (a valid configuration has at least 720 blocks); the geometry (G2) and (G3) of [P]
  section 2, `Valid.free_attachment`, `Valid.slot_not_own`, `Valid.attachment_cost_one`; the extension, the
  merge and the wrap (G4) to (G6), `free_geom`, `cost_one_geom`, `junction_extLast`, `junction_extFirst`,
  `junction_merge`, `path_glue`, `path_glue_links`, `ring_glue`, `TrailFam.rot`; the cut at heavy seams,
  `cutRows_spec`; Lemma FAM for one hanging component, `famH_spec`; Lemma FF and its companion for seven or
  more chains, `family_le_49` and `family_le_44`, both from `Caps` and `Profiles`.
- Lean statements that cannot be used as they stand. `acc_value`, `acc_weight` (Lemma ACC), `hanging_item`,
  `glue_path_bound`, `glue_ring_bound` and `no_config_134` are stated for cost at most 134 or for tables to 84
  holes. Where I need them at cost 135 I repeat the argument on paper below.

*Defect 15 in Lean, level 1 (2026-10-11).* The arguments of this document are formalised with the searches as
hypotheses. The files are in `proofs/lean/n7_5900/LowerBounds/` (`K*.lean`, `A15*.lean`, `J15*.lean`,
`F5900*.lean`). Each theorem below uses the three axioms of level 1 only.

- `KS.tableT_of_search` and `KS.theoremK_of_search` (`KFinal.lean`): table T and Theorem K of section 4 from
  13 equations of the form "this search finds nothing". They contain Lemma RV, Lemma REV and the completeness
  of the search with the reversal cut (sections 4.2 to 4.5). Lemma CL is not needed there: K6, K7 and K8 read
  the rows that K5, K6 and K7 prove.
- `J15.joint_of_search` (`J15Final.lean`): the joint statements S1 to S5 of section 5 from their search
  equations, with the completeness of the joint search (section 5.4).
- `A15.no_config_135` (`A15Final.lean`): statement (*) from set B, table T, Theorem K and the joint
  statements. It contains sections 3, 5.2 and 6. The knapsack is not the count KN of section 3.7 (see the end
  of that section).
- `covers_5900_of_search` (`F5900.lean`): every word that contains all permutations of 7 symbols has at least
  5,900 letters, given the search equations: the 24 hypotheses of the theorem of 5,899 and the equations of
  defect 15. Nothing else is assumed.

*Defect 15 in Lean, level 2 (2026-10-24).* The equations of defect 15 are evaluated by `native_decide` in 72
modules in `proofs/lean/n7_5900/LowerBounds/`. A long search is cut into parts, and its parts are split into
ranges with one equation for each range. The 13 kernel statements and inputs become 41 equations in 36
modules, the 6 joint statements become 36 equations in 36 modules:

| statements of Table C | Lean equations | modules |
|---|---|---|
| I1, I2, C76, I4, K6 | `KS.c59`, `KS.c62`, `KS.c76`, `KS.ring`, `KS.k6` | `KSmallNative` |
| K8, K7 | `KS.k8`, `KS.k7` | `KK87Native` |
| K5 | `KS.k5` | `KK5Native` |
| K4 | `KS.k4` | `KK4Native` |
| K3 | `KS.k3` | `KK3Native` |
| K2 | `KS.k2_0` to `KS.k2_11` (12) | `KK2_00Native` to `KK2_11Native` |
| K1 | `KS.k1_0` to `KS.k1_7` (8) | `KK1_00Native` to `KK1_07Native` |
| K0 | `KS.k0_0` to `KS.k0_10` (11) | `KK0_00Native` to `KK0_10Native` |
| S5, S4, S3 | `J15.s5`, `J15.s4`, `J15.s3` | `J15S5Native`, `J15S4Native`, `J15S3Native` |
| S2a1 | `J15.s2a1_0` to `J15.s2a1_2` (3) | `J15S2A1_00Native` to `J15S2A1_02Native` |
| S2a2 | `J15.s2a2_0` to `J15.s2a2_17` (18) | `J15S2A2_00Native` to `J15S2A2_17Native` |
| S1 | `J15.s1_0` to `J15.s1_11` (12) | `J15S1_00Native` to `J15S1_11Native` |

Each module file names its search with all parameters. The Lean searches take the levels as a closed range:
`KS.k0_0` searches the levels 77 to 90, which is F(0; 76, 90) of section 4.6. `KFinalNative.lean` proves
`KS.tableT_native` and `KS.theoremK_native`, `J15FinalNative.lean` proves `J15.evals_native`, and
`F5900Native.lean` proves

    theorem covers_lower_bound_7_5900_native : forall w : List (Fin 7), Covers w -> 5900 <= w.length

`proofs/lean/n7_5900/Audit5900Native.lean` states the theorem with no definition of this project and prints
its axioms. They are `propext`, `Classical.choice`, `Quot.sound` and 99 axioms of `native_decide`: the 22
equations of the proof of 5,899 (17 behind set B, 5 profile statements), the 41 equations for table T' and
Theorem K, and the 36 equations of the joint statements. So 22 + 41 + 36 = 99. Level 1,
`covers_5900_of_search`, depends on `propext`, `Classical.choice` and `Quot.sound` only. The searches of
defect 15 have about 1.5e13 kept prefixes for the kernel statements and 2.9e13 tried vertices for the joint
statements. The modules ran from 2026-10-11 to 2026-10-23; by the thread count and the wall time of each
module they took about 4,200 thread-hours.

The Lean form differs from this text in four places. None of them changes a statement.

- K6, K7 and K8 read the rows D_5, D_6 and D_7 that K5, K6 and K7 prove (rows 5 to 8 of table T' in
  `KTables.lean`), not the rows T_5, T_6 and T_7 of the tables D^u_S. So the Lean proof needs no Lemma CL for
  Theorem K, and K5, K6, K7, K8 depend on each other in this order. Their trees are smaller than those of
  Table C: 27,105 kept prefixes for 8 links and 22,709,717 for 7 links, against 32,407 and 29,066,365.
- The knapsack is not the count KN, and in it sequences are bounded by table D (Theorem K), not by T.
- The joint search counts shared classes as blocks less classes, does not replace the need of a ring by 0
  (section 5.6), and is cut into parts by a list of gates.
- The Lean evaluations answer "false" and give no counts. The counting copies of the Lean engines gave the
  counts of Table C for K8 and K7 on the tables D^u (32,407 and 29,066,365) and, summed over 60 parts, for S5
  (43,171,554 kept, 218,221,531 tried) and S4 (1,002,039,640 kept, 5,072,908,057 tried).

### 0.2 What is proved on paper in this document

| | argument | section |
|---|---|---|
| P1 | the closure bounds for the tables beyond their given entries | 2.2 |
| P2 | Lemma ACC at cost 135; eps <= 1; the bound on the number of chains | 3.1 to 3.3 |
| P3 | the case eps = 1: the cut at the dear place and the items E, A', B' | 3.5 |
| P4 | every configuration of cost at most 135 gives a surviving profile | 3.6 |
| P5 | the search rule of the kernel-alone statements; Lemma RV; Lemma REV; completeness | 4.2 to 4.5 |
| P6 | from a configuration to pieces, with the bound on shared classes | 5.2 |
| P7 | the search of the joint statements and its completeness; the reduction of S2b | 5.4, 5.5 |
| P8 | the conclusion | 6 |

### 0.3 The computations (Table C)

Every line is an exhaustive search. "kept" is the number of kept prefixes: prefixes whose successors are tried.
"tried" (joint statements) is the number of start vertices tried. The first and the second program are
independent implementations for the processor (section 7.2). "both" means that both ended, found nothing and
have the same counts to the last digit. "card" is a third program, for a graphics card; it uses the same rule,
so its counts are the same numbers. "card, both" means that all three agree. Every line is also evaluated in
Lean (section 0.1).

Kernel alone (section 4), table D:

| | statement: no sequence above table D with | kept | state |
|---|---|---|---|
| K8 | 8 links, all levels to 42 holes | 32,407 | no violation, both |
| K7 | 7 links, all levels to 48 holes | 29,066,365 | no violation, both |
| K6 | 6 links, all levels to 54 holes | 4,551,813,305 | no violation, card, both |
| K5 | 5 links, all levels to 60 holes | 159,884,470,908 | no violation, both; see the note |
| K4 | 4 links, levels 48 to 66 | 45,080,993,091 | no violation, card, both |
| K3 | 3 links, levels 55 to 72 | 445,234,933,436 | no violation, card, both |
| C76 | chains, level 76 | 6,065,162,755 | no violation, card, both |
| K2 | 2 links, levels 61 to 78 | 5,583,726,910,601 | no violation, card, both |
| K1 | 1 link, levels 62 to 84 | 3,743,897,407,212 | no violation, card, both |
| K0 | chains, levels 77 to 90 | 5,236,271,122,213 | no violation, card, both |

The first program ended K2, K1 and K0 on 2026-10-11 with the counts of the card to the last digit (187, 196
and 209 thread-hours), and the second program ended K2, K1 and K0 with the same counts (173, 157 and 122
thread-hours).

Note on K5. The count 159,884,470,908 is the second program's. The first program ran K5 in 3 parts and each
part counted the 214,376 kept prefixes above its gate. The sum of its three logs, 159,884,899,660, went into my
log of results (not in this repository) before I saw this, in the entry of 2026-10-09 21:20 there. Counted once
it is 159,884,899,660 - 2 x 214,376 = 159,884,470,908.

Inputs to the tables (section 2):

| | statement | kept (second program) | state |
|---|---|---|---|
| I1 | chain cap at 59 holes | 321,229,855 | no violation; first computed by the referee's program of the 5,899 work |
| I2 | chain caps at 62 to 75 holes | 3,319,568,194 | no violation; first computed by earlier programs |
| I4 | ring table to 69 holes | 3,156,668,409 | found 0; first computed by earlier programs |

Joint statements (section 5), table T':

| | statement | kept | tried | state |
|---|---|---|---|---|
| S5 | J(S0 S0 R; 62, 70; 2) | 43,171,554 | 218,221,531 | found 0, both |
| S4 | J(S1 S1 R; 61, 71; 1) | 1,002,039,640 | 5,072,908,057 | found 0, both |
| S3 | J(S2 R R; 57, 76; 2) | 86,628,445,019 | 438,813,979,430 | found 0, both |
| S2a1 | J(S5 R; 51, 83; 1), ring with >= 16 holes | 379,470,653,297 | 1,906,338,561,159 | found 0, both |
| S2a2 | the same, ring with 8 to 15 holes | 3,220,712,840,648 | 16,152,522,797,959 | found 0, card, both |
| S1 | J(S4 S4; 55, 78; 1) | 2,104,901,227,440 | 10,736,238,262,512 | found 0, card, both |
| S2b | the same as S2a1, ring with <= 7 holes | | | follows from K0 to K5 (section 5.5) |

Every statement ended with no violation or with "found 0". The card program for the joint statements also
gave the counts of S5, S4, S3 and S2a1.

### 0.4 The level of trust

This is a computer-assisted proof, and it is formalised in Lean. Its three levels differ in what they ask the
reader to trust.

- The Lean level: the Lean kernel for level 1, and for the 99 equations of level 2 the Lean compiler, the C
  compiler of the Lean toolchain, the runtime and the libraries built from the search engines
  (`proofs/lean/n7/LowerBounds/PSearch.lean`, `proofs/lean/n7_5900/LowerBounds/KSearch.lean` and
  `proofs/lean/n7_5900/LowerBounds/J15Search.lean`), as the README of the proof of 5,899 says for its 22
  equations.
- The paper level: the arguments of this document. A referee's check went through them step by step as they
  stood in my working files (its notes are not in this repository) and found no gap. That check is a reading
  with tests. Since then the arguments of sections 3 to 6 have been proved in Lean at level 1 (section 0.1),
  and that work found no gap in this text either. Lemma CL and the count KN are the two steps that Lean does
  not contain, because its proof does not need them.
- The computed level: C and C++ programs. Each statement is to be run by two programs for the processor that
  share no code. The second was written from the texts only, without reading a source of the first. For the
  statements marked "both" the two counts of kept prefixes are equal. The card program for the kernel
  statements takes the code that builds the tables from the first program and has its own search, so it is
  not independent of the first program. Every computed statement of defect 15 has also been evaluated in Lean,
  by searches whose completeness is proved at level 1.

What has not been done is listed in section 7.5.

### 0.5 Who did which part

The transform that cuts a path through all permutations into components is Zach Hunter and Uku Raudvere's. The
chains of a component and the lemmas about them are Xiaolong Liu's. The bound 5,898 is Justin Lebar's; nothing
of his proof is used. The model of standard configurations, the proof of 5,899 and what follows here are mine.

## 1. Objects

All definitions are those of [P] section 1. I repeat what the statements below need.

- A *word* is a permutation of the symbols 1 to 7. `sigma` moves the first letter of a word to its end,
  `sigma^-1` the last letter to the front. The *class* of a word is its orbit under `sigma`: 7 words. There
  are 5,040 words and 720 classes.
- `ew(u, v)`, the *weight* of the step from u to v, is the least t >= 1 such that the last 7 - t letters of u
  are the first 7 - t letters of v.
- A *block* is a class entered at one of its words, the *entry* e. Its *exit* is `sigma^-1 e`. Written
  out, the block is the word e followed by the first 6 letters of e.
- `tau2` rotates the first 6 letters: `tau2(a b c d e f m) = b c d e f a m`. The step from the exit of the
  block of e to `tau2 e` has weight 2.
- A *row* (e, l) with 1 <= l <= 6 is the l blocks entered at e, tau2 e, ..., tau2^(l-1) e. It has 6 - l
  *holes*. Its last entry is tau2^(l-1) e and its exit is the exit of its last block.
- The *link* from a row to the next row has the weight ew(exit of the first, entry of the second).
- A *chain* is a list of rows whose blocks lie in pairwise different classes and whose links all have weight
  exactly 3.
- A *sequence with s links* is a list of rows whose blocks lie in pairwise different classes, whose links
  have weight 3 or 4, exactly s of them weight 4. It is s + 1 chains joined by links of weight 4. A chain is a
  sequence with 0 links. For a sequence with exactly x holes I call x its *level*.
- A *ring* is a chain with at least 2 rows such that the step from the exit of its last row to the entry of
  its first row has weight 3.
- Value and weight of an object: for a sequence with s links `val = rows - holes - 5 s` and
  `wt = holes + 6 s`; for a ring `val = rows - holes` and `wt = holes`.
- A *standard configuration* is a kernel, which is a list of rows, and hanging components, each a list of
  rows attached at one vertex, its slot ([P] section 1; Lean `NConfig`). It is valid if every class is a block
  exactly once, every seam between consecutive rows of a component has weight at least 3, the two attachment
  weights w0 and w1 of every hanging component are at least 2 and the attachments obey the rules of the model.
  Its cost is the number of rows, plus the weight less 3 for every seam, plus w0 + w1 - 4 for every hanging
  component.
- For a component C with m rows, h holes, seam excess X (the weight less 3, summed over its seams), j heavy
  seams (weight at least 4) and attachment cost a = w0 + w1 - 4 (a = 0 for the kernel):

      v(C) = m - h - 5 (X + a),        w(C) = h + 6 (X + a).

  X >= j, with equality iff every heavy seam has weight 4. Always w(C) >= 0.
- The shapes of a hanging component ([P] section 4): H1 (a >= 1), H0a (a = 0, j >= 1), H0b (a = 0, j = 0,
  m >= 3), H0c (a = 0, j = 0, m = 2), H0d (a = 0, j = 0, m = 1).

Facts used ([P] section 1 and 2). Every word has exactly 5 successors of weight 3 and 23 of weight 4 in other
classes. All notions are invariant under renaming the symbols. (G4): a hanging component H with a = 1 can have
its last or its first row extended by one block of the class of its slot; the new list H+ has the same rows
otherwise, one hole less, pairwise different classes, the same seams and a step of weight 3 from its last row
to its first row; the class of the slot contains no block of H. (G5): in a hanging component H with a = 0 and
at least two rows there is a class X that contains no block of H, and the last row, one block of X and the
first row form one row rho*; the cyclic list rho*, rho_2, ..., rho_(m-1) has m - 1 rows, 7 holes less and
pairwise different classes, and its links are the seams of H. (G7): a hanging component with a = 0 and one
row has at least one hole.

## 2. The tables

All tables are upper bounds on the number of rows of an object with an exact number of holes x.

### 2.1 Set B (Lean)

[P] section 9 prints M(0..84), P_1(0..78), P_2(0..72), P_3(0..66), P_4(0..60), P_5(0..54) and PR(0..77). By
(L2): a chain with x holes has at most M(x) rows; a sequence with exactly s links and x holes has at most
P_s(x) rows; a ring with x holes has at most PR(x) rows. Put P_0 = M.

### 2.2 Table T

T has the entries T_s(x) for 0 <= s <= 15 and 0 <= x <= 96 and a row TR(x) for rings. The given entries are

- T_s(x) = P_s(x) for 0 <= s <= 5 and x <= 84 - 6 s, with these exceptions in the row of chains:

      x        59   62  63  64  65  66  67  68  69  70  71  72  73  74  75  76
      T_0(x)   97  101 102 103 104 106 107 109 111 112 115 116 117 118 119 123
      M(x)     98  107 110 111 112 113 114 115 116 119 120 121 122 123 124 125

- TR(x) = PR(x) for x <= 63; TR(64..69) = 95 96 97 98 99 100; TR(x) = min(PR(x), T_0(x)) for 70 <= x <= 77,
  which is 112 115 116 117 118 119 123 126; TR(x) = T_0(x) for x >= 78.

All other entries are defined by the closure: for x = 0, 1, 2, ... and for s = 0, 1, 2, ... in this order, an
entry T_s(x) that is not given is the least of the bounds (cl1) and (cl2):

    (cl1)  for every a with 1 <= a <= x - 5:
           max over a <= d <= a + 4 and over sA + sB in {s, s - 1}, sA, sB >= 0, of  T_sA(d) + T_sB(x - d)
    (cl2)  if s >= 1:
           max over sA + sB = s - 1 and over 0 <= d <= x of  T_sA(d) + T_sB(x - d)

*Lemma CL (closure).* If the given entries are upper bounds, so are all entries.

Proof, by induction in the order of the definition. Let a sequence have exactly s links and x holes.
(cl1): let 1 <= a <= x - 5 and cut after the first row at which the number of holes so far is at least a. A
row has at most 5 holes, so the prefix A has d holes with a <= d <= a + 4 <= x - 1, and the rest B is not
empty and has x - d holes. A and B are sequences with sA and sB links, where sA + sB = s if the cut link has
weight 3 and s - 1 if it has weight 4. Both have fewer than x holes, so their entries come earlier, and
rows = rows(A) + rows(B) <= T_sA(d) + T_sB(x - d).
(cl2): for s >= 1 cut at a link of weight 4. The two parts have sA + sB = s - 1 links, so each has fewer than
s links and at most x holes, and their entries come earlier. QED

Where the given entries come from:

- Set B: (L2).
- I1. T_0(59) = 97. It is the exact value in the chain table to 61 holes of the referee's program of the
  5,899 work (a file of that program, not in this repository). The first chain program and Lean have 98 there.
  The second program proved the level again, given the row of chains of set B to 58 holes: no violation,
  321,229,855 kept.
- I2. T_0(62..75). First computed by the chain ladder of an earlier program of mine in two implementations (C
  and Rust), with 117, 118, 119 = x + 44 at 73 to 75 holes. The second program proved all 14 levels again in
  one search, given the row of chains to 61 holes: no violation, 3,319,568,194 kept.
- I3. T_0(76) = 123 is implied by C76 of Table C, which gives 120.
- I4. TR(64..69), the ring table of an earlier program, equal to the referee's. The second program proved
  the ring table for 0 to 69 holes again by the ring search of [P] section 8.2 with the row T_0: found 0,
  3,156,668,409 kept. It uses T_0 to 69 holes, so it rests on I1 and I2.
- TR(70..77) and beyond: FR, or "a ring is a chain".

So T is valid given (L2), I1, I2, C76 and I4. Closure entries used below:

    T_0(85..90) = 143 145 146 149 150 152          T_1(79..84) = 142 143 145 146 148 149
    T_2(73..78) = 139 140 142 143 145 146          T_3(67..72) = 136 138 139 140 142 143
    T_4(61..66) = 133 135 136 138 139 141          T_5(55..60) = 131 134 135 138 138 141
    T_6(0..54):  35 35 39 39 43 43 47 47 51 51 55 55 59 59 63 63 67 67 71 71 75 75 79 79 83 83 87 87 91 91
                 94 94 98 98 102 102 105 105 109 109 113 113 116 116 120 120 123 123 127 127 131 131 134 134 138
    T_7(0..48):  40 40 44 44 48 48 52 52 56 56 60 60 64 64 68 68 72 72 76 76 80 80 84 84 88 88 92 92 96 96
                 100 100 104 104 107 107 111 111 115 115 118 118 122 122 126 126 129 129 133
    T_8(0..42):  45 45 49 49 53 53 57 57 61 61 65 65 69 69 73 73 77 77 81 81 85 85 89 89 93 93 97 97 101 101
                 105 105 109 109 113 113 117 117 120 120 124 124 128

The rows T_6, T_7, T_8 at these holes depend on set B alone. A table file of mine (`caps7.txt`) holds T for
s <= 8, and a program of mine (`tabs15.py`, tier CAP) computes it; neither is in this repository. The referee's
check recomputed the closure for s <= 15 and x <= 96.

### 2.3 Tables D and T'

- D (file `capD15.txt`; in Lean `Dtab`): D_s(x) = min(T_s(x), x + 44 + 5 s) for 0 <= s <= 8 and
  0 <= x <= 90 - 6 s. In particular D_0(76) = 120. The levels where D_s(x) < T_s(x) are

      s = 0: 76..90     s = 1: 62..64, 67..84     s = 2: 61..78     s = 3: 55..72     s = 4: 48..66
      s = 5: 44, 46..60     s = 6: 44..54     s = 7: 42, 44..48     s = 8: 42

  These are 15 + 21 + 18 + 18 + 19 + 16 + 11 + 6 + 1 = 125 entries. D is what section 4 proves.
- D^u_S for S = 5, 6, 7, 8 (files `capD15u_S.txt`): the rows T_0, ..., T_(S-1) and the row D_S.
- T' (file `caps7b.txt`; in Lean `Ttab` and `TRtab`): T with T'_0(76) = TR'(76) = 120 and with
  T'_s(x) = D_s(x) for 5 <= s <= 8 and x <= 90 - 6 s. T' is valid given T, C76 and K5 to K8. The joint
  statements read the rows 0 to 5 and the ring row of T' only, because their pieces have at most 5 links.

The table files are files of my programs and are not in this repository. `Dtab`, `Ttab` and `TRtab` in
`proofs/lean/n7_5900/LowerBounds/KTables.lean` write D and T' out; `Ttab` has the rows 0 to 8 of T' to the
holes that Lean reads (the row of chains to 84 holes, the rows P_1 to P_4 of set B, the rows D_5 to D_8), and
`TRtab` the ring row to 84 holes.

## 3. The accounting at defect 15

Throughout, c is a valid configuration with cost at most 135.

### 3.1 Lemma ACC at cost 135

*Lemma ACC15.* sum over the components of v(C) >= 45 and sum of w(C) <= 90.

Proof, as for Lemma ACC of [P] section 3. Let R be the number of rows, h the number of holes and S the sum of
X + a over the components, so cost = R + S <= 135. The number of blocks is 6 R - h, and it is at least 720 by
`entries_length_ge`. Hence sum v = R - h - 5 S >= 720 - 5 (R + S) >= 45 and
sum w = h + 6 S <= 6 (R + S) - 720 <= 90. QED

### 3.2 The excess is at most 1

Cut every component at its heavy seams into chains and form the family F of c as in [P] section 4 (kernel and
H1: their chains; H0a: the chains with the last and the first wrapped into one; H0b: the inner chain; H0c,
H0d: nothing). For a chain put e = rows - holes - 5. Let eps_C = X - j for the kernel and H0a,
eps_C = (X - j) + (a - 1) for H1, 0 otherwise, and eps = sum of eps_C. Lemma FAM of [P] section 4 holds for
every valid configuration (`famH_spec` for a hanging component; for the kernel it is the identity
v = sum e + 5 - 5 eps_C, sum (holes + 6) = w + 6 - 6 eps_C):

    sum over C of v(C) <= sum over F of e + 5 - 5 eps,      sum over F of (holes + 6) <= sum of w(C) + 6 - 6 eps.

With Lemma ACC15:

    (3.1)    sum over F of e >= 40 + 5 eps        and        sum over F of (holes + 6) <= 96 - 6 eps.

*Lemma EPS.* eps <= 1.

Proof. If eps >= 2 then F is a family with sum (holes + 6) <= 84 and sum e >= 50. Lemma FF of [P] section 5
(`family_le_49`) says that such a family has sum e <= 49. QED

So there are two cases. If eps = 0, every heavy seam has weight 4 and every attachment costs 0 or 1, as in the
proof of 5,899. If eps = 1, exactly one component carries one unit of excess: it has one seam of weight 5 and
attachment cost at most 1, or it is an H1 with attachment cost 2 and no seam above weight 4. At cost 134 the
case eps = 1 was excluded by Lemma FF (Proposition R1 of [P]). At cost 135 it passes the tables: a family with
sum e >= 45 within weight 90 exists at table level (the tables allow 53). So it has to be treated.

### 3.3 The number of chains

*Lemma NCH.* If eps = 1 the family F has at most 6 chains. If eps = 0 it has at most 9.

Proof. Let e*(x) = M(x) - x - 5; a chain with x holes has e <= e*(x) by F0. For eps = 1, (3.1) gives
sum e >= 45 within sum (holes + 6) <= 90, and seven or more chains within that weight have sum e <= 44: this
is arithmetic (C) of [P] section 5, in Lean `family_le_44`. For eps = 0, (3.1) gives sum e >= 40 within weight
96. For at least 10 hole numbers x_i with sum (x_i + 6) <= 96 the largest sum of e*(x_i) is 36: with exactly
10, 11, ..., 16 numbers it is 36, 30, 24, 18, 12, 6, 0 (the program `acc15.py` of section 3.7; every x_i is at
most 36, so only entries of M in set B are read). QED

Consequences: with eps = 0 the kernel has at most 8 heavy seams, so sequences with up to 8 links occur and
set B, which stops at 5 links, is not enough. With eps = 1 no component has more than 5 heavy seams. The
finite check of section 3.7 does not use Lemma NCH: it runs over all numbers of links that fit into weight
90.

### 3.4 Components and items

An *item* is a kind with a number x. Its value and weight are read from table T:

| kind | object behind it | value | weight | range |
|---|---|---|---|---|
| K_s(x) | sequence, s links, x holes | T_s(x) - x - 5 s | x + 6 s | s >= 0, x >= 0 |
| Z(x) | ring, x - 7 holes | TR(x - 7) + 1 - x | x | x >= 7 |
| A_1(x) | ring, x - 1 holes | TR(x - 1) - x - 5 | x + 6 | x >= 1 |
| A_q(x) | sequence, q - 2 links, x - 1 holes | T_(q-2)(x - 1) - x - 5 q | x + 6 q | q >= 2, x >= 1 |
| B_q(x) | sequence, q - 1 links, x - 7 holes | T_(q-1)(x - 7) + 1 - x - 5 q | x + 6 q | q >= 1, x >= 7 |
| E_q(x) | sequence, q links, x holes | T_q(x) - x - 5 (q + 2) | x + 6 (q + 2) | q >= 0, x >= 0 |
| A'_c(x) | sequence, c - 3 links, x - 1 holes | T_(c-3)(x - 1) - x - 5 c | x + 6 c | c >= 3, x >= 1 |
| B'_c(x) | sequence, c - 2 links, x - 7 holes | T_(c-2)(x - 7) + 1 - x - 5 c | x + 6 c | c >= 2, x >= 7 |

K is the kernel item. Z, A_q, B_q are the hanging items of the proof of 5,899 ([P] section 7), with T in place
of set B. E, A', B' are new; they occur only if eps = 1.

*Lemma ITEM.* Let H be a hanging component of c with m rows, h holes, j heavy seams, seam excess X and
attachment cost a. Then v(H) <= 0 or H is of exactly one line of the following table. In every line the
object exists, the weight of the item is w(H) and v(H) is at most the value of the item.

| H | item | object | rows | holes | v(H) |
|---|---|---|---|---|---|
| H0b: a = 0, j = 0, m >= 3 | Z(h) | ring | m - 1 | h - 7 | (m - 1) + 1 - h |
| H1: a = 1, j = 0, m >= 2 | A_1(h) | ring | m | h - 1 | m - h - 5 |
| H1: a = 1, X = j >= 1 | A_q(h), q = j + 1 | sequence, j - 1 links | m | h - 1 | m - h - 5 q |
| H0a: a = 0, X = j >= 1 | B_q(h), q = j | sequence, j - 1 links | m - 1 | h - 7 | (m - 1) + 1 - h - 5 q |
| H1: a = 2, X = j >= 0 | E_q(h), q = j | sequence, j links | m | h | m - h - 5 (q + 2) |
| H1: a = 1, X = j + 1, j >= 1 | A'_c(h), c = j + 2 | sequence, j - 1 links | m | h - 1 | m - h - 5 c |
| H0a: a = 0, X = j + 1, j >= 1 | B'_c(h), c = j + 1 | sequence, j - 1 links | m - 1 | h - 7 | (m - 1) + 1 - h - 5 c |

For the kernel K with m rows, h holes and j heavy seams: if eps_K = 0 it is a sequence with j links, and
v(K) = m - h - 5 j is at most the value of K_j(h) at the weight w(K). If eps_K = 1 it gives the two items of
case (a) in section 3.5.

Proof of the first four lines and of the completeness of the table. By Lemma EPS every component has
eps_C <= 1, and eps_C is 0 for H0b, H0c, H0d. So a hanging component is of one of these kinds: H0b; H0c;
H0d; an H1 with (a, X) = (1, j), (2, j) or (1, j + 1); an H0a with X = j or X = j + 1. The components not in
the table are three: H0c with v = 2 - h <= -5 by (G5); H0d with v = 1 - h <= 0 by (G7); H1 with a = 1,
j = 0, m = 1, where v = -4 - h. In the lines 1 to 4 all heavy seams have weight 4 and a <= 1; these are the
lines of the table of [P] section 6, whose proofs use (G4), (G5) and the definitions, not the cost. In each
line v(H) is as shown, because X + a is 0, 1, q, q; the rows of the object are bounded by the table entry at
its holes (validity of T), which gives the value of the item; and w(H) = h + 6 (X + a) is the weight of the
item. The lines 5 to 7 are proved in section 3.5. QED

### 3.5 The case eps = 1: the cut at the dear place

Let eps = 1 and let C0 be the component with eps_C0 = 1. There are four cases.

*(a) C0 is the kernel, with one seam of weight 5.* Cut the kernel at that seam: K = K1 ++ K2. All other
heavy seams have weight 4, s1 of them in K1 and s2 in K2, so K1 is a sequence with s1 links and K2 a sequence
with s2 links (their classes are pairwise different because the blocks of a configuration are). With m_i
rows and h_i holes in K_i, X = s1 + s2 + 2 and

    v(K) = [m1 - h1 - 5 s1] + [m2 - h2 - 5 (s2 + 2)],        w(K) = [h1 + 6 s1] + [h2 + 6 (s2 + 2)].

The first brackets are at most the value of the kernel item K_s1(h1) and equal to its weight. The second
brackets are at most the value of E_q(x) with q = s2, x = h2 and equal to its weight.

*(b) C0 is an H1 with a = 2 and j heavy seams, all of weight 4.* Its rows are a sequence with j links, m
rows and h holes; X + a = j + 2. So v(H) = m - h - 5 (j + 2) is at most the value of E_j(h) and
w(H) = h + 6 (j + 2) is its weight. No geometry is used.

*(c) C0 is an H1 with a = 1 and j >= 1 heavy seams, one of weight 5.* Apply (G4): H+ has m rows, h - 1
holes (so h >= 1), pairwise different classes, the seams of H and a step of weight 3 from its last row to its
first row. Read the rows of H+ cyclically, starting with the row behind the seam of weight 5 and ending with
the row before it. The links of this list are the closing step, of weight 3, and the seams of H other than
the one of weight 5; of these, j - 1 have weight 4 and the others weight 3. So it is a sequence with j - 1
links, m rows and h - 1 holes. With c = X + a = j + 2: v(H) = m - h - 5 c <= T_(c-3)(h - 1) - h - 5 c, which
is the value of A'_c(h). Its weight is w(H) = h + 6 c.

*(d) C0 is an H0a (a = 0) with j >= 1 heavy seams, one of weight 5.* H has at least two rows. Apply (G5):
the cyclic list rho*, rho_2, ..., rho_(m-1) has m - 1 rows, h - 7 holes (so h >= 7) and pairwise different
classes, and its m - 1 links are the m - 1 seams of H. Cut the cyclic list at the seam of weight 5: the list
that starts behind it and ends before it is a sequence with j - 1 links, m - 1 rows and h - 7 holes. (If
m = 2 it is the single row rho*.) With c = X = j + 1: v(H) = m - h - 5 c <= T_(c-2)(h - 7) + 1 - h - 5 c,
which is the value of B'_c(h). Its weight is w(H) = h + 6 c.

These are the lines 5 to 7 of Lemma ITEM and the kernel with eps_K = 1. The only difference from the
reductions of [P] section 6 is the place of the cut: there the cyclic list is cut at its first heavy seam,
here at the seam of weight 5. A cyclic list of rows with pairwise different classes, read from any of its
rows, is a list of rows with the same links except the one it is cut at. QED

### 3.6 Profiles

A *profile* is a kernel item K_s(x) and a multiset of hanging items (kinds Z, A, B, E, A', B'), each of
positive value, at most one of them of a kind E, A' or B', with total weight at most 90. It *survives* if
its total value is at least 45. Its *shape* is the list of its kinds without the numbers x, for example
K0+A1+Z.

*Proposition PROF.* The configuration c gives a surviving profile, as follows. Take the kernel item (in
case (a) of section 3.5 the item of K1) and the item of every hanging component with v(H) > 0. In case (a)
take also the item E of K2 if m2 - h2 - 5 (s2 + 2) > 0. For every item taken there is the object of Lemma ITEM
or of section 3.5.

Proof. Every item taken for a hanging component or for K2 has a value that is at least the positive number
it bounds. At most one component has excess, so at most one item is of a kind E, A', B'. The weight of the
item of a hanging component H is w(H). The weight of the kernel item is w(K); in case (a) it is the first
bracket and the weight of the item of K2 is the second bracket, and the two brackets add up to w(K). All
these numbers are at least 0, so the total weight is at most the sum of w(C) over all components, which is at
most 90 by Lemma ACC15. The value of every item is at least the v (or the bracket) that it comes from. A
hanging component that is left out has v <= 0, and if the item of K2 is left out its bracket is at most 0. So
the total value is at least the sum of v(C) over all components, which is at least 45. QED

### 3.7 The knapsack: a finite check

*Finite statement KN.* With table T there are exactly 6,429 surviving profiles. They have 69 shapes: 9 with
one piece (the kernel alone; 125 profiles), 41 with two pieces (5,150 profiles), 19 with three pieces (1,154
profiles), none with four or more. No surviving profile contains an item A' or B'. The 69 shapes are those of
the table in section 5.3 and K0, K1, ..., K8.

The check is a finite enumeration: kernels K_s(x) with x + 6 s <= 90, so s <= 15, and multisets of items of
positive value within the weight that is left. Program: `acc15.py` with the arguments `15 CAP`. It and the
other programs named in this section are programs of mine and are not in this repository. Its output has the
lines

    (profiles) surviving profiles: 6429 in 507 cells (shape, S, u) and 69 shapes; ...
    shapes by number of pieces: 1:9 2:41 3:19

and it writes the shapes with their numbers of profiles to `shapes_D15_CAP.tsv`. I ran it again on
2026-10-10 from a copy: same output; the split 125 / 5,150 / 1,154 is the sum of that file by number of
pieces. Three more programs count the same profiles with their own code: `acc15b.py` (a counting knapsack),
`book.py` (its own recursion) and the referee's `acc_ref.py`. All four give 6,429 profiles and 69 shapes.

The one-piece profiles are the kernels K_s(x) with T_s(x) - x - 5 s >= 45. These are exactly the 125 entries
of section 2.3 where D is below T. For s >= 9 the largest value of T_s(x) - x - 5 s with x + 6 s <= 90 is
41, 35, 29, 23, 17, 11, 5 for s = 9, ..., 15.

The shapes do not depend on the computed entries of T: with set B and its closure alone the referee's check
finds 7,129 surviving profiles in the same 69 shapes.

The Lean proof (`A15.no_config_135`) does not count profiles. For each number of pieces it takes the upper
hull of the table values against the weight and shows by `decide` in the kernel (34 s) that every multiset of
items outside the shapes of section 5.3 stays below 45. That check found one point the count hides: a shape
with a kernel, a ring and an item A or B is excluded only because every item taken has positive value.

## 4. The kernel alone

### 4.1 The statement

*Theorem K.* For 0 <= s <= 8 and 0 <= x <= 90 - 6 s, every sequence with exactly s links and x holes has at
most D_s(x) rows.

*Corollary K.* No sequence with weight at most 90 has value at least 45.

Proof of the corollary. Let the sequence have s links and x holes, x + 6 s <= 90. If s <= 8 then
rows <= D_s(x) <= x + 44 + 5 s, so val <= 44. If s >= 9 then val <= T_s(x) - x - 5 s <= 41 (section 3.7). QED

Theorem K is the conjunction of the statements K8, K7, K6, K5, C76, K0, K1, K2, K3, K4 of Table C and of the
entries of T below their levels. Section 4.6 says which statement gives which entries and in which order they
depend on each other. Each statement has the form

> F(s; LO, G): every sequence with exactly s links and x holes, LO < x <= G, has at most P_s(x) rows,

for a table P whose rows P_0, ..., P_(s-1) are valid at all holes up to G and whose row P_s is valid at
x <= LO.

### 4.2 The search rule

This is the rule of [P] section 8.1, written for levels.

A *counterexample* is a sequence with exactly s links and x holes, LO < x <= G, that has more than P_s(x)
rows. Let pi be a counterexample with the fewest rows. Renaming the symbols, its first row starts at the word
1 2 3 4 5 6 7.

*Lemma PART.* Every contiguous part of pi other than pi itself, with u links and e holes, has at most
P_u(e) rows.

Proof. The part is a sequence with exactly u <= s links and e <= x <= G holes. If u < s the row P_u is valid
at e. If u = s and e <= LO the row P_s is valid at e. If u = s and e > LO the part is not a counterexample,
because it has fewer rows than pi. QED

Cut pi after one of its rows into a prefix A (r rows, d holes, t links) and a rest B with e = x - d
holes. B has s - t links if the cut link has weight 3 and s - t - 1 if it has weight 4. By Lemma PART,
r = rows(pi) - rows(B) > P_s(x) - P_(s-t)(x - d), or the same with s - t - 1.

*Rule.* A level x is *allowed* for a prefix with r rows, d holes and t links if LO < x <= G, x >= d and
r + P_(s-t)(x - d) > P_s(x), or t < s and r + P_(s-t-1)(x - d) > P_s(x). The search is a depth-first search
over prefixes that start at 1 2 3 4 5 6 7. A prefix with r rows, d holes and t links is

- a *violation* if t = s, LO < d <= G and r > P_s(d);
- continued by every row that starts at one of the 5 successors of weight 3 of its exit, if some level x with
  LO < x <= G and x >= d has r + P_(s-t)(x - d) > P_s(x);
- continued by every row that starts at one of the 23 successors of weight 4, if t < s and some such level has
  r + P_(s-t-1)(x - d) > P_s(x).

A row that starts at a vertex is tried with every number of blocks from 1 to 6 for which its classes are new.
Every proper prefix of pi satisfies the condition for the link that follows it, with the level x of pi, and pi
is a violation. So if the search reports no violation, F(s; LO, G) holds. I call this the plain rule. K5 to
K8 were run with it.

### 4.3 Lemma RV: reading a sequence backwards

Let rev(u) be the word u read backwards and `rho(e) = rev(sigma^-1 e)`.

*Lemma RV.* (1) rho is an involution on the 5,040 words and maps classes onto classes, bijectively on the
720 classes. (2) The block entered at e, read backwards, is the block entered at rho(e); its exit is rev(e).
(3) tau2(rho(tau2 e)) = rho(e). (4) For words q, v in different classes and w = 3 or 4: the step from the exit
of the block of q to v has weight w if and only if the step from the exit of the block of rho(v) to rho(q) has
weight w.

Proof. Write e = a b c d e f m. (2) The block of e is the word a b c d e f m a b c d e f. Read backwards it is
f e d c b a m f e d c b a, which is the word f e d c b a m = rev(m a b c d e f) = rho(e) followed by its first
6 letters. Its last 7 letters, which are the exit, are m f e d c b a = rev(e). (1) By (2) the exit of the
block of rho(e) is rev(e), so sigma^-1 rho(e) = rev(e) and rho(rho(e)) = rev(rev(e)) = e. Since
rev(sigma u) = sigma^-1 rev(u), rho maps the class of e onto the class of rev(e), and rev permutes the
classes. (3) tau2 e = b c d e f a m, sigma^-1 of it is m b c d e f a, so rho(tau2 e) = a f e d c b m and
tau2 of that is f e d c b a m = rho(e). (4) By the definition of ew, ew(u, v) = ew(rev v, rev u). The exit of
the block of rho(v) is rev(v), and rho(q) = rev(sigma^-1 q), so
ew(exit of rho(v), rho(q)) = ew(rev v, rev(sigma^-1 q)) = ew(sigma^-1 q, v). QED

*Corollary RV.* Let R_1, ..., R_T be a sequence. Replace every row (e, l) by the row (rho(last entry), l)
and take the rows in the order R_T, ..., R_1. The result is a sequence with the same number of rows, the same
holes row by row in reverse order and the same link weights in reverse order.

Proof. By (3) the row (rho(last entry of R), l) has the entries rho(tau2^(l-1) e), ..., rho(tau2 e), rho(e):
the blocks of R read backwards. By (1) the classes stay pairwise different. Its exit is rev(e) by (2). By (4)
with q the last entry of R_i and v the entry of R_(i+1), the link from the new row of R_(i+1) to the new row
of R_i has the weight of the link from R_i to R_(i+1). QED

Lemma RV was also checked from the definitions on all 5,040 entries and all pairs of successors by three
programs (`revchk.py` of mine, the referee's `rv.py`, the selftest of the second program; none of them is in
this repository). In Lean (`KRev.lean`) it is proved from the definition of the link on words, for every
number of symbols.

### 4.4 Lemma REV: the dip is not deeper than the peak

Fix integers a > 0 and h >= 0 and an integer b. A sequence with T rows has the cuts 0, 1, ..., T; cut i is
behind row i, and for 0 < i < T it carries link i, between the rows i and i + 1. The potential of a cut is

    phi_i = a i - b (holes of the rows 1..i) - 2 h (links of weight 4 among the links 1..i-1)
            - h [link i has weight 4],

so phi_0 = 0 and phi_T = a T - b H - 2 h s for a sequence with H holes and s links. Let m be the least and M
the largest of phi_0, ..., phi_T. Then m <= 0.

*Lemma REV.* Let pi be any sequence with T rows and pi' be pi read backwards (Corollary RV), with
potentials phi', m', M'. Then phi'_i = phi_T - phi_(T-i) for every i. Hence m' = phi_T - M, M' = phi_T - m
and phi'_T = phi_T. So one of pi and pi' has m + M >= phi_T.

Proof. Cut i of pi' is cut T - i of pi. Rows and holes are additive, which gives the terms with a and b. The
links of pi' before its cut i are the links T-i+1, ..., T-1 of pi, and the link at its cut i is link T - i of
pi. So

    phi'_i = a i - b (holes of the rows T-i+1..T) - 2 h (heavy among the links T-i+1..T-1) - h [link T-i heavy],
    phi_T - phi_(T-i) = a i - b (the same holes) - 2 h (heavy among the links T-i..T-1) + h [link T-i heavy],

where "heavy" means weight 4, and the two are equal. So (m + M) + (m' + M') = 2 phi_T. QED

The reversal of a counterexample with the fewest rows is again one: it has the same rows, holes and links.
After renaming the symbols it starts at 1 2 3 4 5 6 7. So there is a counterexample pi with the fewest rows
that starts at 1 2 3 4 5 6 7 and has

    (4.1)    m + M >= phi_T.

The search may look for this one only. Let its level be x and put c(x) = a (P_s(x) + 1) - b x - 2 h s. Since
pi has at least P_s(x) + 1 rows and a > 0, phi_T >= c(x).

*Lemma CUT.* Let 0 < i < T. Let the prefix of i rows have d holes and t links inside, put
f = a i - b d - 2 h t and let m_i and M_i be the least and the largest of phi_0, ..., phi_i. Put, for e >= 0,

    seg(e) = max over 0 <= u <= s - t of  a P_u(e) - b e - 2 h u,
    U(y)   = max over t <= t' <= s of     a P_t'(y) - b y - 2 h t'.

Then at least one of these holds: m_i = 0; M_i + m_i >= c(x); m_i + min(U(d + e), f + seg(e)) >= c(x) for
some 0 <= e <= x - d.

Proof. Let m_i < 0. Then m <= m_i < 0 and by (4.1) M >= phi_T - m >= phi_T - m_i > phi_T. So M is attained at
a cut i* < T.
If i* <= i then M_i = M, and M_i + m_i >= M + m >= phi_T >= c(x).
If i* > i, the rows i+1, ..., i* are a contiguous part of pi other than pi, with e >= 0 holes and u <= s - t
links inside. The links of weight 4 among the links i, ..., i*-1 are link i, if it is heavy, and those u. So

    phi_i* - phi_i = a (i* - i) - b e - 2 h u - h [link i heavy] - h [link i* heavy] <= a P_u(e) - b e - 2 h u

by Lemma PART and h >= 0, which is at most seg(e). Since phi_i <= f, phi_i* <= f + seg(e). The prefix of i*
rows is also a part of pi other than pi, with d + e <= x holes and t' links inside, t <= t' <= s, so
phi_i* <= a P_t'(d + e) - b (d + e) - 2 h t' <= U(d + e) by Lemma PART. Finally
phi_i* = M >= phi_T - m_i >= c(x) - m_i. QED

*The rule with the reversal cut.* A prefix is continued only if the plain rule continues it and, in
addition, m_i = 0 or some level x that is allowed for it has

    M_i + m_i >= c(x)     or     m_i + max over 0 <= e <= x - d of min(U(d + e), f + seg(e)) >= c(x).

Here phi_i depends on the link that follows the prefix: phi_i = f for a link of weight 3 and f - h for a link
of weight 4. So m_i and M_i are taken separately for the two kinds of continuation, and each child inherits
the pair that belongs to its link. The test for a violation is made at every row placed, before any cut. The
programs tabulate the two conditions as A1 = min of c(x) and A2 = min of (c(x) - max_e min(U, f + seg)) over
the allowed levels of (t, d, r).

### 4.5 Why a run without violation proves the statement

Suppose F(s; LO, G) fails. Take the counterexample pi of (4.1). Every proper prefix of pi satisfies the plain
rule for the link that follows it (section 4.2), with the level x of pi, so x is an allowed level; and it
satisfies the additional condition for this x by Lemma CUT. So the search does not cut any prefix of pi,
reaches pi and reports a violation. Hence a run that reports no violation proves F(s; LO, G), given the rows
of fewer links up to G holes and the row P_s up to LO. Both rules apply the tables only to contiguous parts
of pi other than pi itself (Lemma PART). The potential (a, b, h) is free; it changes the size of the tree, not
the statement. The potentials used are 2, 3, 5 for chains; 10, 15, 30 for 1 link; 10, 16, 25 for 2 links;
10, 16, 30 for 3 links; 10, 16, 25 for 4 links.

The first program for K0 to K4 also uses a row mask: at a parent it does not place a row whose prefix would
be neither a violation nor kept. This does not change the set of kept prefixes or of violations. Both
programs cut a statement into parts at a gate: the kept prefixes with a fixed number of rows are numbered in
the order of the search and part i takes the numbers congruent to i. A statement holds when every part is
present and no part reports a violation.

### 4.6 The statements and the order in which they depend on each other

| | statement | table | rule | given |
|---|---|---|---|---|
| K8 | F(8; -1, 42) | D^u_8 | plain | T_0, ..., T_7 at x <= 42 |
| K7 | F(7; -1, 48) | D^u_7 | plain | T_0, ..., T_6 at x <= 48 |
| K6 | F(6; -1, 54) | D^u_6 | plain | T_0, ..., T_5 at x <= 54 |
| K5 | F(5; -1, 60) | D^u_5 | plain | T_0, ..., T_4 at x <= 60 |
| C76 | F(0; 75, 76) | D | reversal, 2, 3, 5 | T_0 at x <= 75 |
| K0 | F(0; 76, 90) | D | reversal, 2, 3, 5 | D_0 at x <= 76 |
| K1 | F(1; 61, 84) | D | reversal, 10, 15, 30 | D_0; D_1 at x <= 61 |
| K2 | F(2; 60, 78) | D | reversal, 10, 16, 25 | D_0, D_1; D_2 at x <= 60 |
| K3 | F(3; 54, 72) | D | reversal, 10, 16, 30 | D_0, D_1, D_2; D_3 at x <= 54 |
| K4 | F(4; 47, 66) | D | reversal, 10, 16, 25 | D_0, ..., D_3; D_4 at x <= 47 |

Proof of Theorem K from the statements.

- s = 5, 6, 7, 8. LO = -1, so the run proves the whole row D_s from the rows of fewer links in T. These rows
  are valid by section 2.2: for K6, K7, K8 they rest on set B and Lemma CL only; for K5 also on I1, because a
  chain inside a sequence with at most 60 holes may have 59 holes. The four statements do not depend on each
  other or on any other statement of Table C.
- s = 0. D_0(x) = T_0(x) for x <= 75, valid by (L2), I1 and I2. C76 gives D_0(76) = 120. K0 gives the levels
  77 to 90.
- s = 1, 2, 3, 4. Below its LO the row D_s equals T_s = P_s of set B (the first level where D is below T is
  LO + 1, section 2.3). Above LO it is given by K_s, which needs the rows D_0, ..., D_(s-1). So K1 needs K0;
  K2 needs K0 and K1; K3 needs K0, K1 and K2; K4 needs K0 to K3. A part of a sequence with at most
  90 - 6 s holes has at most that many holes, so the proof of K_s needs the earlier rows only up to
  90 - 6 s holes.

So K3 and K4 are proved as statements only together with K0, K1 and K2: a run of K_s that finds no violation
says nothing if an earlier row is wrong. QED

In Lean the statements K6, K7, K8 read the rows D_5, D_6, D_7 instead of T_5, T_6, T_7 (section 0.1); there
K5, K6, K7, K8 are proved in this order.

## 5. The joint statements

### 5.1 Pieces and the statement J

A *piece* is a sequence with at most s links, written S<s>, or a ring, written R, with val and wt as in
section 1. Different pieces may have classes in common.

> J(p_1 ... p_n; V, W; B): there are no pieces p_1, ..., p_n of the given kinds with sum val >= V,
> sum wt <= W and sum over the 720 classes of max(0, (number of pieces that contain the class) - 1) <= B.

The last sum is the number of *shared classes*. If J(p; V, W; B) holds, so does every statement with
kinds S<s'> for s' <= s in place of S<s>, with V' >= V, W' <= W and B' <= B: its objects are objects of the
first.

### 5.2 From a configuration to pieces

*Lemma PIECE.* Let c be as in section 3 and take the items of Proposition PROF, none of them of a kind A'
or B'. The objects behind the items are pieces with

    sum of val = (sum of the values v behind the items) + sum of the shifts dv  >=  45 + sum of dv,
    sum of wt  = (sum of the weights of the items) - sum of the shifts dw       <=  90 - sum of dw,
    shared classes <= number of items of the kinds Z and A_q and B_q,

with the shifts

| item | piece | dv = val - v | dw = w - wt | borrows a class |
|---|---|---|---|---|
| kernel K_s(x) | S<s> | 0 | 0 | no |
| Z(x) | R | 6 | 7 | yes: the class X of (G5) |
| A_1(x) | R | 6 | 7 | yes: the class of the slot |
| A_q(x), q >= 2 | S<q-2> | 11 | 13 | yes: the class of the slot |
| B_q(x) | S<q-1> | 11 | 13 | yes: the class X of (G5) |
| E_q(x) | S<q> | 10 | 12 | no |

Proof. The shifts, from the objects of Lemma ITEM. Z: the ring has m - 1 rows and h - 7 holes, so
val = m - h + 6 = v + 6 and wt = h - 7 = w - 7. A_1: the ring has m rows and h - 1 holes, so
val = m - h + 1 = v + 6 and wt = h - 1 = (h + 6) - 7. A_q: val = m - (h - 1) - 5 (q - 2) = v + 11 and
wt = h - 1 + 6 (q - 2) = (h + 6 q) - 13. B_q: val = (m - 1) - (h - 7) - 5 (q - 1) = v + 11 and
wt = h - 7 + 6 (q - 1) = (h + 6 q) - 13. E_q: val = m - h - 5 q = v + 10 and wt = h + 6 q = w - 12, where in
case (a) of section 3.5 v and w are the second brackets. The inequalities for the sums are those of
Proposition PROF.

Shared classes. The blocks of a piece are blocks of the component it comes from, plus one more block for the
kinds Z, A_q, B_q: the block of the class X in the merged row, or the block of the class of the slot in the
extended row. By (G4) and (G5) that class contains no block of the component, so the piece has pairwise
different classes, and I say the piece borrows the class. The pieces K1 and K2 of case (a) are disjoint parts
of the kernel. In a valid configuration every class is a block exactly once, so the blocks of different
components, and of K1 and K2, lie in different classes. Hence a class is contained in at most one piece as a
block of the configuration, and otherwise only in pieces that borrow it:
(number of pieces that contain the class) - 1 is at most the number of pieces that borrow it. Summed over the
classes this is at most the number of borrowing pieces. QED

### 5.3 The five statements and the shapes they remove

| | statement | removes the shapes | profiles |
|---|---|---|---|
| S1 | J(S4 S4; 55, 78; 1) | K_s+E_q; K_s+A_q with q >= 2; K_s+B_q | 3,358 |
| S2 | J(S5 R; 51, 83; 1) | K_s+Z, K_s+A1 | 1,792 |
| S3 | J(S2 R R; 57, 76; 2) | K_s plus two of A1, Z | 682 |
| S4 | J(S1 S1 R; 61, 71; 1) | K_s plus one of A1, Z plus E_q | 380 |
| S5 | J(S0 S0 R; 62, 70; 2) | K0 plus one of A1, Z plus one of A2, B1 | 92 |

3,358 + 1,792 + 682 + 380 + 92 = 6,304 = 6,429 - 125.

The 60 shapes with two or three pieces, with the statement that Lemma PIECE gives for each (pieces; V, W; B)
and the number of profiles in brackets:

- (S<s> S<q>; 55, 78; 0), implied by S1: K0+E0 (490), K0+E1 (325), K0+E2 (105), K0+E3 (10), K0+E4 (17),
  K1+E0 (322), K1+E1 (141), K1+E2 (28), K2+E0 (105), K2+E1 (28), K2+E2 (2), K3+E0 (10), K4+E0 (15).
- (S<s> S<t>; 56, 77; 1), implied by S1: K0+A2 (341), K0+A3 (196), K0+A4 (36), K0+B1 (341), K0+B2 (196),
  K0+B3 (36), K1+A2 (195), K1+A3 (64), K1+A4 (6), K1+B1 (195), K1+B2 (64), K1+B3 (6), K2+A2 (36), K2+A3 (6),
  K2+B1 (36), K2+B2 (6).
- (S<s> R; 51, 83; 1), implied by S2: K0+A1 (474), K0+Z (474), K1+A1 (287), K1+Z (287), K2+A1 (75),
  K2+Z (75), K3+A1 (18), K3+Z (18), K4+A1 (35), K4+Z (35), K5+A1 (7), K5+Z (7).
- (S<s> R R; 57, 76; 2), implied by S3: K0+A1+A1 (148), K0+A1+Z (275), K0+Z+Z (148), K1+A1+A1 (28),
  K1+A1+Z (45), K1+Z+Z (28), K2+A1+A1 (3), K2+A1+Z (4), K2+Z+Z (3).
- (S<s> S<q> R; 61, 71; 1), implied by S4: K0+A1+E0 (180), K0+E0+Z (180), K0+A1+E1 (5), K0+E1+Z (5),
  K1+A1+E0 (5), K1+E0+Z (5).
- (S0 S0 R; 62, 70; 2), which is S5: K0+A1+A2 (23), K0+A1+B1 (23), K0+A2+Z (23), K0+B1+Z (23).

In every line the numbers of links fit: in the first two lines both sequences have at most 4 links (A_q gives
q - 2 links, B_q gives q - 1); in the third s <= 5; in the fourth s <= 2; in the fifth s, q <= 1. The values
V, W, B are 45 + sum dv, 90 - sum dw and the number of borrowing pieces: for example K0+A1+B1 gives
45 + 6 + 11 = 62, 90 - 7 - 13 = 70 and 2. I recomputed this list from `shapes_D15_CAP.tsv` with a script of
mine (`chk2.py`); another program of mine (`stmts.py`) does the same on every profile, and the referee's check
has its own mapping. None of these is in this repository.

### 5.4 The search and why it is complete

Let J(p_1 ... p_n; V, W; B) fail and take a counterexample with the fewest rows in all. The pieces are
searched in the order p_1, ..., p_n; the order does not change the statement. For piece i let `need` be V less
the values of the pieces 1 to i - 1 and `left` be W less their weights. Let Best_(i+1)(b) be the largest
total of table values of single pieces of the kinds p_(i+1), ..., p_n within total weight b, where the table
value of S<s> at weight y is the largest T'_t(y - 6 t) - (y - 6 t) - 5 t over t <= s and that of R at weight
y is TR'(y) - y; Best_(n+1) = 0.

1. *Start.* Renaming the symbols, piece 1 starts at 1 2 3 4 5 6 7 (a ring piece after the rotation of step
   5). All conditions are invariant.
2. *Record.* Every sequence piece S of the counterexample has val(A) < val(S) for every proper prefix A.
   Otherwise replace S by A: fewer rows, the value not smaller, the weight not larger, no new shared class.
3. *Rest.* For every cut S = A ++ B of a sequence piece into two non-empty parts: val(A) >= 1 if the cut link
   has weight 3, and val(A) - 5 >= 1 if it has weight 4. Otherwise val(B) >= val(S), and S is replaced by B
   as in step 2.
4. *Table bound.* Let A be a prefix of the sequence piece p_i = S<s> with t links, followed by a rest B with
   t'' links and e holes, t'' <= s - t for a cut link of weight 3 and t'' <= s - t - 1 for weight 4. B alone
   is a sequence, so rows(B) <= T'_t''(e). Each later piece is a single object, so the later pieces have total
   value at most Best_(i+1) of the weight that is left for them. So, with g = 0 for weight 3 and g = 1 for
   weight 4, some (t'', e) has

       val(A) - 5 g + T'_t''(e) - e - 5 t'' + Best_(i+1)(left - wt(A) - 6 g - e - 6 t'') >= need.

5. *Ring piece.* By the cycle lemma of [P] section 8.2 a ring with T rows and H holes has a rotation in which
   the first r rows have d holes with d T <= r H for every r. Read in that rotation, a prefix with r rows and
   d holes of the ring piece p_i has a target (T, H) with H <= left, T <= TR'(H),
   T - H + Best_(i+1)(left - H) >= need, r < T, d <= H, d T <= r H and T - r <= T'_0(H - d): the rest of the
   ring is a chain with H - d holes.
6. *Later pieces.* A piece after the first starts at any of the 5,040 words. A row may use a class of an
   earlier piece while the number of shared classes stays at most B.

*The search.* Depth-first over the pieces in order. Piece 1 starts at 1 2 3 4 5 6 7, every later piece at
every word. A prefix A of a sequence piece is

- taken as the whole piece if val(A) is larger than the value of every shorter prefix; then, if it is the
  last piece, an object is *found* when val(A) >= need, and otherwise the search goes on to the next piece
  when val(A) + Best_(i+1)(left - wt(A)) >= need;
- continued by the 5 successors of weight 3 if val(A) >= 1 and the inequality of step 4 with g = 0 holds for
  some (t'', e);
- continued by the 23 successors of weight 4 if it has fewer than s links, val(A) - 5 >= 1 and the inequality
  with g = 1 holds for some (t'', e).

A prefix of a ring piece is taken as the whole piece if it has at least 2 rows and closes with weight 3 (and
then tested like a sequence piece), and it is continued by the 5 successors of weight 3 if a target of step 5
exists. Rows are tried with every number of blocks for which the classes are new in the piece, the weight
stays within `left` and the shared classes within B.

*Completeness.* The pieces of the counterexample, in the order of the search and with the renaming and the
rotations of steps 1 and 5, are reached: every prefix of every piece satisfies the conditions for its
continuation by steps 3, 4 and 5; every completed sequence piece is a record by step 2; the tests when a
piece is completed hold because the later pieces obey Best. So the search finds an object. Hence "found 0"
proves J, given table T'. A ring piece that is not the first starts at every word, so its rotation of step 5
is among the starts.

The steps 2 and 3 use that the counterexample has the fewest rows; the steps 4 and 5 use the tables on
single pieces and on parts of one piece, never on two pieces together.

### 5.5 The parts of S2, and S2b from the kernel alone

S2 = J(S5 R; 51, 83; 1) is searched with the ring first, split by the number H of holes of the ring:
S2a1 (H >= 16), S2a2 (8 <= H <= 15), S2b (H <= 7). The three windows cover all rings, so S2 is their
conjunction. In a run with a window the ring row is read only inside the window.

*S2b follows from Corollary K.* PR(H) - H for H = 0, ..., 7 is 5, 4, 3, 2, 1, 0, 4, 3 (set B), so a ring
with at most 7 holes has val <= 5 by FR. In a counterexample to S2b the sequence, which has at most 5 links,
would then have val >= 46 within wt <= 83. Corollary K excludes it. So S2b depends on K0 to K5, and S2 is
proved only when K0, K1 and K2 have ended.

S2a1 and S2a2 read the row T'_5, which is D_5 up to 60 holes, so they rest on K5. The rows 0 to 4 of T' are
those of T, apart from the entry 120 at 76 holes, which is C76. So S1, S3, S4, S5 and the two parts of S2
that are searched do not depend on K0 to K4.

### 5.6 One difference between the first joint program and this text

In `jt.c`, the first joint program, the value still needed by a ring piece is replaced by 0 when it is
negative. The rule of section 5.4 does not do this. It has no effect on the five statements. In S2a1 and S2a2
the ring is the first piece and `need` is 51. In S3, S4, S5 a negative `need` at a ring means that the earlier
pieces have total value at least V + 1; then the table bound of the whole statement, Best_1(W), is at least
V + 1 + 5 = V + 6, because a ring with 0 holes has table value 5. But Best_1(W) is 61 for S3 (V = 57), 64 for
S4 (V = 61) and 64 for S5 (V = 62). So the case does not occur. The second program does not replace the value,
and its counts are equal. Neither does the Lean search.

## 6. Conclusion

*Theorem.* Given Theorem K and the statements S1, S2a1, S2a2, S3, S4, S5, statement (*) holds: no valid
configuration on 7 symbols has cost at most 135. Hence, by (L1), a superpermutation on 7 symbols has at least
5,900 letters.

Proof. Let c be valid with cost at most 135. By Proposition PROF it gives a surviving profile, together with
one object for each item. By KN the shape of the profile is one of 69, and no item is A' or B'.

*One piece.* The profile is a kernel item alone. If eps_K = 0 the kernel is a sequence, and since no other
component has positive value, val = v(K) >= sum v >= 45 and wt = w(K) <= 90. If eps_K = 1 the item is that of
K1, and the item of K2 was left out because m2 - h2 - 5 (s2 + 2) <= 0; then val(K1) >= v(K) >= 45 and
wt(K1) <= w(K) <= 90. Both contradict Corollary K.

*Two or three pieces.* By Lemma PIECE the objects are pieces with sum val >= V, sum wt <= W and at most B
shared classes, for the (pieces; V, W; B) of the shape in section 5.3. That statement is implied by one of
S1 to S5, and S2 holds by S2a1, S2a2 and section 5.5. Contradiction.

So every one of the 6,429 profiles is removed and c does not exist. QED

The argument does not use that the cost is exactly 135; it does not use the theorem of 5,899 as such, only
its tables and lemmas. The model is exact (`no_stdConfig_iff`), so (*) is equivalent to the bound 5,900 and
nothing is lost by the reduction.

Dependencies in one picture:

    (L2) set B, I1, I2, I4, Lemma CL  ->  T        K5..K8  ->  T'
    T, C76  ->  K0  ->  K1  ->  K2  ->  K3  ->  K4
    T'  ->  S1, S2a1, S2a2, S3, S4, S5
    K0..K5  ->  S2b

## 7. How to check this

### 7.1 The Lean proof

The Lean proof of 5,900 is the package `proofs/lean/n7_5900/`: the sources of the modules of defect 15 in
`proofs/lean/n7_5900/LowerBounds/` and `proofs/lean/n7_5900/build.sh`, which builds them on top of the Lean
proof of 5,899 in `proofs/lean/n7/`. The final theorem is `covers_lower_bound_7_5900_native` in
`proofs/lean/n7_5900/LowerBounds/F5900Native.lean`, and `proofs/lean/n7_5900/Audit5900Native.lean` prints its
axioms (section 0.1). The trusted base of level 2 is the one described in `proofs/lean/n7/README.md`, with the
engines `KSearch.lean` and `J15Search.lean` added to `PSearch.lean`.

### 7.2 The programs

The programs of this section are mine and are not in this repository. Their results are the counts of Table
C. They are a cross-check of the Lean evaluation, which is the proof at level 2. The names below identify the
programs. Tables: `capD15.txt` (D), `capD15u_5.txt` to `capD15u_8.txt` (D^u), `caps7.txt` (T) and `caps7b.txt`
(T'). D and T' are also written out in `proofs/lean/n7_5900/LowerBounds/KTables.lean` (section 2.3).

| | first program | second program | card program |
|---|---|---|---|
| K5 to K8 | `pproto.c` | `k2.cpp` | `gk4.cu` (K6 only) |
| C76, K0 to K4 | `kfast.c` (`kfast_v1.c` for C76) | `k2.cpp` | `gk4.cu` |
| S1 to S5 | `jt.c`, built as `jtp.exe` | `j2.cpp` | `gj.cu` |
| I1, I2, I4 | earlier programs of mine | `k2.cpp` (I1, I2), `j2.cpp` (I4) | |

The card programs are CUDA sources with a host part in C (`gk4.c`, `gj.c`). One thread of the card does one
depth-first walk with the rule of the first program. `gk4` takes the code that builds the tables from
`kfast.c`; its search is written anew. A statement is cut into parts at a gate as on the processor.

`pproto.c` is the C prototype of the search engine of the Lean proof. `k15.c` is its search with the reversal
cut added; `kfast.c` is generated from `k15.c` and adds the row mask. The second program builds the geometry
(5,040 entries, 720 classes, 5 successors of weight 3 and 23 of weight 4) from the definitions and was written
from these texts: [P] sections 8.1 and 8.2 and two notes of mine on the cuts of the kernel search and on the
joint search (not in this repository). `j2.cpp` is put together from `j2_body.cpp` and the geometry of
`k2.cpp` by `mkj2.py`.

### 7.3 The runs

THREADS is the number of threads. Parts that are present are skipped, so a line can be repeated after a stop.
The lines record the arguments of every run.

First program, kernel alone:

    ./pproto_my.exe 7 tabs S 90 capD15u_S.txt                  # K5..K8: S = 5, 6, 7, 8
    LO=75 CUT=12 POTA=2 POTB=3 POTH=5 ./kfast_v1.exe run 0 76 capD15.txt               # C76
    ./runparts.sh 4 47 256 12 THREADS 10 16 25      ;  ./summ.sh 4 256                 # K4
    ./runparts.sh 3 54 1024 13 THREADS 10 16 30     ;  ./summ.sh 3 1024                # K3
    ./runparts.sh 2 60 4096 14 THREADS 10 16 25     ;  ./summ.sh 2 4096                # K2
    ./runparts.sh 1 61 8192 17 THREADS 10 15 30     ;  ./summ.sh 1 8192                # K1
    ./runparts.sh 0 76 16384 18 THREADS 2 3 5       ;  ./summ.sh 0 16384               # K0

The arguments of `runparts.sh` are S, LO, the number of parts, the depth of the gate, the threads and the
potential a, b, h.

First program, joint statements:

    ./jtp.exe 7 caps7b.txt run 62 70 2 S0 S0 R                                               # S5
    ./jtp.exe 7 caps7b.txt run 61 71 1 S1 S1 R                                               # S4
    ./run_parts.sh RRS 2000 14 THREADS caps7b.txt 57 76 2 S2 R R ;  ./summ_parts.sh RRS 2000 # S3
    RLO=16 ./run_parts.sh R16 2000 20 THREADS caps7b.txt 51 83 1 R S5                        # S2a1
    ./summ_parts.sh R16 2000
    RLO=8 RHI=15 ./run_parts2.sh ./jtp.exe R8 40 8 250 THREADS caps7b.txt 51 83 1 R S5       # S2a2
    ./summ_parts.sh R8 10000
    ./run_parts.sh TU 6000 16 THREADS caps7b.txt 55 78 1 S4 S4   ;  ./summ_parts.sh TU 6000  # S1

Second program (`./k2c.exe selftest` checks the geometry and Lemma RV):

    ./rk.sh L5 capD15u_5.txt 5 -1 -1 0 1 1 1 12 1024 THREADS                 # K5; K6..K8 alike
    ./rk.sh L4 capD15.txt 4 47 66 12 10 16 25 12 256 THREADS                 # K4
    ./rk.sh K3 capD15.txt 3 54 72 12 10 16 30 18 2048 THREADS                # K3
    ./rk.sh K2 capD15.txt 2 60 78 12 10 16 25 17 8192 THREADS                # K2
    ./rk.sh K1 capD15.txt 1 61 84 12 10 15 30 18 8192 THREADS                # K1
    ./rk.sh K0 capD15.txt 0 76 90 12 2 3 5 17 8192 THREADS                   # K0
    ./rk.sh C76 capD15.txt 0 75 76 12 2 3 5 22 64 THREADS                    # C76
    ./rk.sh C59 capD15.txt 0 58 59 12 2 3 5 12 64 THREADS                    # I1
    ./rk.sh C62 capD15.txt 0 61 75 12 2 3 5 22 1024 THREADS                  # I2
    ./rj.sh R69 512 THREADS ringtab caps7b.txt 0 69 18                       # I4
    ./rj.sh S4 64 THREADS J caps7b.txt 61 71 1 0 96 1 10 S1 S1 R             # S4; S5 alike
    ./rj.sh S3 2048 THREADS J caps7b.txt 57 76 2 0 96 1 16 S2 R R            # S3
    ./rj.sh S2a1 2048 THREADS J caps7b.txt 51 83 1 16 96 1 26 R S5           # S2a1
    ./rj.sh S2a2 8192 THREADS J caps7b.txt 51 83 1 8 15 2 6 R S5             # S2a2
    ./rj.sh S1 8192 THREADS J caps7b.txt 55 78 1 0 96 1 16 S4 S4             # S1
    python summ.py TAG          # kernel statements and I2
    python summj.py TAG         # joint statements and I4

Card program, K2, K1 and K0:

    ./gparts.sh 2 60 16 14 10 16 25 capD15.txt 90  ;  ./gsumm.sh 2 16     # K2, 733 s
    ./gparts.sh 1 61 16 17 10 15 30 capD15.txt 90  ;  ./gsumm.sh 1 16     # K1, 590 s
    ./gparts.sh 0 76 16 18 2 3 5 capD15.txt 90     ;  ./gsumm.sh 0 16     # K0, 599 s

The arguments of `gparts.sh` are S, LO, the number of parts, the depth of the gate, the potential a, b, h, the
table file and the top weight. The seconds are those of one CUDA card with 32 GB.

The arguments of `rk.sh` are the tag, the table file, S, LO, G (-1 -1: all levels), the cut (0 plain, 12
reversal), the potential a, b, h, the depth of the gate, the number of parts and the threads. Those of
`rj.sh` in mode J are the tag, the number of parts, the threads, the table file, V, W, B, the window of ring
holes, the piece that carries the gate, the depth of the gate and the pieces.

The knapsack: `python acc15.py 15 CAP` (section 3.7). It writes two files into the current directory, so run it
from a copy if the files there are to be kept.

### 7.4 What a result looks like and what to compare

First program, plain rule, one line per run:

    tabs K=7 S=8 GTOP=90 (holes <= 42): violations 0   rows placed 232757   kept 32407

First program with the reversal cut, one line per part (broken into three here), and the last line of
`summ.sh`:

    run S=4 GTOP=90 (holes <= 66) LO=47 CUT=12 POT=10,16,25 part 7 of 256 at depth 12: violations 0
        rows placed 205173409   kept 113266897   above the gate: rows placed 89354 kept 30378
        prefixes at the gate 58971   time 9.7s  (0.0858 us per kept)
    RESULT: no violation, all parts present

First joint program, per part or per run, and the line of `summ_parts.sh`:

    RESULT: found 0   kept 18636502   rows tried 93360081   time 2.7s (0.0287 us per row tried)
    parts finished 2000 of 2000   found 0   kept ...   rows tried ...

Second program, one file per part, and the last line of `summ.py` or `summj.py`:

    k2 statement: tables 8f1f7cc3012453b8 S 3 LO 54 G 72 CUT 12 potential 10,16,30
    gate: depth 18 parts 2048 gate_count 1236034 kept_top 1685398 placed_top 8948077 violations_top 0
    part 7 kept_below 19185427 placed_below 71057630 violations_below 0
    RESULT: all parts present, headers agree, no violation        (or: ... found 0)

Compare with Table C: the number of kept prefixes for the kernel statements and the inputs; "kept" and
"tried" for the joint statements ("rows tried" of the first program is "tried" of the second). With the same
rule these are fixed numbers that do not depend on the gate or on the number of parts. "Rows placed" and the
gate counts depend on the program and are not reference counts. A program with another valid rule only has to
find nothing. `summ_parts.sh` counts result lines only; for the finished statements I checked in addition
that every part index is present and that every part says "found 0".

Tests of the programs that are on file (all of them mine or the referee's, none in this repository):

- Kernel, first program: a validation script runs 103 cases with 0 to 4 links, in which a table entry that is
  attained is lowered by one and the search with the reversal cut must report the violation; it does in all
  cases, for each potential used. Plain rule and reversal cut were compared on small statements between three
  builds (7 links: 29,066,365 and 24,856,368 kept; chains to 52 holes: 111,443,191 and 84,697,457).
- Reversal cut, the referee's own program on 5 and 6 symbols: the plain search and the search with the cut,
  with 10 potentials, against ground truth from exact tables: 66,000 + 6,600 + 1,100 searches, no mismatch.
- Joint, first program: on 5 symbols without cuts the number of joint objects equals a Python count from the
  definitions in 30 cases; on 6 symbols "found" with and without cuts agrees in 392 cases; on 7 symbols
  J(S0 S0; 60, 72; 0), which is Lemma FF for two chains, gives found 0 with 635,179 kept in both programs,
  and J(S0 S0; 30, 24; 0) is false and objects are found.
- Second program, negative controls: M(12) lowered to 26 gives violations; PR(40) lowered to 64 gives the
  ring with 65 rows and 40 holes; J(S0 S0; 30, 24; 0) gives 1,612 objects.
- Conversions of section 3.4, 3.5 and 5.2: the referee's `pieces.py` checked every conversion from the
  definitions on 26 known certificates, on all 877 enumerated configurations on 5 symbols and on random
  hanging components with seams of weight 3, 4, 5 and attachments of cost 0, 1, 2 (11,000 on 6 symbols, 1,500
  on 7 symbols, all kinds including A', B' and E).

### 7.5 What has not been done

- A second joint search by the referee. The referee's check read `jt.c` against the rule; it did not write a
  joint search of its own. The second program is the independent joint search. The Lean search is proved
  complete at level 1.
- No end-to-end check on 6 symbols. It is not possible in principle. On 6 symbols the chain with 22 rows
  and 14 holes has value 8 = 24 - 4 D at D = 4, so the analogue of Corollary K is false there although no
  configuration of defect 4 exists. The method is a sufficient condition, and on 6 symbols it does not apply.
  The parts were tested on 5 and 6 symbols separately (section 7.4).
- An audit of all part files in one pass. For every statement: every part index present, equal statement
  lines, equal gate counts, no violation. The scripts of the second program do this; for the first joint
  program I did it by hand for the finished statements.
