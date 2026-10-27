# The coefficient 61937/120960 in Lean

This directory is a second development in the style of [`../constant/`](../constant/README.md). It proves, for
superpermutations on $`n`$ symbols,

```math
L(n) \le F_3(n) + \left(\tfrac{61937}{120960} + o(1)\right)(n-3)!, \qquad F_3(n) = n! + (n-1)! + (n-2)!
```

```math
\tfrac{61937}{120960} = \tfrac{1771}{3456} - \tfrac{1}{2520} = 0.512045\ldots
```

for every $`n \ge 13`$. The coefficient of `../constant/` is $`\tfrac{1771}{3456} = 0.512442\ldots`$, and Pantone's is $`\tfrac{43}{80} = 0.5375`$.
The construction is Pantone's. The change from `../constant/` is one choice inside it, the cycle re-choice:

* In `../constant/` the short walks of the 48 groups on 12 symbols are covered by 48 of the 203 connector cycles
  found on 12 symbols. Here the three short walks of each group, written nine times and transported from port 0,
  get connector cycles of their own on 13 symbols. A minimum cover of their 30 trails needs 6 cycles per group,
  288 in all (`gen_cert.py` finds it with an integer programme and writes the pointers). The 155 cycles on 12
  symbols that the long walks use stay.
* So the cycles on 13 symbols number 7,731 where `../constant/` has 7,875, and the cost of the cycles drops from
  $`\tfrac{25}{1152}`$ to $`\tfrac{859}{40320}`$ of $`(n-3)!/(n-3)`$.

The Lean kernel checks every proof. There is no `native_decide` and no `sorry`. The theorems below depend on
the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## The theorems

`Covers`, `HasWord` and `F3` are the definitions of Pantone's `Challenge.lean`, as in `../constant/`.

```lean
-- SuperpermutationUpperBound61937/Main13.lean
theorem word_thirteen : SuperpermutationBounds.HasWord 13 6747847656

-- SuperpermutationUpperBound61937/Main.lean
theorem finite_bound (m : Nat) (hm : 11 <= m) (a : Nat) (ha : 2 <= a) (ham : a <= m) :
    exists w : List (Fin (m + 2)), SuperpermutationBounds.Covers w /\
      (w.length : Rat) <=
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : Rat)
          + (61937 / 120960 : Rat) * ((m - 1).factorial : Rat)
          + ((a - 2 : Nat) : Rat) * (859 / 40320 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat)
          + ((m - a : Nat) : Rat) *
              min ((859 / 40320 : Rat) * ((m - 1).factorial : Rat) / ((m - 1 : Nat) : Rat))
                (((m + 1).factorial : Rat) / ((a + 1).factorial : Rat))

theorem eventual_bound :
    forall eps : Rat, 0 < eps -> exists N : Nat, 13 <= N /\
      forall K : Nat, N <= K -> exists w : List (Fin K), SuperpermutationBounds.Covers w /\
        (w.length : Rat) <= SuperpermutationBounds.F3 K +
          ((61937 / 120960 : Rat) + eps) * (Nat.factorial (K - 3) : Rat)
```

`Corollaries.lean` adds the same bound in the shape of his `Finite` and `FiniteInteger` (`Cost61937`,
`finite_61937`, `finiteInteger_61937`) and these values of `finite_bound`:

| symbols | statement | parameters |
|---|---|---|
| 13 | `word_thirteen : HasWord 13 6747847656` | m = 11 |
| 14 | `hasWord_fourteen : HasWord 14 93905285310` | m = 12, a = 8 |
| 15 | `hasWord_fifteen : HasWord 15 1401330999486` | m = 13, a = 9 |
| 16 | `hasWord_sixteen : HasWord 16 22320904300200` | m = 14, a = 9 |

These are values of the general formula, not words. The words for 13 symbols in `words/` at the top of this
repository are shorter by about 45,000 letters. There is no `Audit` file for this directory; the statements use
`Covers` and `HasWord` of `Challenge.lean` as they stand.

## The files

`SuperpermutationUpperBound61937/` is `../constant/SuperpermutationUpperBound1771/` with the namespace renamed, so
that the two cannot be confused, and these changes:

| file | change |
|---|---|
| `Hybrid.lean` | `GroupFacts` has no field `safe` (the cover of the short walks by the 48 group cycles). `Cert.circles` holds the 155 long-walk cycles. New fields: `gcircles` (288 cycles on 13 symbols) and `smallPorts` (a `PortsCovered` certificate of the transported short walks) |
| `Thirteen.lean` | the cycles on 13 symbols are three parts (155 extended, 288 group cycles, 6,048 loop words), 7,731 in all; in `safe12` the short walks come from `smallPorts` |
| `AllSizes.lean`, `GenericBounds.lean` | 7875 -> 7731, $`\tfrac{25}{1152} \to \tfrac{859}{40320}`$, $`\tfrac{1771}{3456} \to \tfrac{61937}{120960}`$ |
| `Main13.lean`, `Main.lean`, `Corollaries.lean` | the statements with the new constants and values |
| `Certificate/Checks.lean` | `GroupOK` has no cycle pointers; new `smallPortsB` and `smallPortsB_sound` |
| `Certificate/` (generated) | `Circles` (155 cycles), `GCircles13` (288), `Small00` to `Small07` (1,440 pointers), `Groups00` to `Groups07` without cycle pointers, the others as in `../constant/` |

`Repeat.lean`, `Levels.lean` and `WordOfLevel.lean` are the files of `../constant/` with the namespace renamed. Next
to the directory: `gen_cert.py` writes the generated files and `build.sh` builds everything. The patched file of
Pantone's library and the list of hashes of his sources are those of `../constant/` (`patches/` and
`pantone-sources.sha256` there).

## Inputs

`gen_cert.py` reads the two files that `../constant/gen_cert.py` reads and nothing else:

* `arrange/data/n12t-selection.txt.xz` of the repository, SHA-256
  `44f6c51e66b20ce625dc3cfc8d53abce6b2c23984a57608a915ff5209b3c44be`
* `selection/data/zcycles_n12.txt`, SHA-256 `a38ed3727c69273843f892e6bd72b17fe9117f1d3e8d8fed09e6a745c0501957`

It needs Python 3 with numpy and scipy (`scipy.optimize.milp`) for the minimum cover of the short walks.

## Building

```sh
./build.sh
```

`build.sh` follows `../constant/build.sh`. It checks Pantone's sources against `../constant/pantone-sources.sha256`,
runs `gen_cert.py` (25 s, 1.9 GB) and requires its output to be identical to
`SuperpermutationUpperBound61937/Certificate/`, compiles his library with the patched file of
`../constant/patches/` and then the modules of this development, and prints the `#print axioms` lines. The settings
(`LEAN`, `PYTHON`, `PANTONE_DIR`, `JOBS`, `MINFREE_GB`, ...) are those of `../tools/common.sh`. There is no Lake
project.

I ran the generator in this layout and compared its output with the files here: all 48 files are identical. I
built the 58 modules of the development with one Lean process on one thread, in my working directory and with the
compiled library of `../constant/` on the module path: 37.5 minutes, and the largest process
(`Certificate/WalkB`) at 3.9 GB of working set. On 2026-10-24 I ran `build.sh` from an empty build directory, on the files
of this repository as `git archive` writes them, with five Lean processes: 153 modules (Pantone's library and
this development), 13 minutes, exit 0.

## Axiom audit

The `#print axioms` lines of the final statements, from my build log:

    'SuperpermutationUpperBound61937.word_thirteen' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.finite_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.eventual_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.finite_61937' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.finiteInteger_61937' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.hasWord_fourteen' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.hasWord_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound]
    'SuperpermutationUpperBound61937.hasWord_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound]

All 99 `#print axioms` lines of that build: 63 with `[propext, Classical.choice, Quot.sound]`, 32 with
`[propext, Quot.sound]`, 2 with `[propext]` and 2 without axioms. `build.sh` prints these counts at the end.
