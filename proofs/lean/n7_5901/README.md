# L(7) >= 5,901: the Lean reduction (level 1)

$`L(7) \ge 5{,}901`$ is a computer-assisted proof, not a Lean theorem. Its written proof, its programs, its tables and
the state of every search are in [`../../n7_5901/`](../../n7_5901/README.md). This directory holds the part of it
that Lean checks completely: the reduction of the bound to thirty search equations.

```lean
-- LowerBounds/F5901Search.lean                                     (namespace SuperpermLowerBounds)
theorem covers_5901_of_search ... :
    forall w : List (Fin 7), SuperpermutationBounds.Covers w -> 5901 <= w.length
```

The hypotheses are the search equations of 5,899 and 5,900 (all evaluated, see `../n7/` and `../n7_5900/`), the
eleven fields of `K16.Evals` (K0 to K10, engine `K16.seqSearch`) and the nineteen fields of `J16.Evals` (the
eighteen joint runs and the ring search RX, engine `J16.jSearch`). `#print axioms covers_5901_of_search` gives
`propext`, `Classical.choice` and `Quot.sound` only. Lean proves on the way the accounting at defect 16 (A16), the
kernel statements and their rules (K16: Lemma CUT16, Rule JS, the engine and its completeness) and the joint
statements (J16: PREV, ORD, VS, the ring classes, the engine and its completeness).

Six of the thirty equations are evaluated by `native_decide` so far (K10, K9, K8, K7, T9', T8), in files that
import this directory; they and their logs are in `../../n7_5901/lean/`. The README there has the trust level of
each of the thirty searches.

## Files

| file | what |
|---|---|
| `LowerBounds/A16*.lean` | the accounting at defect 16: cuts, items, pieces, the knapsack (`A16Tables` is generated) |
| `LowerBounds/K16*.lean` | the kernel statements: table D16, the potential, Rule JS, the engine, its soundness, `K16.Evals` |
| `LowerBounds/J16*.lean` | the joint statements: the rules, the ring row RX, the engine, its soundness, `J16.Evals` (`J16Final` and `J16Tables` are generated) |
| `LowerBounds/F5901.lean`, `F5901Search.lean`, `F5901Audit.lean` | the assembly and its audit |
| `LowerBounds/PCount.lean`, `K16Count.lean` | counting copies of the engines (they give the kept counts of Table C) |
| `LowerBounds/A16Test.lean`, `J16Test.lean`, `K16SmallSearch.lean` | kernel tests on small cases |
| `build.sh`, `sources.sha256` | the build of level 1 and the hashes it checks |

The generated files were written by generators of mine that are not in this repository; the kernel checks them.

## Building

```sh
cd proofs/lean && ./n7/build.sh && ./n7_5900/build.sh && ./n7_5901/build.sh
```

`build.sh` here works in the build directory of the other two and compiles only what is missing.
