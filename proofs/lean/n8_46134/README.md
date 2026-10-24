# L(8) >= 46,134, with three evaluations by `native_decide`

A superpermutation on 8 symbols has at least 46,134 letters. This directory proves it in Lean 4 at two levels
of trust, kept apart as in [`../n7/`](../n7/README.md):

* Level 1 is checked by the kernel to the end, with no `native_decide`. It proves the bound from three
  equations, each of which says that a finite search finds nothing.
* Level 2 evaluates those three equations by compiled code (`native_decide`). For them the Lean compiler, the
  C compiler of the Lean toolchain and the Lean runtime are trusted, as in `../n7/` and in Lebar's proof for
  n = 7.

The bound without `native_decide` stays 46,133 (Theorem C of [`../lower/`](../lower/README.md)). William
Echols's framework, taken further in [`../n8/`](../n8/README.md), gives 46,132.

## The statements

```lean
-- AuditD.lean: the statement written with the definitions of Challenge.lean only, and Lean accepts
-- covers_lower_bound_8_native as its proof
example : forall w : List (Fin 8), (forall p : List (Fin 8), p.length = 8 -> p.Nodup ->
    exists u v : List (Fin 8), w = u ++ p ++ v) -> 46134 <= w.length

-- LowerBounds/DFinal.lean, level 1
theorem covers_boundD_8_of_search {sz1 f1 d1 n1 sz2 f2 d2 n2 sz3 f3 d3 n3 : Nat}
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h1 : S.lineSearch 8 sz1 4 9 56 f1 d1 n1 = false)
    (h2 : S.lineSearch 8 sz2 17 38 264 f2 d2 n2 = false)
    (h3 : S.zoneSearch 8 sz3 4 9 56 2 17 38 264 6 f3 d3 n3 = false) :
    forall w : List (Fin 8), SuperpermutationBounds.Covers w -> 46134 <= w.length

-- LowerBounds/DLine1Native.lean, DLine2Native.lean, DZoneNative.lean, level 2
theorem S.lineSearch_8_4_9_56    : S.lineSearch 8 2097152 4 9 56 400 40 251 = false := by native_decide
theorem S.lineSearch_8_17_38_264 : S.lineSearch 8 2097152 17 38 264 400 40 251 = false := by native_decide
theorem S.zoneSearch_8 : S.zoneSearch 8 2097152 4 9 56 2 17 38 264 6 400 40 251 = false := by native_decide

-- LowerBounds/DFinalNative.lean
theorem covers_lower_bound_8_native :
    forall w : List (Fin 8), SuperpermutationBounds.Covers w -> 46134 <= w.length
theorem ssuper_lower_bound_8_native : 46134 <= Hunter.Ssuper 8
```

(namespace `SuperpermLowerBounds`, symbols in ASCII). `#print axioms`:

```
'SuperpermLowerBounds.covers_boundD_8_of_search' depends on axioms: [propext, Classical.choice, Quot.sound]
'SuperpermLowerBounds.covers_lower_bound_8_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SuperpermLowerBounds.S.lineSearch_8_17_38_264._native.native_decide.ax_1_1,
 SuperpermLowerBounds.S.lineSearch_8_4_9_56._native.native_decide.ax_1_1,
 SuperpermLowerBounds.S.zoneSearch_8._native.native_decide.ax_1_1]
```

## The argument

Theorem D (`LowerBounds/DTheorem.lean`, for every k >= 5) bounds a Hamiltonian path in the overlap graph by
lines that the exact weight-three chains of a strongly exitless path must satisfy: if every such chain with r
pieces and total deficit δ has a r <= b δ + c for each line (a, b, c) of a list, and the lines exclude every
excess below m, then the shortest superpermutation has at least hpv(k) + m letters. For k = 8, `D8.lean` uses
the two lines 4 r <= 9 δ + 56 and 17 r <= 38 δ + 264 and one statement about the zone where both are tight,
and gets 46,134.

The three hypotheses are statements about all chains. `DModel.lean` reduces them to chains of a finite model,
and `DSound.lean` proves that a depth-first search over the model chains (`DSearch.lean`) is complete: if it
answers `false`, no chain breaks the line. Those two files and the search are checked by the kernel. Only the
three runs of the search are evaluated by compiled code.

`DSmall.lean` runs the whole chain on 5 symbols with the search evaluated by the kernel (`decide +kernel`) and
gets `ssuper_ge_153_D : 153 <= Ssuper 5`, the true value, with the three standard axioms. `DTestNative.lean`
proves small searches both by the kernel and by `native_decide`, and larger ones whose answers are known from a
C program of mine that shares no code with `DSearch.lean`. That program and a standalone build of the same
search count 776,981,464 chains for the first line and 3,597,654,861 for the zone, with no chain that breaks
them. The second line (5,807,830,513 chains by the C program) was not counted a second time.

## Files

| file | what |
|---|---|
| `LowerBounds/DTheorem.lean` | Theorem D for every k >= 5 (`theoremD_pathwise`, `superperm_boundD`, `covers_length_ge_boundD`) |
| `LowerBounds/D8.lean` | k = 8: `covers_boundD_8` from the three hypotheses about chains |
| `LowerBounds/DModel.lean` | the hypotheses for model chains, and from them for the chains of the preimage-chain library |
| `LowerBounds/DFinal.lean` | `covers_boundD_8_of_search`: the bound from the three equations |
| `LowerBounds/DSmallSearch.lean`, `DSmall.lean` | the kernel test on 5 symbols |
| `LowerBounds/DTestNative.lean` | small searches by the kernel and by `native_decide`, and searches with known answers |
| `LowerBounds/DLine1Native.lean`, `DLine2Native.lean`, `DZoneNative.lean` | the three evaluations |
| `LowerBounds/DFinalNative.lean` | the theorem |
| `AuditD.lean` | both levels stated with the definitions of `Challenge.lean` and of the preimage-chain library only |
| `build.sh` | builds everything from sources |

`DSearch.lean`, `DSound.lean`, `DCapacity.lean`, `DJunction.lean` and the files they import are shared with the
proof for n = 7 and are read from `../n7/LowerBounds/`.

## Building

```sh
JOBS=4 ./build.sh          # everything
./build.sh level1          # level 1 only, no native_decide
```

It needs what `../n7/build.sh` needs: Lean 4.31.0, Pantone's repository with Mathlib fetched (for
`Challenge.lean` and Mathlib), the Hunter-Raudvere and preimage-chain libraries at the commits of
`../words/README.md`, and `leanc`. The library engine is `DSearch.lean`, compiled to C and to a shared library
that the evaluations load with `--load-dynlib`, as `../n7/build.sh` does with `PSearch.lean`.

What it cost when I built it (2026-10-07, on a busy machine): the level-1 files of this directory 30 to 60 s each
with one thread and 3.2 to 3.5 GB of working set; the three evaluations 722 s with 2 threads, 3,431 s with 2
threads and 3,739 s with 3 threads, about 5.4 thread-hours in all, 0.3 GB each; `DTestNative` 52 s. A build from
an empty directory also compiles the two lower-bound libraries and the level-1 files of `../n7/` that are needed,
as `../n7/build.sh` does.
