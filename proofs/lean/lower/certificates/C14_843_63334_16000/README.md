# n = 14: 93,891,141,126 by Theorem C, as a recipe

A superpermutation on 14 symbols has at least 93,891,141,126 letters. This is Theorem C of
[`../../`](../../README.md) with the certificate c = 843/16000, b = 63334/16000, checked by the Lean kernel in the
same way as the certificates of `../../certificates-large.txt`: `decide +kernel`, no `native_decide`, axioms
`propext`, `Classical.choice` and `Quot.sound` only. It is 118 letters above 93,891,141,008, the value of the
largest certificate for k = 14 that `../../build.sh full` checks.

The generated Lean files take about 12 GB, so they are not stored. This directory holds what is needed to write
them again and to check that they are the files I compiled:

| file | what |
|---|---|
| `build.sh` | generate, compile, write and check the final statement |
| `fix_imports.py` | after generation: each part imports only the data files it uses, not the file `Defs` that imports all 4,479 (9.9 GB of compiled files at once) |
| `make_final.py` | writes the final statement from the head file of the generator |
| `Final_C14_843_63334_16000.lean` | the final statement as I compiled it; `build.sh` requires `make_final.py` to write the same file |
| `generated.sha256` | SHA-256 of the 5,347 generated files after `fix_imports.py` |

The generator is the public `../../tools/s_plan2.py`, unchanged:
`s_plan2.py 14 843 63334 16000 C14_843_63334_16000 --leaf 400 --band 250 --per-file 3000`.

## The statement

```lean
-- Final_C14_843_63334_16000.lean                                    (namespace SuperpermLowerBounds)
theorem covers_length_ge_93891141126 : forall w : List (Fin 14), Covers w -> 93891141126 <= w.length
theorem ssuper_ge_93891141126 : 93891141126 <= Ssuper 14
```

with the output of my build (2026-10-24):

```
'SuperpermLowerBounds.covers_length_ge_93891141126' depends on axioms: [propext, Classical.choice, Quot.sound]
'SuperpermLowerBounds.ssuper_ge_93891141126' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Running it

```sh
cd proofs/lean/lower && ./build.sh                       # once: the compiled LowerBounds modules
cd certificates/C14_843_63334_16000 && JOBS=4 ./build.sh
```

The phases `generate`, `build` and `final` can be run one at a time; `build` continues where it stopped (a
module counts as done when its stamp is written, as in the other build scripts). What my run cost:

* generation: 984 s on one thread, 25.1 GB of memory at the peak (the generator holds the whole plan of
  about 2.5 million states in memory);
* the data files and the 866 parts: 61.3 hours of Lean time in all, one thread per process, at most 6.8 GB of committed
  memory for one process (most below 2 GB), run with two processes over about 39 hours;
* the head file 11.4 GB and the final statement 17.9 GB of committed memory, each alone, a few minutes;
* disk: about 12 GB of generated source and 11 GB of compiled files.

I ran these steps with the same generator and the same two scripts in my working directory, not through this
`build.sh`; the file names, options and hashes are those of that run.
