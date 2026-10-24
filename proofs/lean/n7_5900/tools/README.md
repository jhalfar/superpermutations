# The generators of n7_5900

The generated Lean files of `../LowerBounds/` were written by these scripts (Python 3, no packages). They are not
trusted and `../build.sh` does not run them: the kernel checks what they write, except the equations that level 2
evaluates by `native_decide`.

| script | writes |
|---|---|
| `k/gen_tables.py` | `KTables.lean`, from `../../n7/LowerBounds/PTables.lean` (set B) and `tables/capD15.txt` (table D) |
| `k/gen_testtables.py` | `KTestTables.lean`, from `tables/capD15u_*.txt` |
| `k/gen_native.py` | the 36 files `K*Native.lean` and `KFinalNative.lean` |
| `j15/gen_native.py` | the 36 files `J15*Native.lean` and `J15FinalNative.lean` (with the gates of `j15/gates.py`) |
| `j15/mkorder.py` | the order of the evaluations, `../evaluations.txt` (it read the two `native_order.txt` files that the two `gen_native.py` write) |

They write into `../LowerBounds/`, or into the directory `$OUT` if that is set (with the side files
`native_order.txt`, `KFinalCheck.lean`, `J15FinalCheck.lean`, `capT.txt` there too):

```sh
OUT=/tmp/gen python3 tools/k/gen_tables.py      # from proofs/lean/n7_5900
```

On 2026-10-24 I ran the first four with `OUT` set and compared: all 76 files they write are identical to the files
of `../LowerBounds/`. `tables/` holds the table files that the written proof calls `capD15.txt` and
`capD15u_0.txt` to `capD15u_8.txt`.
