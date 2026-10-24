# The catalogue of results

`catalogue.jsonl` lists the results of this repository, one JSON object per line and one claim per object, each
with its status, its evidence and the command that reruns it. `CATALOGUE.md` is the same list to read; it is
written by `make_catalogue_md.py` (`python3 catalogue/make_catalogue_md.py`). `check_catalogue.py` checks the
file against this schema, that every cited file exists, that the hashes of the evidence files match and that
every quoted line is still in its file (`python3 catalogue/check_catalogue.py`; part 7 of `test.sh`). All paths
are relative to the top of the repository, with forward slashes.

The entries here are those whose evidence is in this repository. I keep a longer catalogue in my working
directory, with results whose evidence is not public yet; they come here when their files do.

## Entry schema

### Fields

| field | type | required | meaning |
|---|---|---|---|
| `id` | string | yes | unique, stable, `n<N>-<slug>` (for example `n7-lb-5901`, `n8-klein-no-46172-g1`); `all-` for results about every n, `meth-` for methods that gave nothing |
| `n` | integer, list of integers, or `"all"` | yes | the number of symbols the claim is about |
| `kind` | enum | yes | `lower-bound` (about every word), `class-negative` (no word of a stated class reaches a length), `class-optimum` (the best word of a class has exactly this length), `structural` (a law or a count about objects, not a length), `upper-construction` (a construction or constant proved in Lean), `method-negative` (a method that gave nothing, with the reason) |
| `claim` | string | yes | the exact statement, one sentence; for anything that is not a Lean theorem or a published proof it names its model and class ("no Pantone completion of the Klein selection with ... has length 46,172"), never "no shorter word exists" |
| `family` | string | yes | the exact definition of the class or model the claim is about; `"all words"` only for lower bounds on L(n) |
| `status` | enum | yes | see below |
| `method` | string | yes | how it was obtained (program, model, search, LP, Lean tactic) |
| `reproduce` | object | yes | `{"command": "...", "path": "..."}`: the command that reruns it and the directory it runs in; `command` may be `""` with a note in `notes` when nothing reruns it in one step |
| `evidence` | list of objects | yes | `{"file": "...", "sha256": "..."}`: logs or outputs that record the result; `sha256` is the hash of the file as it was when the entry was written, or `""` when the file is gone or too large to hash in the check. A changed hash is an error for logs and outputs and a warning for `.md` reports, which are rewritten as work goes on; `"growing"` marks the log of a job that is still running (not hashed; replace by the hash when the job has ended) |
| `date` | string | yes | `YYYY-MM-DD` of the result (not of the entry) |
| `credit` | string | yes | whose the result is; results of Theo H., William Echols, Jay Pantone and others carry their name |
| `published` | object | yes | `{"yes": true/false, "where": "..."}`; for unpublished results `where` is `"local, unpublished"` |
| `supersedes` | list of ids | yes | entries this one replaces (may be empty) |
| `superseded_by` | list of ids | yes | entries that replace this one (may be empty) |
| `source` | list of strings | yes | `"path:line"` of the text the entry was checked against; at least one |
| `source_quote` | list of strings | yes | for each `source`, a short exact substring of that line (checked by the validator) |
| `needs_owner` | string | yes | `""`, or the question that has to be settled before the entry can be trusted (contradiction between sources, unclear class) |
| `notes` | string | no | anything else |

### Status values

* `lean`: a Lean theorem. Say in `method` whether `native_decide` is used and where the module lies (public
  `proofs/lean`).
* `certificate`: a finite certificate checked by an independent checker (LRAT proof checked by `cake_lpr` or
  `lrat-check`, an LP dual checked in exact arithmetic, a word checked by `verify_stream`).
* `computed-two-programs`: computed by two programs written independently (different authors or written from the
  text alone), with equal results.
* `computed-one-program`: computed by one program.
* `conjecture`: believed, with partial evidence only.

### Rules

* Words of unpublished results are never written into the catalogue, nor recipes (plans, selections) that produce
  them. An unpublished length is written as a length with `"published": {"yes": false, "where": "local, unpublished"}`.
* Words and texts of other people (Echols, Theo H., Pantone, Egan and others) are referred to by SHA-256 only.
* An entry whose sources disagree, or whose class is not clear from the source, gets a non-empty `needs_owner`
  instead of a guess; `CATALOGUE.md` lists these entries separately.
