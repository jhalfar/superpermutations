# Attempts: what was tried and did not work

This is a log of attempts on superpermutations, including the ones that gave nothing. It started after Stefan Djokovic
suggested a public "tried X, didn't work" list. The first page is [`n7.md`](n7.md), everything I tried for n = 7. The
same rows are in [`attempts.tsv`](attempts.tsv), one row per attempt, which is the file to edit.

## How to read an outcome

Every row ends in one of six words.

- `proved`: a written argument or a Lean proof. The result column says which.
- `computed`: a program gave the number. The result says how many independent programs.
- `negative`: a finished run or a measurement that gave no gain inside the stated caps. It does not mean the idea is
  dead, and it does not mean a bound is false. It is also the word for "too slow for the budget", and the result says
  so.
- `inconclusive`: stopped, hit a limit, or undecided either way.
- `false`: a counterexample exists, and the result gives it.
- `idea`: not run.

I did not rerun the n = 7 negatives with 4x larger settings. Where a row has a qualifier (for example "partial" or "to
64 rows"), the result column keeps it.

## The columns of `attempts.tsv`

Tab-separated, with the header in the first line.

| column | meaning |
|---|---|
| id | short stable id, such as `n7-up-04` |
| n | the n of the problem |
| group | `lower` (lower bound), `upper` (words), `structure`, or `tool` |
| target | what it was for: a length or a claim |
| method | one sentence on the approach |
| scale | what was run: nodes, CPU or GPU hours, threads. "not run" for an idea |
| caps | the family and limits a negative or inconclusive result holds under |
| outcome | one of the six words above |
| result | the key number, or why it failed |
| date | the day the row was written |
| who | who ran it |
| link | a note, code, log or message, if there is one |
| retest | what would change the verdict (more time, a bigger neighbourhood, a better bound) |

One example row:

```
n7-up-03	7	upper	5,904	Kernels up to 64 rows, every seam type but one, links of weight 4, loops only	62 rows: 2.76e12 nodes, 21,085,426 kernels, 2.7 GPU hours. 64 rows: 1.42e13 nodes, 37,425,892 kernels, 14.0 GPU hours	family: Kernels up to 64 rows, every seam type but one, links of weight 4, loops only	negative	no forest. Growth is 2.3 to 2.9x per row; 66 rows about 3 days, 70 rows about 2.5 months (estimate). Cross-checked independently at 56 rows only [computed negative (to 64 rows)]	2026-11-27	Jakub		
```

## Adding rows

Open a pull request that adds rows to `attempts.tsv`. One row per attempt; split a long project into its approaches.
Your own dead ends for any n are welcome, and so are published ones if the link points to the source. A row you own
can be changed later by another pull request, for example from `negative` to `inconclusive` after a longer rerun.
The old value stays in the history. The n pages are written by hand for now, and I will add a small script that builds
them from the TSV once there are rows for more than one n.
