# Referee notes on PROOF_5901.md

2026-10-24. Before publishing the written proof I compared its counts and statement parameters with the files
behind them. Section A says what I compared and found equal, section B lists every discrepancy or open point I
found, and section C keeps the points of my earlier list of disagreements between the sources (2026-10-15 and
2026-10-16), with the reading the text takes. None of the points changes the mathematics of the proof.

## A. What I compared

- Table C (`PROOF_5901.md` 0.3 and `table/TABLE_C16.md`) against `audit/partaudit.txt`, the sums over the part
  files: all 32 tags (11 kernel tags, the 18 counted joint tags, the two `gj2` repeats and the three ORDS runs),
  kept and tried, every digit equal. The tried column of the counted joint runs adds up to 4.99e15, as the text
  says ("about 5.0e15").
- The second counts against their outputs: `audit/second/k2_K10.txt`, `k2_K9.txt`, `k2_K8.txt` (172,577,
  384,081,983, 22,732,567,392, no violation), `j2_T9r.txt` and `j2_T8.txt` (found 0, kept and tried equal),
  `audit/k7second/summary.txt` (320,243,136,927, 64 of 64 parts), and the eight parts of
  `audit/t7second/parts/` (above the gate once plus the parts: 1,432,335,917,907 kept, 7,283,065,963,552 tried,
  found 0 in every part).
- The statement parameters of 3.4 (S, LO, G, potential, table, Rule JS) against the parameter lines printed in
  `audit/partaudit.txt` and against the fields of `K16.Evals` (`LowerBounds/K16Final.lean`: lo = LO + 1,
  hi = G = 96 - 6 s, the potentials, `Utab s` for K5 to K10 and `D16tab` for K0 to K4, the JS flag for K0 to
  K2). All equal.
- The runs of 4.7 and the commands of 6.2 against the command lines and statement lines of every joint tag in
  `audit/partaudit.txt` (kinds and their order, V, W, B, RLO, RHI, RVMIN, the PREV piece RP, the potential, ORD,
  ORDS, the table, the numbers of parts and the gate depth) and against `J16.Evals` (`LowerBounds/J16Bridge.lean`:
  the specs of each field and the rules `rT1` to `rT9`, `rT2up a`, `rT2lo a`). All equal. The clip flag of the
  Lean rules is off exactly in T1, T2 and T4' (and T5, which has no ring), and the ring class "value >= 0" is on
  exactly in T3', T6', T7, T8 and T9', as 0.4 says.
- The tables (1.2 to 1.5, 2.7) against the files of `table/`, with a script of mine: RX is lower than the ring row
  of D at exactly 23 levels (x = 1 to 5, 7, 9 to 12, 17, 19, 21, 23, 25, 29, 35, 41, 53 to 55, 61, 63), never
  higher, and 84 84 84 against 81 82 83 at 53 to 55; `capD_r.txt` is D with RX on 0 to 63; the three lowered
  files are D in the rows 0 to 11, min(row, H + a - 1) on their window whether the row is taken from D or from RX,
  and RX outside it (1 at 1 hole, 6 at 7 holes); D16 lies below D at the levels of 1.4, 248 entries, with the gaps
  53, 54 (s = 2), 39 (s = 5) and 37 (s = 7); `capD16_k.txt` is D16 and each `capD16u_s_k.txt` has the rows below
  s from D and the row s from D16, with no ring line; the ring row of D on 0 to 7 holes is 5 5 5 5 5 5 10 10.
- The knapsack (1.2, 1.4, 2.8) against `programs/knapsack/knap16_map.log` and `knap16_map.shapes.txt`: 603
  entries equal to the Lean `Dtab`, the ring row equal to `TRtab` on 0 to 76 holes, the largest values 35, 29, 23,
  17, 11, 5 of the rows 11 to 16, 131,436 profiles, the 20 shapes with their counts and statements, the largest
  numbers of links, slack 0 everywhere. 114,745 profiles on `capD_r.txt` in `knap16_rx.log` and `knap_rx.log`;
  299,595 item profiles in 361 shapes and the 5,039 profiles removed by S1 to S5 in `acc16_D.log`.
- The Lean evaluations (0.4) against `lean/logs/`: `NK.log` 6,324 s on 1 thread (105 min), `NJ.log` 6,993 s on 2
  threads (117 min), `NEv.log` 58 s; the `#print axioms` lines (propext, Quot.sound for `t9_ev` only, one
  `native_decide` axiom each); `K10K9.log` 963 ms and 83,936 ms; `K8.log` 3,411,677 ms on 2 threads (57 min);
  `T8eq.log` 6,460,082 ms (108 min); `T8cnt.log` 6,925,342 ms (115 min) and the counts of T8; `T9.log` the counts
  of T9'. `NK7_0.log` to `NK7_3.log` and `nk_queue.log` for K7 (9,377 + 13,371 + 43,978 + 10,707 s), and
  `NK6_00.log` for the first file of K6 (13,552 s).
- Small arithmetic: (L1) 5,884 + 17 = 5,901; ACC16 (720 - 680, 816 - 720); V, W and B of the 20 shapes; the sums
  by statement in 2.8; XL = 0 for 10,15,40 and 10,16,43; Lemma L2 (46 - 37, 46 - 36, 46 - 31 = 9, 10, 15).
- The line numbers of 4.6 in `programs/gj2/jr_core.h` (92, 102, 158, 206) and `programs/gj2/gj2.c` (222): they
  are the places where the ring row is read. In `programs/gj3/jr_core.h` the same places are the lines 93, 103,
  159, 208; I added that to the text.

## B. Discrepancies and open points

1. The second count of T7 had ended and was not recorded. The working text said that `j2_np5` was still running
   on T7. Its eight part files (`audit/t7second/parts/`, last one written 2026-10-21 20:04) add up to the counts of
   Table C with found 0 in every part; `audit/t7second/run.log` records that two workers stopped once without a
   result and were run again. I wrote this into 0.3, 0.4 and 7.2, and T7 moved from "one program" to "two
   independent programs". A summary script for these parts, like `summ_k7.py` for K7, does not exist; I added
   the parts by hand (above the gate once, plus the eight parts).
2. K7 in Lean was four theorems, not yet the field. `NK7_0.lean` to `NK7_3.lean` prove
   `seqSearch 7 Utab7 7 36 54 10 16 25 false 400 8 64 pa pb = false` for the ranges 0..16, 16..32, 32..48 and
   48..64, which cover all 64 parts. No compiled file states the field `k7 : K16.Ev Utab7 7 36 54 10 16 25 false`
   (`NEv.lean` has only k10, k9, k8, t9 and t8). The missing step is a `PS.Covered` case split like
   `f1_covered_native` of the proof of 5,899. Closed on 2026-10-24: `lean/Audit5901/NEv7.lean` states the field
   as `k7_ev` and compiles in 16 s (`lean/logs/NEv7.log`). The same step will be needed for K6 (16 ranges).
3. "T9' in 16 s" (0.4, the `#eval` runs). No log shows 16 s: `lean/logs/T9.log` prints "(0 ms)" for the equation
   and a wall time of 65 s for the whole script, which also ran three counts; `T9g.log` ran 47 s on 2 threads. I
   left the number as written.
4. The count of K9 by the Lean counting copy (384,081,983, and 359,998,813 with Rule JS) is not in `lean/logs/`.
   `K10K9.log` has the count of K10 and the equation of K9 only. The K9 counts come from a bench run recorded in
   STATE_5901B 4 (its log is a scratch file of the Lean work, not in this repository).
5. The date of Table C. The text said "`TABLE_C16.md` of 2026-10-16"; the file says "State of 2026-10-18" and has
   K1, which ended on 2026-10-18. I changed the date to 2026-10-18.
6. The table files named in parameter files (3.4). The text said that K3 to K7, K10 and K2 print their table file;
   `audit/partaudit.txt` shows that the parameter files of K1 and K0 name `caps/capD16_k.txt` too. I extended the
   sentence to K2, K1 and K0.
7. The size of the Lean evaluations still to do (7.3: "about 2.4e15 kept prefixes (kernel)", "about 420 days").
   This is the estimate of PLAN_5901 4 for all of K0 to K10, made before K1 ended (K1 estimated at 7.6e14). With
   the final counts K0 to K10 have 2.342e15 kept prefixes and K0 to K5, which are not evaluated, 2.339e15; at
   0.42 us per kept prefix on 28 threads that is about 406 days. I left the text as written. The joint figure,
   9.2e14, matches the runs not yet evaluated.
8. 6.2 said that `knap16.py` has absolute paths in its first lines. It now finds the root of my tree through a
   marker file and reads `capD.txt` and `KTables.lean` from there. I changed the sentence.
9. Lean and the text differ in one dependency (known, STATE_5901B 5 item 2). The text (3.4) says that K5 to K10 do
   not depend on each other: K10 reads the row 9 of D at 36 holes, 122, which rests on Lemma CL. Lean takes that
   entry from K9 instead (D16_9(36) = 120 <= 122). Both are valid; no statement changes.
10. Names of one program. 0.4 calls the program that counted K9 with Rule JS `kjs` (359,998,813, as in
    STATE_5901B 4, which cites the log of `kjs.exe`); 6.1 and 6.4 name `kfast_js` as the CPU reference of Rule JS.
    My notes do not say whether these are two builds of one source or two programs (both `kjs.c` and
    `kfast_js.c` exist in my tree). It does not affect any count of Table C.
11. The table bounds in the T2 window programs. The text (4.6) says that the lower halves read the lowered ring
    row only as a bound on a whole ring piece. I did not re-read the code for this; the references are note tune
    4 and ref16b 1, and the line numbers above are where `PRt` is read.
12. Records. `audit/partaudit.txt` and the logs of `lean/logs/` record paths of my working tree. I changed only
    the absolute root (`<research tree>`), not the records themselves.

## C. The points of my list of disagreements between the sources

The list was written on 2026-10-15 and updated on 2026-10-16; the fourth referee check, ref5901, read it with the
proof and agreed with the readings taken. In short:

1. A (cyc) component with two dear places: every part is its own item, the -6 and +7 of (cyc) go to the borrowing
   part, positivity per item (2.4, 2.5). The map took the positive parts together as one item; the knapsack
   enumerates the parts separately, and that is the accounting used.
2. T2 48..55 on the CPU (`jr6`) shares `jr_core.h` with the card host: one program twice, not an independent
   second count (0.4, 7.2). The independent `j2r` ran the upper half only at a = 25, which is not the split used.
3. K8 by `gk4` and `kfast2`: one lineage (the card host takes its table code from kfast.c).
4. The count of K9 in the map (384,081,919) was made with a table file whose ring line the kernel programs read as
   row 0; 384,081,983 is the count on the corrected file.
5. The commands of K2, K1, K0 are those of `gkjs` with Rule JS and the potentials 20,29,60, 20,29,60 and 17,24,5;
   an older run book had other lines.
6. The double places and the joint statements S1 to S5 of defect 15 are not used; every profile is removed whole
   by K or one of T1 to T9.
7. T3, T4 and T6 about all pieces are not proved; the accounting needs only the restricted forms (2.9, 4.8).
8. The places where the lowered ring row is read were checked in both copies of `jr_core.h`, whose line numbers
   differ by one (4.6).
9. The sentence that a ring's own cycle-lemma rotation passes the ring rule in every position is in 4.2 and used
   by ORD and ORDS.
10. The kernel rows of defect 15 have two programs ([W] 0.3), so every statement of defect 16 rests on a Theorem K
    with two programs.
11. and 12. K10 and K7 were run again on 2026-10-16 with stored part files that name their tables
    (`audit/records/`). The headers of K8 and K9 still do not name the table; the scripts name the `u` files.
13. T7 and T8 by `gj` have no stored statement line; their repeats by `gj2` do.
14. ORDS on 7 symbols with a positive case: not done, and not needed, because no counted statement uses ORDS.
15. T9 by the plain rule: done (T9r, counted as T9').
16. Best >= 0 under the cut at a ring with negative need (4.2): the argument is mine; ref5901 checked it and asked
    for the two sentences now in 4.2.
17. Lemma CL for s = 16: its proof does not use s <= 15 (1.2); ref5901 agreed. Only the knapsack reads row 16.
18. The kernel item is taken even when its value is not positive; consistent with PROF16.
19. The potential guard of the programs (b >= a, XL >= 0) is stronger than Lemma REV needs; every potential used
    satisfies it.
20. T2 8..15 and 16..23 are split into 64 parts by the start vertex of piece 2, not by a gate.
