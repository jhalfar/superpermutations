# Defect 16 (L(7) >= 5,901): the computed statements

State of 2026-10-18 (the table of the card runs; the second counts made on 2026-10-20 and 2026-10-21 are in
`../PROOF_5901.md`, sections 0.3, 0.4 and 7.2). One line per statement that the accounting of defect 16 needs.
"kept" is the number of kept prefixes, "tried" the number of start vertices tried (joint statements). All runs
are on one CUDA card with 32 GB unless the program column says otherwise. The runs of 2026-10-16 (T6rp, T9r,
T9rs, K7, K10 and the `gj2` repeats of T7 and T8) were made after the host machine was changed, with the same
card. No counted line rests on the rule ORDS. The rules are proved in `../PROOF_5901.md` (sections 3 and 4);
each rule has had a referee (ref16, ref16b, refjs).

## Joint statements (all found 0)

| | statement | rule | kept | tried | program, parts |
|---|---|---|---|---|---|
| T1 | J(S7 S7; 50, 84; 1) | ORD + PREV 10,15,25 | 432,156,242,209,710 | 2,386,049,711,507,025 | `gj2`, 1,024 parts |
| T2 | J(R S7; 46, 89; 1), rings 8..15 | PREV 10,15,40 | 101,123,384,635,543 | 591,203,509,244,515 | `gj2`, 64 |
| T2 | rings 16..23 | PREV 10,15,40 | 129,493,336,379,997 | 664,376,894,711,771 | `gj2`, 64 |
| T2 | rings 24..31 | PREV 10,15,40 | 135,483,427,600,468 | 687,655,387,002,664 | `gj2`, 64 |
| T2 | rings 32..39, value >= 17 | VS, ring first | 151,457,803,584 | 795,609,616,646 | `gj3`, 16 |
| T2 | rings 32..39, value <= 16 | VS, kernel first | 817,008,248,719 | 4,282,237,016,933 | `gj2`, 16 |
| T2 | rings 40..47, value >= 20 | VS | 91,979,996,005 | 476,425,689,572 | `gj3`, 16 |
| T2 | rings 40..47, value <= 19 | VS | 284,267,038,527 | 1,671,708,523,584 | `gj2`, 16 |
| T2 | rings 48..55, value >= 23 | VS | 71,260,814,984 | 365,649,914,334 | `gj3`, 64; equal to `jr6` on the CPU |
| T2 | rings 48..55, value <= 22 | VS | 174,112,070,351 | 957,110,796,225 | `gj2`, 64; equal to `jr6` on the CPU |
| T2 | rings 56..89 | PREV 10,15,40 | 28,953,480,015,964 | 152,453,459,284,641 | `gj2`, 64 |
| T3' | J(R S5 R; 52, 82; 2), rings >= 8 holes | PREV 10,16,43 | 40,196,474,735,125 | 213,550,167,376,609 | `gj2`, 64 |
| T4' | J(R S4 S4; 56, 77; 2), rings >= 8 holes | ORD + PREV 10,16,43 | 1,479,145,818,172 | 7,891,206,447,132 | `gj2`, 64 |
| T5 | J(S3 S3 S3; 60, 72; 2) | plain | 52,379,362,069,149 | 268,009,289,170,899 | `gj`, 16 |
| T6' | J(S2 R R R; 58, 75; 3), rings >= 8 holes | PREV 10,16,25 (tag T6rp) | 112,728,682,360 | 592,623,181,185 | `gj2`, 16 |
| T7 | J(S1 S1 R R; 62, 70; 3) | plain | 1,432,335,917,907 | 7,283,065,963,552 | `gj`; repeated by `gj2`, 1 part (same counts) |
| T8 | J(S0 S0 S0 R; 66, 65; 2) | plain | 7,126,584,865 | 36,384,111,126 | `gj`; repeated by `gj2`, 1 part (same counts) |
| T9' | J(S0 R R R R; 64, 68; 4), rings >= 8 holes | plain (tag T9r) | 11,105,597 | 59,706,146 | `gj2`, 8 |

The statement line of T6rp: `gj K=7 caps=../jrev/capD.txt V=58 W=75 B=3 pieces S2 R R R NOCUT=0 PART=*/16
DEPTH=10 PART2=*/1 RLO=8 RHI=128 REV=1 RP=0 potential 10,16,25 ORD=0 ORDS=0`. The T6rp run took 77 card seconds.
`gj` and `gj2` share `jr_core.h`, so the `gj2` runs of T7 and T8 are repeats, not independent checks.

Extra runs with the rule ORDS (all found 0), not counted; no statement rests on them:

| | statement | rule | kept | tried | program, parts |
|---|---|---|---|---|---|
| T6' | J(S2 R R R; 58, 75; 3), rings >= 8 holes | ORDS + PREV 10,16,25 (tag T6r) | 98,752,840,534 | 515,328,744,583 | `gj2`, 16 |
| T9' | J(S0 R R R R; 64, 68; 4), rings >= 8 holes | ORDS (tag T9rs) | 4,287,144 | 22,804,444 | `gj2`, 8 |
| T9 | J(S0 R R R R; 64, 68; 4), all rings | ORDS (tag T9s) | 9,560,336,846,694 | 50,933,661,579,615 | `gj2`, 8 |

Rules: PREV, ORD (sections 4.3, 4.4 of the proof), ORDS (section 4.5; used only in the extra runs), VS = split by
the value of the ring (section 4.6, exact ring row `capD_r.txt` of this folder). T3', T4', T6', T9' are the statements
restricted to rings of value >= 7 (at least 8 holes); ref16b showed that these are the statements the
accounting needs and that the unrestricted T3, T4, T6 are not proved.

## Kernel alone (no violation)

| | links, levels | potential, rule | kept | program, parts |
|---|---|---|---|---|
| K10 | 10, level 36 | 10,16,25; table `capD16u_10_k.txt` | 172,577 | `gk4`, 1 part file (`../audit/records/K10_p0.txt`, LO 35) |
| K9 | 9, levels 36 to 42 | 10,16,25 | 384,081,983 | `gk4` and `kfast2` (with Rule JS: 359,998,813, three programs) |
| K8 | 8, levels 36 to 48 | 10,16,25 | 22,732,567,392 | `gk4` and `kfast2` (with Rule JS: 19,526,754,031) |
| K7 | 7, levels 36 to 54 | 10,16,25; table `capD16u_7_k.txt` | 320,243,136,927 | `gk4`, 1 part file (`../audit/records/K7_p0.txt`, LO 35, 32 card seconds) |
| K6 | 6, levels 38 to 60 | 10,16,25 | 2,569,985,903,558 | `gk4`, 16 |
| K5 | 5, levels 38 to 66 | 10,16,25 | 23,993,915,746,406 | `gk4`, 64 |
| K4 | 4, levels 42 to 72 | 10,15,25 | 160,141,566,085,840 | `gk4`, 64 |
| K3 | 3, levels 49 to 78 | 10,15,30 | 527,651,578,348,368 | `gk4`, 256 |
| K2 | 2, levels 52 to 84 | 20,29,60, Rule JS | 375,408,252,302,475 (512 of 512 parts, no violation) | `gkjs`, 512 |
| K1 | 1, levels 56 to 90 | 20,29,60, Rule JS | 755,070,879,353,479 (2,048 of 2,048 parts, no violation) | `gkjs`, 2,048 (89,682 card seconds) |
| K0 | chains, levels 66 to 96 | 17,24,5, Rule JS | 497,079,750,869,693 (4,096 of 4,096 parts, no violation) | `gkjs`, 4,096 |

Rule JS: section 3.3 of the proof, referee refjs (sound for b >= 0). The kernel-alone runs use the tables
`*_k.txt` of this folder (the map's files carry a ring row that the kernel programs would misread).

## Later

The second counts, the Lean evaluations and what is still missing are in `../PROOF_5901.md` (sections 0.3,
0.4 and 7). The part-file audit of every line is `../audit/partaudit.txt`.
