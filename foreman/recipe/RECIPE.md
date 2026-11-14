# How foreman found the n = 12 word of 522,736,429 letters

Start: William Echols's word W-0091 (522,736,503 letters). Every step below works on plans over the base word
`base12_hybrid_e.txt` (n = 12; SHA-256 0d36cdd07fe7c90912fc0a295ca9b9895c9fba0ad0769196e2b37960b1657c68), in its letters.

## The start plan

`W-0091_on_base12_hybrid_e.plan` (SHA-256 4737a5c715a7d6e777e77bb4b25d3141d7c9ac7635eb157cef33f7c71e29c2cc) is
W-0091 written in the letters of the base and turned into a plan:

    tr -d '\r\n' < W-0091.txt | tr '71056389A4B2' '0123456789AB' > w503b.txt     # the letter map fits all trails
    tools/word2plan base12_hybrid_e.txt w503b.txt w503b.plan                     # "exact", safe to search from

W-0091 in the base's letters has SHA-256 7b4719c8ea20fa484b4efe15a4bce27f850e66be308518116ee13a17c5b1afda.

## The steps (foreman case bench12z, arm expert12 = `wrap/expert12.sh`; 13-14 Nov 2026)

Each step starts from the best plan so far. Times are wall clock from the start.

| # | step | settings | result | time |
|---|---|---|---|---|
| 1 | trailsearch | `--time 1200 --seed 11 --kmax 8 --T0 0.4 --threads 4 --sync 15` | 522,736,502 | 0:20 |
| 2 | segment insertion on the card | `--or3 3 --or3-slack 1 --or3-gpu --or3-maxcand 200000 --or3-sec 1800 --threads 6` | 522,736,500 | 0:21 |
| 3 | the same, 4 cuts | `--or3 4 ...` | 522,736,499 | 0:21 |
| 4 | the same, 5 cuts | `--or3 5 ...` | 522,736,497 | 0:22 |
| 5 | segins_ils | `--seed 7 --ils 3000 --ils-log 600 --ils-kmax 1 --ils-slack 2 --ils-near -1 --ils-cuts 3 --threads 2` | 522,736,486 | 1:12 |
| 6 | ils12.sh, 9 rounds (below) | | 522,736,445 | 9:37 |
| 7 | recut `--co-skip` | | no gain | |
| 8 | trailsearch | as step 1 with `--seed 22` | 522,736,444 | 9:59 |
| 9 | segment insertion 3 / 4 / 5 cuts on the card | as steps 2-4 | no gain | |
| 10 | ils12.sh round 1, kmax 3 lane | `--seed 121` | 522,736,433 | 10:55 |
| 11 | ils12.sh round 2, kmax 2 lane | `--seed 214` | **522,736,429** | 11:50 |

An ils12.sh round (`tools/pipeline/ils12.sh`): `tools/polish.sh DIR BASE PLAN 4 6 "--or3 5 --or3-slack 1"` (relocate --dpa,
segins, loopscan), then two segins_ils lanes side by side from the best plan, `--ils 3000 --ils-log 600 --ils-kmax K
--ils-slack 2 --ils-near -1 --ils-cuts 3 --threads 2` with K = 2 and 3 and seed ROUND * 100 + K * 7. The best word
that delcheck finds complete goes on. In step 6 the rounds gave: polish 485; kmax 2 480 and kmax 3 462 (round 1);
kmax 2 458 (round 2, seed 214); kmax 2 452 (round 3, seed 314); then kmax 3 451, 450, 448, 446, 445 (rounds 4 to 8,
seeds 421, 521, 621, 721, 821); round 9 gave nothing. In step 10 the kmax 2 lane gave 442 and the kmax 3 lane 433; the round
went on from 433.

The plan of the 429 is `522736429.plan` (SHA-256 bc2ace6cd996129921fc2ef7293f163f77848c6a6bb4da65032f302d52205637).
delcheck: 0 missing permutations, no letter can be deleted.

After it: the next polish step of the same run (relocate --dpa) gave a word of 522,736,428 letters at 11:56. The
n = 12 word of 522,736,428 letters that is submitted is another one: one more trailsearch of the 429 outside foreman
(kmax 8, T0 0.4, 1200 s, in the prepublication check of the 429), after which the check found nothing more. Another
full cycle of the chain from foreman's 428 found nothing.

## Programs

All of them are built from `tools/` of this repository: trailsearch, segins_ils, relocate, segins, loopscan, recut,
delcheck, word2plan and `tools/polish.sh`; steps 2-4 and 9 ran `tools/gpucuts/tsw5g2` with `orkern.ptx` on an NVIDIA
RTX 5090 (the program the arm calls), and the ils12.sh rounds are `tools/pipeline/ils12.sh`. Runs with several threads
need not repeat to the letter, so the same settings can give a word of another length; the plans above are the check.
