# Commitment for a probabilistic check (n = 18)

This file fixes, before the random keys exist, everything that a probabilistic check of an 18-symbol word depends
on. The check (a hash of the set of completed groups, as in `recipes/n17`'s hash mode, with four keys r_1..r_4 modulo
2^61 - 1) can only be fooled by someone who knows the keys when the plan is fixed. The keys come from a drand round
that is released after this commit.

| what | SHA-256 |
|---|---|
| the unit plan (15,602,710,590 bytes) | `725d7a39d348237c18684a1b537005973e0303203b45fdacefa5aa57ba568094` |
| checker source `mh6.c` | `bd1d12bec527b874e6a19e652d90e2bfbd277fbaf655eb88474c29cff04b1758` |
| `gcard6.h` | `b1d75b26a0252f1d1c04f4464978c21a2d747b7a4a24567fb6a1a64274159d99` |
| `gcheck6.cu` | `a301ed1a0f13d17e179db46ad0b4bf1a4513dfe2bede26aa05e9740c3ecae993` |
| `gcheck6.ptx` | `27fa7aec6895a3ed1a9988330b252c12794374415ff7011705e45022ad4a1395` |
| generator `genB6.c` | `fdc067f1b4d9cd8fb516e413d85e1033c788823291a8056e7501b6273c7d15bc` |
| `blake3.h` (as in `recipes/n17`) | `9ceee7884dce0f39233926c8f38de2a41b22fc69e21601cb780572a0a9aa6b28` |
| checker binary `mh6.exe` (MinGW gcc 13.2) | `a290b111d74c788d2a897f49603f7daf1088fc6b99ae10bf6e1bf354133f8a60` |
| selection (`arrange/data/n12t-selection.txt.xz`, unpacked) | `4f31dab69be987cb94cc993bf78f854833d861970c1f57ec290bebbe198d2a1a` |
| block (`proofs/lean/constant305989/data/s103_old2_0.txt`) | `6dbc820dfa9702a2114b64d2b0f71342bec166ebbc61b8a13682834dbeba6618` |

**Keys.** drand quicknet (chain hash `52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971`, one round
every 3 s), round **33475799**, released at 2026-10-28 23:39:21 UTC (unix time 1793230761). For k = 1..4 and j = 0, 1, 2, ...:
x = SHA-256(randomness || plan || k || j), with randomness the 32 bytes of that round's `randomness`, plan the 32
bytes of the plan's SHA-256 above, k and j one byte each; r = (x read big-endian, mod 2^64) AND (2^61 - 1); the first
j with 2 <= r <= 2^61 - 3 gives r_k.

The sources, the plan and the result will be published with the word.
