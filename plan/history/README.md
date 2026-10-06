# Plans of earlier words

Words found on the way to the ones in the main table, kept as plans. A plan is a short text file that says how to
write a word from the trails of a base word, so the published tool rebuilds each word in seconds (n=11), about a
minute (n=12) or about ten minutes and 11 GB of RAM (n=13, with `--threads 1`):

```sh
cc -O2 -fopenmp -o trailsearch tools/trailsearch.c -lm
./trailsearch BASE.txt rebuilt.txt --plan-in plan/history/NAME.plan --time 0
sha256sum rebuilt.txt
```

Every plan here was rebuilt this way and the word checked with `tools/delcheck.c`: all permutations present, no
single letter can be deleted. The SHA-256 is that of the rebuilt word (one line plus LF).

| n | length | base word | plan | how it was reached | SHA-256 of the word |
|---|---|---|---|---|---|
| 11 | 43,930,625 | my 43,930,674 word (`words/superpermutation-11-43930674.txt.xz`) | [`trailsearch-11-43930625.plan`](trailsearch-11-43930625.plan) | fixed-order pass (step 3) on the 43,930,628 word | `f79f7775ee881bb57bb63c02b0a44b9290d078553e46eaf8f4a13de93933640a` |
| 11 | 43,930,621 | my 43,930,674 word (`words/superpermutation-11-43930674.txt.xz`) | [`trailsearch-11-43930621.plan`](trailsearch-11-43930621.plan) | segment insertion on 43,930,623 | `c8faaa717abb3bf05e4c76fdcf0c64c1dfb433117f71d83f7caf4f8b1f8c048d` |
| 11 | 43,930,619 | my 43,930,674 word (`words/superpermutation-11-43930674.txt.xz`) | [`trailsearch-11-43930619.plan`](trailsearch-11-43930619.plan) | segment insertion, next step | `e22d43e758f14a81aac379861bcf8b36d4f6c378a002ec9ef4182f9e56b60a59` |
| 11 | 43,930,615 | my 43,930,674 word (`words/superpermutation-11-43930674.txt.xz`) | [`trailsearch-11-43930615.plan`](trailsearch-11-43930615.plan) | segment insertion, next step (614 follows) | `c6cf42cb7ade14db6aea65d5c972336434838738c1288201d8776c8cba9ca589` |
| 11 | 43,930,618 | Pantone's 43,930,680 word | [`trailsearch-11-43930618.plan`](trailsearch-11-43930618.plan) | second line: fixed-order pass and segment insertion on the 43,930,628 word | `e88f6b8e86fde2e1fd96978c038947106cfbc9c90d51b988f23e78c784efe78d` |
| 11 | 43,930,615 | Pantone's 43,930,680 word | [`trailsearch-11-43930615-b.plan`](trailsearch-11-43930615-b.plan) | second line, continued; a different word from the 615 above | `36083d787e7b85a4a80b4d9d149c5d70dfedc79abb001bf9ec1fb00e9b2a486f` |
| 12 | 522,745,537 | Pantone's 522,745,581 word | [`trailsearch-12-522745537.plan`](trailsearch-12-522745537.plan) | trail search (step 2), the word before step 3 | `a385ec1e49affbd47b814227115c534b46a60d9beb5baea28ff028271607d36e` |
| 12 | 522,745,516 | Pantone's 522,745,581 word | [`trailsearch-12-522745516.plan`](trailsearch-12-522745516.plan) | second line: two rounds of GPU search from 522,745,531, each followed by the fixed-order pass | `b6abb98aa3a0b6d72b6516313865e40879ec2fc65cf3e8fab7cfa24a8bebf327` |
| 12 | 522,745,508 | Pantone's 522,745,581 word | [`trailsearch-12-522745508.plan`](trailsearch-12-522745508.plan) | second line: one more round and pass | `efe5721f6502d566b713054a3e39d5c380ccd531d7f6a73192fd3a5febb4144a` |
| 12 | 522,745,503 | Pantone's 522,745,581 word | [`trailsearch-12-522745503.plan`](trailsearch-12-522745503.plan) | second line: loop moves and the pass | `65474880fc643e5d86b35ebdb7311fd4c68b7d0ec4c5fbb93a6c2ec8b2921274` |
| 12 | 522,745,494 | Pantone's 522,745,581 word | [`trailsearch-12-522745494.plan`](trailsearch-12-522745494.plan) | second line: first round with block moves, loop moves and the pass | `2fad024c8cd38f56ffa955960875a90852c99c992a08dca4020535683bdd169b` |
| 12 | 522,745,474 | Pantone's 522,745,581 word | [`trailsearch-12-522745474.plan`](trailsearch-12-522745474.plan) | second line: eight more rounds | `e2c0da1d86ac3220da66c28727bb5c4af505612702cc25965cb541fecffb6ac5` |
| 12 | 522,745,530 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745530-rb.plan`](trailsearch-12-522745530-rb.plan) | fixed-order pass with openings inside a 1-cycle, on the 522,745,537 word | `b56d321d9cf9705cc72afc565d3ff039a1d8ccb9dee9548b952cabbb56a9647d` |
| 12 | 522,745,526 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745526-rb.plan`](trailsearch-12-522745526-rb.plan) | one round of GPU search and the fixed-order pass | `021ab63aa9777844123e6161ce1445b891b1fc253150444f5ee8a6f5c8c95af2` |
| 12 | 522,745,512 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745512-rb.plan`](trailsearch-12-522745512-rb.plan) | one more round and pass | `3492fe141cf340fc5217ae68054bb7afd3947f56f2a21faf4d4a1072d19075b5` |
| 12 | 522,745,505 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745505-rb.plan`](trailsearch-12-522745505-rb.plan) | one more round and pass | `7cd226e4450c0f49408223ead2ec664a1f6d72811fdf0efaf3e200e6845bde78` |
| 12 | 522,745,498 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745498-rb.plan`](trailsearch-12-522745498-rb.plan) | five minutes of GPU search with block moves | `8097afd9a8bd9ae49eb6e563bc00b8bd11cc47edf9df7def27dc2e3ad3a08079` |
| 12 | 522,745,482 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745482-rb.plan`](trailsearch-12-522745482-rb.plan) | a loop move and one 20-minute round with block moves | `7074a65f462c689b4fbdd3736dfdfdee8b1aacae134705c0a84f9502828085a0` |
| 12 | 522,745,466 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745466-rb.plan`](trailsearch-12-522745466-rb.plan) | relocation with re-opening on 522,745,482 (a side branch) | `3176a29a0fec5e6466de7eca6be23c97a9c00707bf086442dd3b143ca24c366a` |
| 12 | 522,745,464 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745464-rb.plan`](trailsearch-12-522745464-rb.plan) | eight more rounds with block moves from 522,745,482 | `e86ea8cb53583f6d5fb267a8e10fd690b8ff85430e78cbc7cd6f327fe2891c24` |
| 12 | 522,745,445 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745445-rb.plan`](trailsearch-12-522745445-rb.plan) | relocation with re-opening on 522,745,464 | `fc52ead7b97ba3b50775c3359bb559336e498713b27dba7bda72a30841ef8a90` |
| 12 | 522,745,383 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745383-rb.plan`](trailsearch-12-522745383-rb.plan) | segment insertion on 522,745,445 (its plan on Pantone's word is in `plan/`) | `6d787880b4b660f36428715f11a178af816bd1a936f95cfb518217685d99382e` |
| 12 | 522,745,376 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745376-rb.plan`](trailsearch-12-522745376-rb.plan) | one more round of GPU search (522,745,379) and segment insertion again (its plan on Pantone's word is in `plan/`) | `964c633ea377ecbaea3f0d30e974a2ecb925c2e810de8997abf1aa37b92763b1` |
| 12 | 522,745,374 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745374-rb.plan`](trailsearch-12-522745374-rb.plan) | a short hot search from 522,745,376 that ends on another sequence one letter longer, then relocation, a loop move and segment insertion on that sequence | `923970bb594a4a27075434f742f35396927171681f054e996c7b712dff14b233` |
| 12 | 522,745,366 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745366-rb.plan`](trailsearch-12-522745366-rb.plan) | segment insertion with up to five cuts on 522,745,374 | `15f9ee4f478bcdcb1a751975d43deb9014c1aca11944ff56400b0976f09e1749` |
| 12 | 522,745,356 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745356-rb.plan`](trailsearch-12-522745356-rb.plan) | another short hot search from 522,745,366, then relocation, loop moves and segment insertion with up to five cuts (its plan on Pantone's word is in `plan/`) | `cfe09d18369578c7ad619d570d701d01c400963e5848d1ddfa737bb04593bfc6` |
| 12 | 522,745,355 | `base-12-rebased.txt.xz` (below) | [`trailsearch-12-522745355-rb.plan`](trailsearch-12-522745355-rb.plan) | one more such start from 522,745,356 (the current word; its plan on Pantone's word is in `plan/`) | `f5a5b106ebf9a5ee1deb1f168ffa182d91e5b447685a9f86e33598c655098488` |
| 12 | 522,737,299 | the n = 12 base word that `reproduce/tools/geng.py` writes (see [`REPRODUCE.md`](../../reproduce/REPRODUCE.md)) | [`n12-522737299.plan`](n12-522737299.plan) | on the closed trails of selection E: the first word I published on them (`words/superpermutation-12-522737299.txt.xz`), before more local kicks gave 522,737,175 | `acac6023eff390880f8fec3e48fc3b7ef24c5a45e71bbf8c328a6d8615901717` |
| 13 | 6,747,917,445 | my 6,747,918,058 word (`words/superpermutation-13-6747918058.txt.xz`) | [`trailsearch-13-6747917445.plan`](trailsearch-13-6747917445.plan) | relocation with re-opening on 6,747,917,464 (whose plan is in `plan/`) | `225ecc2d6f19600ec8384f0092aced150805dcea39903dacf0fd5bdccba1c87e` |
| 13 | 6,747,802,875 | the n = 13 base word that `reproduce/tools/geng.py` writes (see [`REPRODUCE.md`](../../reproduce/REPRODUCE.md)) | [`n13-6747802875.plan`](n13-6747802875.plan) | on the closed trails of selection N: the first word I published on them (`words/superpermutation-13-6747802875.txt.xz`), before more passes with moves of equal length gave 6,747,802,562 | `91fc31abc4d28626a6839e3c8263f676377744a173349f4ecfd02a3309a337f6` |

## The re-based word for n=12

`base-12-rebased.txt.xz` (522,993,734 letters, SHA-256 `f973097e4b81803208b4e34376ac16187e9f996edd4b9c516f80c1457cd6b4c2`)
is not a short word. It holds the trails of Pantone's 522,745,581 word written one after another, except that two
trails which my 522,745,530 word joins tightly (overlap of n-2 letters, after openings inside a 1-cycle) are
written as one open piece. The search tool never moves an open piece, so plans relative to this word (`-rb`) can
be searched from safely. The same words written as plans on Pantone's word need trimmed segments there; they
rebuild correctly but are not safe starting points for the search.

The second n=12 line (plans on Pantone's word, 522,745,516 to 522,745,474) and the second n=11 line (plans on
Pantone's 43,930,680 word) are independent of the lines that led to the current words, in case someone wants a
different starting point.
