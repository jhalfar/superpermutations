import Superperm.N8k.Main
import Superperm.N8k_1746523ff629.Main
import Superperm.N8k_24efc13a6b92.Main
import Superperm.N8k_3677542ddb4f.Main
import Superperm.N8k_510faf236ad6.Main
import Superperm.N8k_6b1c42e70199.Main
import Superperm.N8k_b9001a0c8fdf.Main
import Superperm.N8k_e45fecc9625b.Main

/-!
# HasWord 8 46174: the published word and its seven ties

Statements in the vocabulary of Pantone's `Challenge.lean`, each proven by checking one literal word in the Lean
kernel with the rotation-class method (`Superperm/Cyc.lean`, certificates by `gen11.py`), as for `N8` (46,181).
The words are those of the repository (`words/superpermutation-8-46174.txt.xz` and `words/n8/ties/`);
`verify_blocks.py` compares the generated numbers with the word files.

| certificate | word file | SHA-256 of the letters, first 12 hex digits |
|---|---|---|
| `N8k` | `words/superpermutation-8-46174.txt.xz` | `50d9bb150ffc` |
| `N8k_1746523ff629` | `words/n8/ties/superpermutation-8-46174-1746523ff629.txt.xz` | `1746523ff629` |
| `N8k_24efc13a6b92` | `words/n8/ties/superpermutation-8-46174-24efc13a6b92.txt.xz` | `24efc13a6b92` |
| `N8k_3677542ddb4f` | `words/n8/ties/superpermutation-8-46174-3677542ddb4f.txt.xz` | `3677542ddb4f` |
| `N8k_510faf236ad6` | `words/n8/ties/superpermutation-8-46174-510faf236ad6.txt.xz` | `510faf236ad6` |
| `N8k_6b1c42e70199` | `words/n8/ties/superpermutation-8-46174-6b1c42e70199.txt.xz` | `6b1c42e70199` |
| `N8k_b9001a0c8fdf` | `words/n8/ties/superpermutation-8-46174-b9001a0c8fdf.txt.xz` | `b9001a0c8fdf` |
| `N8k_e45fecc9625b` | `words/n8/ties/superpermutation-8-46174-e45fecc9625b.txt.xz` | `e45fecc9625b` |
-/

namespace LiteralSuperperm

open SuperpermutationBounds

/-- A superpermutation on 8 symbols with 46,174 letters: `words/superpermutation-8-46174.txt.xz`
(SHA-256 of the letters 50d9bb150ffcf28482e4663f9d8a5ff449fae2de2ef09643eefd922fe1b224aa). -/
theorem hasWord_eight_k : HasWord 8 46174 := N8k.hasWord

theorem exists_word_eight_k : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k.word, N8k.word_covers, N8k.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-1746523ff629.txt.xz`
(SHA-256 of the letters 1746523ff6295904bc7192650dc81063a7943d72d24616152df3b660cf729bcf). -/
theorem hasWord_eight_k_1746523ff629 : HasWord 8 46174 := N8k_1746523ff629.hasWord

theorem exists_word_eight_k_1746523ff629 : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_1746523ff629.word, N8k_1746523ff629.word_covers, N8k_1746523ff629.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-24efc13a6b92.txt.xz`
(SHA-256 of the letters 24efc13a6b924f9f452d7f550badb3e500d6898111c912e5653d08feb6b17469). -/
theorem hasWord_eight_k_24efc13a6b92 : HasWord 8 46174 := N8k_24efc13a6b92.hasWord

theorem exists_word_eight_k_24efc13a6b92 : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_24efc13a6b92.word, N8k_24efc13a6b92.word_covers, N8k_24efc13a6b92.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-3677542ddb4f.txt.xz`
(SHA-256 of the letters 3677542ddb4fa816605b50d9216994e2b06ce50465e3f000d974068906b1a44f). -/
theorem hasWord_eight_k_3677542ddb4f : HasWord 8 46174 := N8k_3677542ddb4f.hasWord

theorem exists_word_eight_k_3677542ddb4f : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_3677542ddb4f.word, N8k_3677542ddb4f.word_covers, N8k_3677542ddb4f.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-510faf236ad6.txt.xz`
(SHA-256 of the letters 510faf236ad6e900257cf280beaff5712e9acab9aed3e12038f2f4b81729be6d). -/
theorem hasWord_eight_k_510faf236ad6 : HasWord 8 46174 := N8k_510faf236ad6.hasWord

theorem exists_word_eight_k_510faf236ad6 : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_510faf236ad6.word, N8k_510faf236ad6.word_covers, N8k_510faf236ad6.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-6b1c42e70199.txt.xz`
(SHA-256 of the letters 6b1c42e70199b911685c349e697dec82de1b749addb99e447510837893da5e64). -/
theorem hasWord_eight_k_6b1c42e70199 : HasWord 8 46174 := N8k_6b1c42e70199.hasWord

theorem exists_word_eight_k_6b1c42e70199 : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_6b1c42e70199.word, N8k_6b1c42e70199.word_covers, N8k_6b1c42e70199.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-b9001a0c8fdf.txt.xz`
(SHA-256 of the letters b9001a0c8fdfee13646b01919725779329a0ee95338cc6d2e5c096a1f26ced41). -/
theorem hasWord_eight_k_b9001a0c8fdf : HasWord 8 46174 := N8k_b9001a0c8fdf.hasWord

theorem exists_word_eight_k_b9001a0c8fdf : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_b9001a0c8fdf.word, N8k_b9001a0c8fdf.word_covers, N8k_b9001a0c8fdf.word_length⟩

/-- A superpermutation on 8 symbols with 46,174 letters: `words/n8/ties/superpermutation-8-46174-e45fecc9625b.txt.xz`
(SHA-256 of the letters e45fecc9625baf02c4dd7879d9668e7237f9e31305d52d99d53317e4e24ee7ae). -/
theorem hasWord_eight_k_e45fecc9625b : HasWord 8 46174 := N8k_e45fecc9625b.hasWord

theorem exists_word_eight_k_e45fecc9625b : ∃ w : List (Fin 8), Covers w ∧ w.length = 46174 :=
  ⟨N8k_e45fecc9625b.word, N8k_e45fecc9625b.word_covers, N8k_e45fecc9625b.word_length⟩

end LiteralSuperperm

#print axioms LiteralSuperperm.hasWord_eight_k
#print axioms LiteralSuperperm.exists_word_eight_k
#print axioms LiteralSuperperm.hasWord_eight_k_1746523ff629
#print axioms LiteralSuperperm.exists_word_eight_k_1746523ff629
#print axioms LiteralSuperperm.hasWord_eight_k_24efc13a6b92
#print axioms LiteralSuperperm.exists_word_eight_k_24efc13a6b92
#print axioms LiteralSuperperm.hasWord_eight_k_3677542ddb4f
#print axioms LiteralSuperperm.exists_word_eight_k_3677542ddb4f
#print axioms LiteralSuperperm.hasWord_eight_k_510faf236ad6
#print axioms LiteralSuperperm.exists_word_eight_k_510faf236ad6
#print axioms LiteralSuperperm.hasWord_eight_k_6b1c42e70199
#print axioms LiteralSuperperm.exists_word_eight_k_6b1c42e70199
#print axioms LiteralSuperperm.hasWord_eight_k_b9001a0c8fdf
#print axioms LiteralSuperperm.exists_word_eight_k_b9001a0c8fdf
#print axioms LiteralSuperperm.hasWord_eight_k_e45fecc9625b
#print axioms LiteralSuperperm.exists_word_eight_k_e45fecc9625b
