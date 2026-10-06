import Superperm.Literal

/-!
# The literal tree checked leaf by leaf

`Superperm/Cyc.lean` checks the literal tree against the number it spells in one kernel
computation (`chkT`), which holds the whole word several times per tree level in memory: 1.7 GB
for 44 million letters, far too much for 523 million.  Here nothing is computed on the whole
word.

`valT B d t` is the number a tree spells; it is only a definition, the kernel never evaluates
it.  `okT` checks three things, all on single blocks: the shape (depth `d`), that every leaf has
at most `B + K` digits, and that at every node the digits above `B` of the last leaf on the left
are the lowest `K` digits of the first leaf on the right, that is, that neighbouring blocks
agree on the `K` letters they share.  `okT_sound` shows that the tree is then
`build B K d (valT B d t)`, the form `Superperm/Literal.lean` reads words in.  `okT_node` lets
the generated files check the subtree of each block file on its own and join the results.

This file needs only `Superperm/Literal.lean`.
-/

namespace LiteralSuperperm

/-! ### The tree, leaf by leaf -/

/-- The number spelt by a tree of depth `d` whose leaves serve `B` digits each: the left half
gives the lowest `B * 2 ^ d'` digits, the right half the rest. -/
def valT (B : Nat) : Nat → WT → Nat
  | 0, .leaf x => x
  | d + 1, .node l r => valT B d l % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * valT B d r
  | _, _ => 0

def firstLeaf : WT → Nat
  | .leaf x => x
  | .node l _ => firstLeaf l

def lastLeaf : WT → Nat
  | .leaf x => x
  | .node _ r => lastLeaf r

/-- Shape, size of the leaves, and agreement of neighbouring leaves (`mK` is `16 ^ K - 1`). -/
def okT (B K mK : Nat) : Nat → WT → Bool
  | 0, .leaf x => Nat.beq (Nat.shiftRight x (Nat.mul 4 (Nat.add B K))) 0
  | d + 1, .node l r =>
    and (and (okT B K mK d l) (okT B K mK d r))
      (Nat.beq (Nat.shiftRight (lastLeaf l) (Nat.mul 4 B)) (Nat.land (firstLeaf r) mK))
  | _, _ => false

theorem okT_sound {B K mK : Nat} (hmK : mK = 2 ^ (4 * K) - 1) (hKB : K ≤ B) :
    ∀ (d : Nat) (t : WT), okT B K mK d t = true →
      t = build B K d (valT B d t) ∧ valT B d t < 16 ^ (B * 2 ^ d + K) ∧
      valT B d t / 16 ^ (B * 2 ^ d) = lastLeaf t / 16 ^ B ∧
      valT B d t % 16 ^ K = firstLeaf t % 16 ^ K := by
  intro d
  induction d with
  | zero =>
    intro t h
    cases t with
    | node l r => exact absurd h (by simp [okT])
    | leaf x =>
      have h0 : x >>> (4 * (B + K)) = 0 := Nat.eq_of_beq_eq_true h
      rw [shiftRight_four_mul] at h0
      have hlt : x < 16 ^ (B + K) := by
        rcases Nat.lt_or_ge x (16 ^ (B + K)) with h1 | h1
        · exact h1
        · have := Nat.div_pos h1 (Nat.pow_pos (by decide))
          omega
      refine ⟨rfl, ?_, ?_, rfl⟩
      · simpa [valT] using hlt
      · simp [valT, lastLeaf]
  | succ d ih =>
    intro t h
    cases t with
    | leaf x => exact absurd h (by simp [okT])
    | node l r =>
      have h' : ((okT B K mK d l && okT B K mK d r) &&
          Nat.beq (Nat.shiftRight (lastLeaf l) (Nat.mul 4 B)) (Nat.land (firstLeaf r) mK)) = true := h
      rw [Bool.and_eq_true, Bool.and_eq_true] at h'
      obtain ⟨hla, hlb, hlc, hld⟩ := ih l h'.1.1
      obtain ⟨hra, hrb, hrc, hrd⟩ := ih r h'.1.2
      have hfour : (2 : Nat) ^ 4 = 16 := by decide
      have hov : lastLeaf l / 16 ^ B = firstLeaf r % 16 ^ K := by
        have h2 : lastLeaf l >>> (4 * B) = firstLeaf r &&& mK := Nat.eq_of_beq_eq_true h'.2
        rw [hmK, shiftRight_four_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul 2 4, hfour] at h2
        exact h2
      -- names for the two halves
      generalize hxl : valT B d l = xl at hla hlb hlc hld
      generalize hxr : valT B d r = xr at hra hrb hrc hrd
      have hval : valT B (d + 1) (WT.node l r) = xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr := by
        show valT B d l % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * valT B d r = _
        rw [hxl, hxr]
      have hpos : 0 < 16 ^ (B * 2 ^ d) := Nat.pow_pos (by decide)
      have f1 : (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr) / 16 ^ (B * 2 ^ d) = xr := by
        rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (Nat.mod_lt _ hpos), Nat.zero_add]
      have f2 : (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr) % 16 ^ (B * 2 ^ d) =
          xl % 16 ^ (B * 2 ^ d) := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
      have f3 : (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr) % 16 ^ (B * 2 ^ d + K) = xl := by
        rw [Nat.pow_add, Nat.mod_mul, f1, f2, hrd, ← hov, ← hlc, Nat.mod_add_div]
      have hdouble : B * 2 ^ (d + 1) = B * 2 ^ d + B * 2 ^ d := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      rw [hval]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- the tree
        show WT.node l r = WT.node
          (build B K d (Nat.land (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr)
            (Nat.sub (Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1)))
          (build B K d (Nat.shiftRight (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr)
            (Nat.mul 4 (Nat.mul B (Nat.pow 2 d)))))
        have e1 : Nat.land (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr)
            (Nat.sub (Nat.pow 2 (Nat.mul 4 (Nat.add (Nat.mul B (Nat.pow 2 d)) K))) 1) = xl := by
          show (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr) &&& (2 ^ (4 * (B * 2 ^ d + K)) - 1) = xl
          rw [Nat.and_two_pow_sub_one_eq_mod, Nat.pow_mul 2 4, hfour, f3]
        have e2 : Nat.shiftRight (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr)
            (Nat.mul 4 (Nat.mul B (Nat.pow 2 d))) = xr := by
          show (xl % 16 ^ (B * 2 ^ d) + 16 ^ (B * 2 ^ d) * xr) >>> (4 * (B * 2 ^ d)) = xr
          rw [shiftRight_four_mul, f1]
        rw [e1, e2, ← hla, ← hra]
      · -- the size
        have h1 : xl % 16 ^ (B * 2 ^ d) < 16 ^ (B * 2 ^ d) := Nat.mod_lt _ hpos
        have h2 : 16 ^ (B * 2 ^ d) * (xr + 1) ≤ 16 ^ (B * 2 ^ d) * 16 ^ (B * 2 ^ d + K) :=
          Nat.mul_le_mul_left _ hrb
        rw [hdouble, Nat.add_assoc, Nat.pow_add]
        rw [Nat.mul_add, Nat.mul_one] at h2
        omega
      · -- the top digits
        rw [hdouble, Nat.pow_add, ← Nat.div_div_eq_div_mul, f1]
        exact hrc
      · -- the lowest digits
        have hdvd : 16 ^ K ∣ 16 ^ (B * 2 ^ d) :=
          Nat.pow_dvd_pow 16 (Nat.le_trans hKB (Nat.le_mul_of_pos_right B (Nat.pow_pos (by decide))))
        rw [← Nat.mod_mod_of_dvd _ hdvd, f2, Nat.mod_mod_of_dvd _ hdvd]
        exact hld

/-- The check of a node from the checks of its two halves and the agreement of the two leaves
that meet in the middle. -/
theorem okT_node {B K mK d : Nat} {l r : WT} (hl : okT B K mK d l = true)
    (hr : okT B K mK d r = true)
    (hadj : Nat.beq (Nat.shiftRight (lastLeaf l) (Nat.mul 4 B)) (Nat.land (firstLeaf r) mK) = true) :
    okT B K mK (d + 1) (WT.node l r) = true := by
  show ((okT B K mK d l && okT B K mK d r) &&
    Nat.beq (Nat.shiftRight (lastLeaf l) (Nat.mul 4 B)) (Nat.land (firstLeaf r) mK)) = true
  rw [hl, hr, hadj]
  rfl

end LiteralSuperperm
