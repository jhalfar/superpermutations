import Superperm.Cyc2

/-!
# The same checks with fewer kernel steps

`partCycF` computes what `partCyc` computes (`partCycF_eq`), so a kernel check of `partCycF … = true`
is a proof of `partCyc … = true`; nothing in the soundness proofs changes.  The kernel spends
its time in the bookkeeping of the recursions, not in the arithmetic, so two things are written
differently:

* `getR` is `getT` written with the recursor of `WT` instead of structural recursion (which the
  kernel sees through `brecOn` and a matcher);
* `goF` is `go` with the last three levels of the walk written out (`go3`): six leaves at a time,
  with no list operation between them.
-/

namespace LiteralSuperperm

/-! ### The lookup -/

/-- `getT`, by the recursor. -/
noncomputable def getR (t : WT) : Nat → Nat → Nat :=
  WT.rec (motive := fun _ => Nat → Nat → Nat)
    (fun x _ q => Nat.shiftRight x q)
    (fun _ _ il ir h q =>
      Bool.rec (motive := fun _ => Nat) (il (Nat.shiftRight h 1) q)
        (ir (Nat.shiftRight h 1) (Nat.sub q h)) (Nat.ble h q)) t

theorem getR_eq : ∀ (t : WT) (h q : Nat), getR t h q = getT t h q := by
  intro t
  induction t with
  | leaf x => intro h q; rfl
  | node l r ihl ihr =>
    intro h q
    show Bool.rec (motive := fun _ => Nat) (getR l (Nat.shiftRight h 1) q)
        (getR r (Nat.shiftRight h 1) (Nat.sub q h)) (Nat.ble h q) =
      (bif Nat.ble h q then getT r (Nat.shiftRight h 1) (Nat.sub q h)
        else getT l (Nat.shiftRight h 1) q)
    rw [ihl, ihr]
    cases Nat.ble h q <;> rfl

/-- `leafCyc` with `getR`. -/
noncomputable def leafF (Kw L S mS mW M h0 : Nat) (tree : WT) (c tbl : Nat) : Bool :=
  and (Nat.ble (Nat.add (Nat.land tbl mS) Kw) L)
    (Nat.beq (Nat.land (getR tree h0 (Nat.mul 4 (Nat.land tbl mS))) mW)
      (Nat.land (Nat.shiftRight (Nat.mul c M) (Nat.mul 4 (Nat.land (Nat.shiftRight tbl S) 15))) mW))

theorem leafF_eq (Kw L S mS mW M h0 : Nat) (tree : WT) :
    leafF Kw L S mS mW M h0 tree = leafCyc Kw L S mS mW M h0 tree := by
  funext c tbl
  show (and _ (Nat.beq (Nat.land (getR tree h0 _) mW) _)) = (and _ (Nat.beq (Nat.land (getT tree h0 _) mW) _))
  rw [getR_eq]

/-! ### The walk -/

/-- The walk over the arrangements of two symbols, written out. -/
def go2 (leaf : Nat → Nat → Bool) (rem : List Nat) (c tbl stride : Nat) : Bool :=
  match rem with
  | [a, b] =>
    and (leaf (step (step c a) b) tbl) (leaf (step (step c b) a) (Nat.shiftRight tbl stride))
  | _ => go leaf 2 rem c tbl stride

theorem go2_eq (leaf : Nat → Nat → Bool) (rem : List Nat) (c tbl stride : Nat) :
    go2 leaf rem c tbl stride = go leaf 2 rem c tbl stride := by
  unfold go2
  split
  · rename_i a b
    have h1 : erase1 [a, b] a = [b] := by simp [erase1]
    show _ = loop (fun x t => go leaf 1 (erase1 [a, b] x) (step c x) t (Nat.div stride 1)) stride [a, b] tbl
    show _ = and (go leaf 1 (erase1 [a, b] a) (step c a) tbl (Nat.div stride 1))
      (and (go leaf 1 (erase1 [a, b] b) (step c b) (Nat.shiftRight tbl stride) (Nat.div stride 1)) true)
    rw [h1]
    by_cases hab : a = b
    · subst hab
      rw [h1]
      show _ = and (and (leaf (step (step c a) a) tbl) true)
        (and (and (leaf (step (step c a) a) (Nat.shiftRight tbl stride)) true) true)
      simp
    · have h2 : erase1 [a, b] b = [a] := by
        have : Nat.beq a b = false := by
          rw [← Bool.not_eq_true]
          intro hh
          exact hab (Nat.eq_of_beq_eq_true hh)
        simp [erase1, this]
      rw [h2]
      show _ = and (and (leaf (step (step c a) b) tbl) true)
        (and (and (leaf (step (step c b) a) (Nat.shiftRight tbl stride)) true) true)
      simp
  · rfl

/-- The walk over the arrangements of three symbols, written out: six leaves.  (If the first and
the last symbol are equal, which does not happen in a walk, `go` visits them in another order,
so that case is left to `go`.) -/
def go3 (leaf : Nat → Nat → Bool) (rem : List Nat) (c tbl stride : Nat) : Bool :=
  match rem with
  | [x, y, z] =>
    bif Nat.beq x z then go leaf 3 [x, y, z] c tbl stride
    else
      and
        (and (leaf (step (step (step c x) y) z) tbl)
          (leaf (step (step (step c x) z) y) (Nat.shiftRight tbl (Nat.div stride 2))))
        (and
          (and (leaf (step (step (step c y) x) z) (Nat.shiftRight tbl stride))
            (leaf (step (step (step c y) z) x)
              (Nat.shiftRight (Nat.shiftRight tbl stride) (Nat.div stride 2))))
          (and
            (and (leaf (step (step (step c z) x) y) (Nat.shiftRight (Nat.shiftRight tbl stride) stride))
              (leaf (step (step (step c z) y) x)
                (Nat.shiftRight (Nat.shiftRight (Nat.shiftRight tbl stride) stride) (Nat.div stride 2))))
            true))
  | _ => go leaf 3 rem c tbl stride

theorem go3_eq (leaf : Nat → Nat → Bool) (rem : List Nat) (c tbl stride : Nat) :
    go3 leaf rem c tbl stride = go leaf 3 rem c tbl stride := by
  unfold go3
  split
  · rename_i x y z
    by_cases hxz : Nat.beq x z = true
    · rw [hxz, cond_true]
    · rw [Bool.not_eq_true] at hxz
      rw [hxz, cond_false]
      have h1 : erase1 [x, y, z] x = [y, z] := by simp [erase1]
      have h2 : erase1 [x, y, z] y = [x, z] := by
        by_cases hxy : x = y
        · subst hxy; simp [erase1]
        · have : Nat.beq x y = false := by
            rw [← Bool.not_eq_true]
            intro hh
            exact hxy (Nat.eq_of_beq_eq_true hh)
          simp [erase1, this]
      have h3 : erase1 [x, y, z] z = [x, y] := by
        by_cases hyz : y = z
        · subst hyz; simp [erase1, hxz]
        · have : Nat.beq y z = false := by
            rw [← Bool.not_eq_true]
            intro hh
            exact hyz (Nat.eq_of_beq_eq_true hh)
          simp [erase1, hxz, this]
      show _ = and (go leaf 2 (erase1 [x, y, z] x) (step c x) tbl (Nat.div stride 2))
        (and (go leaf 2 (erase1 [x, y, z] y) (step c y) (Nat.shiftRight tbl stride) (Nat.div stride 2))
          (and (go leaf 2 (erase1 [x, y, z] z) (step c z)
            (Nat.shiftRight (Nat.shiftRight tbl stride) stride) (Nat.div stride 2)) true))
      rw [h1, h2, h3, ← go2_eq, ← go2_eq, ← go2_eq]
      rfl
  · rfl

/-- `go` with the last three levels written out. -/
def goF (leaf : Nat → Nat → Bool) : Nat → List Nat → Nat → Nat → Nat → Bool
  | 0, _, c, tbl, _ => leaf c tbl
  | r + 1, rem, c, tbl, stride =>
    loop (fun a t =>
      bif Nat.beq r 3 then go3 leaf (erase1 rem a) (step c a) t (Nat.div stride r)
      else bif Nat.beq r 2 then go2 leaf (erase1 rem a) (step c a) t (Nat.div stride r)
      else goF leaf r (erase1 rem a) (step c a) t (Nat.div stride r)) stride rem tbl

theorem goF_eq (leaf : Nat → Nat → Bool) : ∀ (r : Nat) (rem : List Nat) (c tbl stride : Nat),
    goF leaf r rem c tbl stride = go leaf r rem c tbl stride := by
  intro r
  induction r with
  | zero => intro rem c tbl stride; rfl
  | succ r ih =>
    intro rem c tbl stride
    show loop (fun a t =>
        bif Nat.beq r 3 then go3 leaf (erase1 rem a) (step c a) t (Nat.div stride r)
        else bif Nat.beq r 2 then go2 leaf (erase1 rem a) (step c a) t (Nat.div stride r)
        else goF leaf r (erase1 rem a) (step c a) t (Nat.div stride r)) stride rem tbl =
      loop (fun a t => go leaf r (erase1 rem a) (step c a) t (Nat.div stride r)) stride rem tbl
    congr 1
    funext a t
    by_cases h3 : Nat.beq r 3 = true
    · have : r = 3 := Nat.eq_of_beq_eq_true h3
      subst this
      rw [h3, cond_true, go3_eq]
    · rw [Bool.not_eq_true] at h3
      rw [h3, cond_false]
      by_cases h2 : Nat.beq r 2 = true
      · have : r = 2 := Nat.eq_of_beq_eq_true h2
        subst this
        rw [h2, cond_true, go2_eq]
      · rw [Bool.not_eq_true] at h2
        rw [h2, cond_false, ih]

/-! ### The check for one branch -/

/-- `partCyc` with `goF` and `leafF`. -/
noncomputable def partCycF (K Kw L S mS mW M h0 : Nat) (tree : WT) (stride : Nat) (t : List Nat)
    (tbl : Nat) : Bool :=
  goF (leafF Kw L S mS mW M h0 tree) (Nat.sub K (Nat.succ t.length))
    ((Nat.pred K :: t).foldl erase1 (List.range K)) ((Nat.pred K :: t).foldl step 0) tbl stride

theorem partCycF_eq {K Kw L S mS mW M h0 : Nat} {tree : WT} {stride : Nat} {t : List Nat}
    {tbl : Nat} :
    partCycF K Kw L S mS mW M h0 tree stride t tbl = partCyc K Kw L S mS mW M h0 tree stride t tbl := by
  unfold partCycF partCyc
  rw [goF_eq, leafF_eq]

end LiteralSuperperm
