import LowerBounds.PLevels

/-!
# Reading a sequence backwards (the written proof, section 4.3)

`rho e` is the entry of the block entered at `e`, read backwards: the exit of the block, reversed.
Lemma RV: `rho` maps permutation words to permutation words (`rho_perm`), keeps the classes apart
(`rho_rot`), and turns a step of weight `d` from the block of `u` to `v` into a step of weight `d`
from the block of `rho v` to `rho u` (`rho_wlink`; `d = 2` is part (3) of the lemma, `d = 3, 4`
part (4)).

`revA k c L` is the list of rows `L` read backwards: the rows in reverse order, every row with its
blocks reversed and replaced by `rho`, every link with its kind; `c` is the kind of the link that
follows `L`.  Corollary RV: it is a sequence (`isSeq_revA`) with the same number of rows, holes
and links of weight 4.  `revA_append` says where a cut of the sequence goes.
-/

namespace SuperpermLowerBounds
namespace KS

open S (PermW WLink)
open PS (TRow IsSeq LinkK holesT linksT)

variable {k : ℕ}

/-! ### Words -/

/-- The entry of the block entered at `e`, read backwards. -/
def rho (k : ℕ) (e : List ℕ) : List ℕ := (e.rotate (k - 1)).reverse

theorem rho_perm {w : List ℕ} (h : PermW k w) : PermW k (rho k w) := by
  have h' := h.rotate (k - 1)
  refine ⟨List.nodup_reverse.mpr h'.1, ?_, fun a => ?_⟩
  · rw [rho, List.length_reverse]
    exact h'.2.1
  · rw [rho, List.mem_reverse]
    exact h'.2.2 a

/-- **Lemma RV (3), (4).** -/
theorem rho_wlink {d : ℕ} (hk : 1 ≤ k) (hd : d ≤ k) {u v : List ℕ} (hu : u.length = k)
    (hv : v.length = k) (h : WLink k d u v) : WLink k d (rho k v) (rho k u) := by
  unfold WLink at h ⊢
  unfold rho
  have e0 : v.rotate k = v := by
    rw [← hv]
    exact List.rotate_length v
  have e1 : (v.rotate (k - 1)).reverse.rotate (k - 1) = v.reverse := by
    rw [List.rotate_reverse, List.length_rotate, hv, Nat.mod_eq_of_lt (by omega),
      show k - (k - 1) = 1 from by omega, List.rotate_rotate, show k - 1 + 1 = k from by omega, e0]
  rw [e1, List.take_reverse, List.length_rotate, hu, show k - (k - d) = d from by omega, h,
    List.reverse_take, hv, show k - (k - d) = d from by omega]

/-- **Lemma RV (1)**: different classes stay different. -/
theorem rho_rot {u v : List ℕ} (h : ¬ u ~r v) : ¬ rho k u ~r rho k v := by
  intro h'
  apply h
  have h1 : u.rotate (k - 1) ~r v.rotate (k - 1) := List.isRotated_reverse_iff.mp h'
  have hu : u ~r u.rotate (k - 1) := ⟨k - 1, rfl⟩
  have hv : v ~r v.rotate (k - 1) := ⟨k - 1, rfl⟩
  exact (hu.trans h1).trans hv.symm

/-! ### Rows and sequences -/

/-- The blocks of a row, read backwards. -/
def rhoRow (k : ℕ) (Q : List (List ℕ)) : List (List ℕ) := (Q.map (rho k)).reverse

theorem length_rhoRow (Q : List (List ℕ)) : (rhoRow k Q).length = Q.length := by
  simp [rhoRow]

/-- The rows read backwards; `c` is the kind of the link that follows the rows. -/
def revA (k : ℕ) (c : ℕ) : List TRow → List TRow
  | [] => []
  | [x] => [(c, rhoRow k x.2)]
  | x :: y :: rest => revA k c (y :: rest) ++ [(y.1, rhoRow k x.2)]

theorem revA_cons_cons (c : ℕ) (x y : TRow) (rest : List TRow) :
    revA k c (x :: y :: rest) = revA k c (y :: rest) ++ [(y.1, rhoRow k x.2)] := rfl

theorem length_revA (c : ℕ) : ∀ L : List TRow, (revA k c L).length = L.length
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [revA_cons_cons, List.length_append, length_revA c (y :: rest)]
    simp

theorem holesT_revA (c : ℕ) : ∀ L : List TRow, holesT k (revA k c L) = holesT k L
  | [] => rfl
  | [x] => by simp [revA, holesT, length_rhoRow]
  | x :: y :: rest => by
    rw [revA_cons_cons, PS.holesT_append, holesT_revA c (y :: rest), PS.holesT_cons x]
    simp [holesT, length_rhoRow]
    omega

theorem revA_ne_nil (c : ℕ) {L : List TRow} (h : L ≠ []) : revA k c L ≠ [] := by
  intro h'
  have := length_revA (k := k) c L
  rw [h'] at this
  exact h (List.length_eq_zero_iff.mp this.symm)

/-- The first row of the reversed list has the kind `c`. -/
theorem revA_head (c : ℕ) : ∀ (x : TRow) (rest : List TRow),
    ∃ Q T, revA k c (x :: rest) = (c, Q) :: T
  | x, [] => ⟨rhoRow k x.2, [], rfl⟩
  | x, y :: rest => by
    obtain ⟨Q, T, h⟩ := revA_head c y rest
    exact ⟨Q, T ++ [(y.1, rhoRow k x.2)], by rw [revA_cons_cons, h]; rfl⟩

/-- The last row of the reversed list is the first row, read backwards. -/
theorem revA_last (c : ℕ) : ∀ (x : TRow) (rest : List TRow),
    ∃ T c', revA k c (x :: rest) = T ++ [(c', rhoRow k x.2)]
  | _, [] => ⟨[], c, rfl⟩
  | _, y :: rest => ⟨revA k c (y :: rest), y.1, rfl⟩

theorem linksT_revA (c : ℕ) : ∀ L : List TRow, linksT (revA k c L) = linksT L
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    have h1 := PS.linksT_append (revA k c (y :: rest)) (y.1, rhoRow k x.2) []
      (revA_ne_nil c (List.cons_ne_nil y rest))
    have h2 := PS.linksT_append [x] y rest (List.cons_ne_nil x [])
    have ih := linksT_revA c (y :: rest)
    have e : ([x] ++ y :: rest) = x :: y :: rest := rfl
    have e1 : linksT [x] = 0 := rfl
    have e2 : linksT [((y.1, rhoRow k x.2) : TRow)] = 0 := rfl
    rw [e, e1] at h2
    rw [e2, ih] at h1
    dsimp only at h1
    rw [revA_cons_cons, h1, h2]
    omega

theorem mem_revA {c : ℕ} {z : TRow} : ∀ {L : List TRow}, z ∈ revA k c L →
    ∃ x ∈ L, z.2 = rhoRow k x.2 ∧ (z.1 = c ∨ ∃ y ∈ L, z.1 = y.1)
  | [], h => by simp [revA] at h
  | [x], h => by
    simp only [revA, List.mem_singleton] at h
    exact ⟨x, List.mem_singleton_self x, by rw [h], Or.inl (by rw [h])⟩
  | x :: y :: rest, h => by
    rw [revA_cons_cons, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨x', hx', h1, h2⟩ := mem_revA h
      refine ⟨x', List.mem_cons_of_mem _ hx', h1, ?_⟩
      rcases h2 with h2 | ⟨y', hy', h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨y', List.mem_cons_of_mem _ hy', h2⟩
    · exact ⟨x, List.mem_cons_self, by rw [h], Or.inr ⟨y, by simp, by rw [h]⟩⟩

/-- Where a cut goes: the rows behind the cut come first. -/
theorem revA_append (c : ℕ) (y : TRow) (B : List TRow) : ∀ A : List TRow,
    revA k c (A ++ y :: B) = revA k c (y :: B) ++ revA k y.1 A
  | [] => by simp [revA]
  | [x] => rfl
  | x :: x' :: A => by
    have ih := revA_append c y B (x' :: A)
    have e : x :: x' :: A ++ y :: B = x :: x' :: (A ++ y :: B) := rfl
    rw [e, revA_cons_cons]
    have e' : x' :: (A ++ y :: B) = x' :: A ++ y :: B := rfl
    rw [e', ih, revA_cons_cons, List.append_assoc]

/-- The blocks of the reversed list. -/
theorem blocks_revA (c : ℕ) : ∀ L : List TRow,
    ((revA k c L).map Prod.snd).flatten = (((L.map Prod.snd).flatten).map (rho k)).reverse
  | [] => rfl
  | [x] => by simp [revA, rhoRow]
  | x :: y :: rest => by
    rw [revA_cons_cons, List.map_append, List.flatten_append, blocks_revA c (y :: rest)]
    simp [rhoRow]

theorem isChain_imp_mem {α : Type} {R S : α → α → Prop} : ∀ {l : List α}, List.IsChain R l →
    (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) → List.IsChain S l
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.isChain_singleton a
  | a :: b :: l, h, himp => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨himp a (by simp) b (by simp) h.1,
      isChain_imp_mem h.2 (fun x hx y hy => himp x (List.mem_cons_of_mem _ hx) y
        (List.mem_cons_of_mem _ hy))⟩

/-- A row read backwards is a row. -/
theorem doors_rhoRow (hk : 2 ≤ k) {Q : List (List ℕ)} (hw : ∀ w ∈ Q, PermW k w)
    (h : List.IsChain (WLink k 2) Q) : List.IsChain (WLink k 2) (rhoRow k Q) := by
  unfold rhoRow
  rw [List.isChain_reverse, List.isChain_map]
  exact isChain_imp_mem h (fun a ha b hb hab =>
    rho_wlink (by omega) hk (hw a ha).2.1 (hw b hb).2.1 hab)

/-- The links of the reversed list. -/
theorem links_revA (hk : 4 ≤ k) (c : ℕ) : ∀ L : List TRow, IsSeq k L →
    List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
      LinkK k y.1 (x.2.getLast hx) (y.2.head hy)) (revA k c L)
  | [], _ => List.IsChain.nil
  | [x], _ => List.isChain_singleton _
  | x :: y :: rest, h => by
    have htail : IsSeq k (y :: rest) := h.infix ⟨[x], [], by simp⟩
    obtain ⟨T, c', hT⟩ := revA_last (k := k) c y rest
    rw [revA_cons_cons, List.isChain_append]
    refine ⟨links_revA hk c (y :: rest) htail, List.isChain_singleton _, ?_⟩
    intro a ha b hb
    rw [hT] at ha
    simp only [List.getLast?_append, List.getLast?_singleton, Option.mem_def, Option.some_or,
      Option.some.injEq] at ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst ha
    subst hb
    intro ha hb
    have hxne : x.2 ≠ [] := h.pieces_ne x (by simp)
    have hyne : y.2 ≠ [] := h.pieces_ne y (by simp)
    have hlink : LinkK k y.1 (x.2.getLast hxne) (y.2.head hyne) :=
      (List.isChain_cons_cons.mp h.links).1 hxne hyne
    have hu : (x.2.getLast hxne).length = k :=
      (h.words x (by simp) _ (List.getLast_mem hxne)).2.1
    have hv : (y.2.head hyne).length = k :=
      (h.words y (by simp) _ (List.head_mem hyne)).2.1
    have e1 : (rhoRow k y.2).getLast ha = rho k (y.2.head hyne) := by
      simp only [rhoRow, List.getLast_reverse, List.head_map]
    have e2 : (rhoRow k x.2).head hb = rho k (x.2.getLast hxne) := by
      simp only [rhoRow, List.head_reverse, List.getLast_map]
    show LinkK k y.1 ((rhoRow k y.2).getLast ha) ((rhoRow k x.2).head hb)
    rw [e1, e2]
    exact ⟨fun h0 => rho_wlink (by omega) (by omega) hu hv (hlink.1 h0),
      fun h1 => rho_wlink (by omega) (by omega) hu hv (hlink.2 h1)⟩

/-- **Corollary RV.** A sequence read backwards is a sequence. -/
theorem isSeq_revA (hk : 4 ≤ k) (c : ℕ) {L : List TRow} (h : IsSeq k L) :
    IsSeq k (revA k c L) := by
  refine ⟨?_, ?_, ?_, ?_, links_revA hk c L h, ?_⟩
  · intro z hz w hw
    obtain ⟨x, hx, h1, _⟩ := mem_revA hz
    rw [h1, rhoRow, List.mem_reverse, List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact rho_perm (h.words x hx w0 hw0)
  · intro z hz
    obtain ⟨x, hx, h1, _⟩ := mem_revA hz
    rw [h1]
    intro h0
    have := length_rhoRow (k := k) x.2
    rw [h0] at this
    exact h.pieces_ne x hx (List.length_eq_zero_iff.mp this.symm)
  · intro z hz
    obtain ⟨x, hx, h1, _⟩ := mem_revA hz
    rw [h1, length_rhoRow]
    exact h.size_le x hx
  · intro z hz
    obtain ⟨x, hx, h1, _⟩ := mem_revA hz
    rw [h1]
    exact doors_rhoRow (by omega) (h.words x hx) (h.doors x hx)
  · rw [blocks_revA, List.pairwise_reverse, List.pairwise_map]
    exact h.classes.imp (fun {a b} hab => rho_rot (fun h' => hab h'.symm))

theorem kinds_revA {c : ℕ} (hc : c ≤ 1) {L : List TRow} (h : ∀ x ∈ L, x.1 ≤ 1) :
    ∀ z ∈ revA k c L, z.1 ≤ 1 := by
  intro z hz
  obtain ⟨_, _, _, h2⟩ := mem_revA hz
  rcases h2 with h2 | ⟨y, hy, h2⟩
  · rw [h2]
    exact hc
  · rw [h2]
    exact h y hy

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.rho_wlink
#print axioms SuperpermLowerBounds.KS.isSeq_revA
