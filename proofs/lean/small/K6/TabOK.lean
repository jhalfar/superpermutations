import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Rotate
import LowerBounds.SSound
import K6.Engine

/-!
# The tables of the search on 6 symbols mean what they say

The coding `enc w` is the index of the word `w` in the list `allW` of the 720 words of `TP`.  Every
fact below is checked against the words by `decide +kernel` (the kernel computes the tables and the
words) and then carried to all permutation words:

* `enc_pw`, `pw_enc`: `enc` and `pw` are inverse on permutation words;
* `ci_eq_iff`: two permutation words have the same class index iff they are rotations of each other;
* `nx_enc`: `nx` is the door of the exit (`DoorEq`);
* `s3_enc`: a word of another class that the exit of `u` overlaps in 3 letters is one of `s3 (enc u) j`.
-/

namespace K6

open SuperpermLowerBounds SuperpermLowerBounds.S

/-- The 720 words of the table. -/
def allW : List (List ℕ) := (List.range 720).map pw

/-- The index of a word in the table. -/
def enc (w : List ℕ) : ℕ := allW.idxOf w

/-! ### Checks by the kernel -/

set_option maxRecDepth 100000 in
theorem chk_idx : (List.range 720).all (fun i => allW.idxOf (pw i) == i) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_all : (List.permutations' [1, 2, 3, 4, 5, 6]).all (fun w => allW.contains w) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_rot : (List.range 720).all (fun i =>
    (pw i).rotate (rot i) == pw (rep (ci i)) && rep (ci i) < 720) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_ci_rot : (List.range 720).all (fun i => ci (enc ((pw i).rotate 1)) == ci i) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_nx : (List.range 720).all (fun i =>
    pw (nx i) == doorW ((pw i).rotate 5) && nx i < 720) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_s3 : (List.range 720).all (fun i =>
    (((pw i).rotate 5).take 3).permutations'.all (fun t =>
      (List.range 6).any (fun s => (((pw i).rotate 5).drop 3 ++ t).rotate s == pw i) ||
      (List.range 5).any (fun j => pw (s3 i j) == ((pw i).rotate 5).drop 3 ++ t && s3 i j < 720)))
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chk_id : pw 0 = [1, 2, 3, 4, 5, 6] := by decide +kernel

/-! ### Consequences -/

theorem all_range {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) {i : ℕ} (hi : i < n) :
    f i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem enc_pw {i : ℕ} (hi : i < 720) : enc (pw i) = i := by
  have := all_range chk_idx hi
  simpa [enc] using this

theorem permW_perm {w : List ℕ} (hw : PermW 6 w) : w.Perm [1, 2, 3, 4, 5, 6] := by
  rw [List.perm_ext_iff_of_nodup hw.1 (by decide)]
  intro a
  rw [hw.2.2 a]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_allW {w : List ℕ} (hw : PermW 6 w) : w ∈ allW := by
  have hm : w ∈ List.permutations' [1, 2, 3, 4, 5, 6] := List.mem_permutations'.mpr (permW_perm hw)
  have := List.all_eq_true.mp chk_all w hm
  simpa using this

theorem enc_lt {w : List ℕ} (hw : PermW 6 w) : enc w < 720 := by
  have h := List.idxOf_lt_length_of_mem (mem_allW hw)
  simpa [enc, allW] using h

theorem pw_enc {w : List ℕ} (hw : PermW 6 w) : pw (enc w) = w := by
  have h := List.getElem_idxOf (List.idxOf_lt_length_of_mem (mem_allW hw))
  simp only [allW, List.getElem_map, List.getElem_range] at h
  exact h

theorem enc_inj {u v : List ℕ} (hu : PermW 6 u) (hv : PermW 6 v) (h : enc u = enc v) : u = v := by
  rw [← pw_enc hu, ← pw_enc hv, h]

theorem rot_rep {w : List ℕ} (hw : PermW 6 w) : w.rotate (rot (enc w)) = pw (rep (ci (enc w))) := by
  have := all_range chk_rot (enc_lt hw)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rw [← this.1, pw_enc hw]

set_option maxRecDepth 100000 in
theorem chk_perm : (List.range 720).all (fun i => (pw i).isPerm [1, 2, 3, 4, 5, 6]) = true := by
  decide +kernel

theorem permW_of_perm {w : List ℕ} (h : w.Perm [1, 2, 3, 4, 5, 6]) : PermW 6 w := by
  refine ⟨h.nodup_iff.mpr (by decide), h.length_eq, fun a => ?_⟩
  rw [h.mem_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem permW_pw {i : ℕ} (hi : i < 720) : PermW 6 (pw i) := by
  have := all_range chk_perm hi
  exact permW_of_perm (List.isPerm_iff.mp this)

theorem ci_rot1 {w : List ℕ} (hw : PermW 6 w) : ci (enc (w.rotate 1)) = ci (enc w) := by
  have := all_range chk_ci_rot (enc_lt hw)
  simp only [beq_iff_eq] at this
  rw [pw_enc hw] at this
  exact this

theorem ci_rotate {w : List ℕ} (hw : PermW 6 w) : ∀ n, ci (enc (w.rotate n)) = ci (enc w)
  | 0 => by rw [List.rotate_zero]
  | n + 1 => by
    rw [← List.rotate_rotate, ci_rot1 (hw.rotate n), ci_rotate hw n]

/-- **Class indices are the rotation classes.** -/
theorem ci_eq_iff {u v : List ℕ} (hu : PermW 6 u) (hv : PermW 6 v) :
    ci (enc u) = ci (enc v) ↔ u ~r v := by
  constructor
  · intro h
    have e : u.rotate (rot (enc u)) = v.rotate (rot (enc v)) := by
      rw [rot_rep hu, rot_rep hv, h]
    have h1 : u ~r u.rotate (rot (enc u)) := ⟨_, rfl⟩
    have h2 : v ~r v.rotate (rot (enc v)) := ⟨_, rfl⟩
    rw [e] at h1
    exact h1.trans h2.symm
  · rintro ⟨n, rfl⟩
    exact (ci_rotate hu n).symm

/-- **`nx` is the door of the exit.** -/
theorem nx_enc {a b : List ℕ} (ha : PermW 6 a) (h : DoorEq 6 a b) : nx (enc a) = enc b := by
  have := all_range chk_nx (enc_lt ha)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rw [pw_enc ha] at this
  unfold DoorEq at h
  rw [h, show 6 - 1 = 5 from rfl, ← this.1, enc_pw this.2]

/-- The words that the exit of `u` overlaps in 3 letters. -/
theorem wlink3_shape {u v : List ℕ} (hu : PermW 6 u) (hv : PermW 6 v) (h : WLink 6 3 u v) :
    ∃ t ∈ ((u.rotate 5).take 3).permutations', v = (u.rotate 5).drop 3 ++ t := by
  unfold WLink at h
  simp only [show 6 - 1 = 5 from rfl, show 6 - 3 = 3 from rfl] at h
  refine ⟨v.drop 3, ?_, ?_⟩
  · rw [List.mem_permutations']
    have hpv := permW_perm hv
    have hpu := (List.rotate_perm u 5).trans (permW_perm hu)
    have e1 : v = (u.rotate 5).drop 3 ++ v.drop 3 := by
      conv_lhs => rw [← List.take_append_drop 3 v]
      rw [h]
    have e2 : (u.rotate 5).take 3 ++ (u.rotate 5).drop 3 = u.rotate 5 := List.take_append_drop 3 _
    have p1 : List.Perm ((u.rotate 5).drop 3 ++ v.drop 3) ((u.rotate 5).drop 3 ++ (u.rotate 5).take 3) := by
      have p2 : List.Perm (u.rotate 5) ((u.rotate 5).drop 3 ++ (u.rotate 5).take 3) := by
        conv_lhs => rw [← e2]
        exact List.perm_append_comm
      rw [← e1]
      exact hpv.trans (hpu.symm.trans p2)
    exact (List.perm_append_left_iff _).mp p1
  · conv_lhs => rw [← List.take_append_drop 3 v]
    rw [h]

/-- **`s3` lists the weight-3 successors of another class.** -/
theorem s3_enc {u v : List ℕ} (hu : PermW 6 u) (hv : PermW 6 v) (h : WLink 6 3 u v)
    (hn : ¬ u ~r v) : ∃ j, j < 5 ∧ s3 (enc u) j = enc v := by
  obtain ⟨t, ht, rfl⟩ := wlink3_shape hu hv h
  have := all_range chk_s3 (enc_lt hu)
  rw [pw_enc hu] at this
  have h2 := List.all_eq_true.mp this t ht
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h2
  rcases h2 with ⟨s, _, hs⟩ | ⟨j, hj, hpj, hlt⟩
  · exact absurd ⟨s, hs⟩ (fun h' => hn (List.IsRotated.symm h'))
  · exact ⟨j, hj, by rw [← hpj, enc_pw hlt]⟩

theorem enc_id : enc [1, 2, 3, 4, 5, 6] = 0 := by
  rw [← chk_id, enc_pw (by norm_num)]

end K6
