import SuperpermutationUpperBound1771.Certificate.Cert
import Challenge

/-!
# A superpermutation on 13 symbols of length at most 6,747,849,960

The statement is in the vocabulary of `Challenge.lean` (`SuperpermutationBounds.HasWord`).
The word is the one completion of the selection on 12 symbols that `Hybrid.lean` builds from
the certificate `Certificate.cert`, joined by 7,875 connector cycles.  The bound is

  F3(13) + 1,780,800 + 10 · 7,875 + 6 · 7,875 + 3 · 1,320,

the finite formula of the construction with `m = 11`, `a = 8` and `c = 7,875`.
-/

namespace SuperpermutationUpperBound1771

open SuperpermutationUpperBound

/-- There is a superpermutation on 13 symbols with at most 6,747,849,960 letters. -/
theorem word_thirteen : SuperpermutationBounds.HasWord 13 6747849960 := by
  obtain ⟨w, hw, hl⟩ := Certificate.cert.word13
  refine ⟨w, ?_, hl⟩
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := hw p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

end SuperpermutationUpperBound1771

#print axioms SuperpermutationUpperBound1771.word_thirteen
#print axioms SuperpermutationUpperBound1771.Cert.word13
#print axioms SuperpermutationUpperBound1771.Certificate.cert
