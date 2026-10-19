theorem blockData_walks : ∀ wg ∈ blockData.items, BasedOn (alphabet 2) 9 wg.1 ∧ ClosedTrail wg.1 ∧
    0 < 12 / wg.2 ∧ (12 : Int) ∣ ((12 / wg.2 : Nat) : Int) * signedExcess wg.1 ∧
    ((List.range wg.2).flatMap (orbitPorts wg.1 (12 / wg.2))).Perm (List.range 12) := by
  unfold BasedOn ClosedTrail CyclicallyCompatible Row.Compatible
  decide +kernel

theorem blockData_dloops : ∀ e ∈ blockData.dloops, e.Perm (alphabet 2) := by decide +kernel

theorem blockData_cover : coveredB blockData.walks blockData.dloops (above3 alph10) blockData.ptrs = true := by
  decide +kernel

theorem blockData_rest : blockData.walks.flatten.length = 880 ∧
    (blockData.walks.flatten.map Row.charge).sum = 370 ∧ blockData.dloops.length = 440 ∧
    CircleFamilyValid 13 blockData.cyc ∧ (∀ c ∈ blockData.cyc, ∀ a ∈ c, a < 16 ∧ a ≠ 9) ∧
    blockData.cyc.length = 26 := by
  unfold CircleFamilyValid
  decide +kernel

theorem blockData_ok : BlockOK blockData :=
  ⟨blockData_walks, blockData_dloops, blockData_cover, blockData_rest⟩

#print axioms blockData_ok
