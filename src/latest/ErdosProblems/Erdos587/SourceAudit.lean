import ErdosProblems.Erdos587.CorrectedWeyl

namespace Erdos587

/-- The count used in Nguyen--Vu Section 6 cannot have main term
`X / (d*q)` with a uniformly bounded additive error unless the relevant
coprimality condition is imposed. This counterexample uses a nonzero residue
and the fixed parameters `d = 2`, `q = 4`, `r = 2`.

The valid replacement in `NVDevelopment` uses `lcm d q`, retaining the gcd
obstruction. -/
theorem divisorResidueCount_no_uniform_product_modulus_error (K : ℕ) :
    ∃ X : ℕ, X / (2 * 4) + K < divisorResidueCount 2 4 2 X := by
  classical
  let X := 8 * (K + 1)
  let s := (Finset.range (2 * (K + 1))).image fun j ↦ 4 * j + 2
  have hinj : Function.Injective (fun j : ℕ ↦ 4 * j + 2) := by
    intro x y h
    dsimp only at h
    omega
  have hcard : s.card = 2 * (K + 1) := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : s ⊆ (Finset.Icc 1 X).filter fun v ↦ 2 ∣ v ∧ v % 4 = 2 := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hj' := Finset.mem_range.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
    · dsimp only [X]
      omega
    · constructor
      · exact ⟨2 * j + 1, by ring⟩
      · omega
  have hlower : 2 * (K + 1) ≤ divisorResidueCount 2 4 2 X := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  refine ⟨X, ?_⟩
  have hquot : X / (2 * 4) = K + 1 := by simp [X]
  omega

end Erdos587
