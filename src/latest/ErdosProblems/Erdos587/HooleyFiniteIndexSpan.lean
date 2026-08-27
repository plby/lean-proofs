import ErdosProblems.Erdos587.GAPImageSums
import Mathlib.GroupTheory.IndexNSmul

/-! # Finite coordinate-lattice index implies full real span -/

open scoped BigOperators

namespace Erdos587.CFP

open GeneralizedAP

theorem delta_real_span_of_finiteIndex_generated {α : Type*} {d : ℕ}
    (φ : α → Fin d → ℤ) (A : Finset α)
    (hfinite : (generatedSubgroup φ A).FiniteIndex) :
    Submodule.span ℝ ((intCastVec ∘ φ) '' (A : Set α)) = ⊤ := by
  by_contra hspan
  obtain ⟨ℓ, hℓ, hker⟩ :=
    (Submodule.span ℝ ((intCastVec ∘ φ) '' (A : Set α))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  let F : (Fin d → ℤ) →+ ℝ := {
    toFun := fun z => ℓ (intCastVec z)
    map_zero' := by
      change ℓ (intCastVec (0 : Fin d → ℤ)) = 0
      rw [show intCastVec (0 : Fin d → ℤ) = 0 by
        funext i
        norm_num [intCastVec], map_zero]
    map_add' := by
      intro x y
      rw [ConvexProgression.intCastVec_add, map_add]
  }
  have hgen : generatedSubgroup φ A ≤ F.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨a, ha, rfl⟩
    exact hker (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hcast (z : Fin d → ℤ) : ℓ (intCastVec z) = 0 := by
    have hh := hgen ((generatedSubgroup φ A).nsmul_index_mem z)
    change F ((generatedSubgroup φ A).index • z) = 0 at hh
    rw [map_nsmul, nsmul_eq_mul] at hh
    have hindex : ((generatedSubgroup φ A).index : ℝ) ≠ 0 := by
      exact_mod_cast hfinite.index_ne_zero
    exact (mul_eq_zero.mp hh).resolve_left hindex
  apply hℓ
  apply LinearMap.ext
  intro x
  change ℓ x = 0
  rw [show x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) from pi_eq_sum_univ' x, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, show Pi.single i (1 : ℝ) = intCastVec (Pi.single i (1 : ℤ)) by
    ext j
    simp [intCastVec, Pi.single_apply], hcast, smul_zero]

end Erdos587.CFP
