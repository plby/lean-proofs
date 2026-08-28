import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Scalar coordinates for a nonzero differential

A nonzero differential has a nonzero scalar component. A surjective scalar
linear map can be completed to a continuous linear coordinate equivalence.
These are the source and target coordinate inputs for the nonzero-rank
step in Sard's theorem.
-/

open scoped ContDiff
open Module

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_surjective_scalarComponent (D : E →L[ℝ] F) (hD : D ≠ 0) :
    ∃ ℓ : F →L[ℝ] ℝ, Function.Surjective ℓ ∧ Function.Surjective (ℓ.comp D) := by
  have hv : ∃ v : E, D v ≠ 0 := by
    by_contra! h
    apply hD
    exact ContinuousLinearMap.ext h
  obtain ⟨v, hv⟩ := hv
  obtain ⟨ℓ, _, hℓ⟩ := exists_dual_vector ℝ (D v) (norm_ne_zero_iff.mpr hv)
  have hsurj : Function.Surjective (ℓ.comp D) := by
    apply LinearMap.surjective (f := (ℓ.comp D).toLinearMap)
    intro h
    have hv0 : ℓ (D v) = 0 := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L v) h
    rw [hℓ] at hv0
    exact hv (norm_eq_zero.mp hv0)
  exact ⟨ℓ, Function.Surjective.of_comp hsurj, hsurj⟩

theorem exists_scalarCoordinateEquiv [FiniteDimensional ℝ F]
    (ℓ : F →L[ℝ] ℝ) (hℓ : Function.Surjective ℓ) :
    ∃ e : F ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin (finrank ℝ F - 1)),
      ∀ y, (e y).1 = ℓ y := by
  have hd : 1 ≤ finrank ℝ F := by
    simpa using LinearMap.finrank_le_finrank_of_surjective (f := ℓ.toLinearMap) hℓ
  obtain ⟨R, hR⟩ := ℓ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hℓ)
  have hright : Function.RightInverse R ℓ := by
    intro v
    exact congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L v) hR
  let C : ℓ.ker ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F - 1)) :=
    (LinearEquiv.ofFinrankEq ℓ.ker (EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) (by
      rw [finrank_kernel_of_surjective ℓ hℓ (finrank ℝ F - 1)
        (by simp only [finrank_self]; omega), finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  let e := (ContinuousLinearEquiv.equivOfRightInverse ℓ R hright).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C)
  exact ⟨e, fun _ ↦ rfl⟩

end NoExoticSixSphere.Sard
