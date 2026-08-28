import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A negative definite bilinear form identifies a finite space with its dual

The identification is the actual bilinear form, with a continuous linear
inverse. No inner-product structure is imposed on the original norm.
-/

namespace NoExoticSixSphere.NegativeBilinearEquiv

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

theorem bijective (B : D →L[ℝ] D →L[ℝ] ℝ)
    (hneg : ∀ x : D, x ≠ 0 → B x x < 0) : Function.Bijective B := by
  have hi : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).mpr
    intro x hx
    by_contra hn
    have hh := hneg x hn
    simp only [hx, zero_apply, lt_self_iff_false] at hh
  have hdim : Module.finrank ℝ D = Module.finrank ℝ (D →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ D = Module.finrank ℝ (D →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = Module.finrank ℝ (D →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (D →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (D →L[ℝ] ℝ)).finrank_eq
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := B.toLinearMap) hdim).mp hi⟩

noncomputable def toDualEquiv (B : D →L[ℝ] D →L[ℝ] ℝ)
    (hneg : ∀ x : D, x ≠ 0 → B x x < 0) : D ≃L[ℝ] (D →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective B.toLinearMap (bijective B hneg)).toContinuousLinearEquiv

theorem toDualEquiv_apply (B : D →L[ℝ] D →L[ℝ] ℝ)
    (hneg : ∀ x : D, x ≠ 0 → B x x < 0) (x : D) : toDualEquiv B hneg x = B x := rfl

end NoExoticSixSphere.NegativeBilinearEquiv
