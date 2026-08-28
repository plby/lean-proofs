import Wikipedia.NoExoticSixSphere.NegativeBilinearEquiv
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Abel

/-!
# Local coordinates for the derivative in a negative linear family

Restriction of the derivative to a negative Hessian family is a submersion.
The negative bilinear form supplies an explicit right inverse of its derivative,
and therefore a complementary linear projection. The inverse-function theorem
gives actual smooth local coordinates consisting of the partial derivative and
that projection.
-/

open Set
open scoped ContDiff Manifold

namespace NoExoticSixSphere.PartialGradientCoordinates

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def restrict (L : D →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] D →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ D E ℝ).flip L

noncomputable def gradient (f : E → ℝ) (L : D →L[ℝ] E) (z : E) : D →L[ℝ] ℝ :=
  restrict L (fderiv ℝ f z)

theorem gradient_apply (f : E → ℝ) (L : D →L[ℝ] E) (z : E) (w : D) :
    gradient f L z w = fderiv ℝ f z (L w) := rfl

noncomputable def derivative (f : E → ℝ) (L : D →L[ℝ] E) : E →L[ℝ] D →L[ℝ] ℝ :=
  (restrict L).comp (fderiv ℝ (fderiv ℝ f) 0)

theorem derivative_apply (f : E → ℝ) (L : D →L[ℝ] E) (z : E) (w : D) :
    derivative f L z w = fderiv ℝ (fderiv ℝ f) 0 z (L w) := rfl

theorem hasFDerivAt_gradient (f : E → ℝ) (L : D →L[ℝ] E) (hf : ContDiffAt ℝ 2 f 0) :
    HasFDerivAt (gradient f L) (derivative f L) 0 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  exact (restrict L).hasFDerivAt.comp 0 (hd.differentiableAt one_ne_zero).hasFDerivAt

theorem contDiffOn_gradient (f : E → ℝ) (L : D →L[ℝ] E) (U : Set E)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (gradient f L) U := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf |>.2
  exact (restrict L).contDiff.comp_contDiffOn hd

noncomputable def restrictedHessian (f : E → ℝ) (L : D →L[ℝ] E) : D →L[ℝ] D →L[ℝ] ℝ :=
  (derivative f L).comp L

variable [FiniteDimensional ℝ D]

noncomputable def rightInverse (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) :
    (D →L[ℝ] ℝ) →L[ℝ] E :=
  L.comp (NegativeBilinearEquiv.toDualEquiv (restrictedHessian f L) hneg).symm.toContinuousLinearMap

theorem rightInverse_spec (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) :
    Function.RightInverse (rightInverse f L hneg) (derivative f L) := by
  intro ψ
  exact (NegativeBilinearEquiv.toDualEquiv (restrictedHessian f L) hneg).apply_symm_apply ψ

noncomputable def projection (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) :
    E →L[ℝ] (derivative f L).ker :=
  (derivative f L).projKerOfRightInverse (rightInverse f L hneg) (rightInverse_spec f L hneg)

theorem projection_apply_family (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) (w : D) :
    projection f L hneg (L w) = 0 := by
  have hh : rightInverse f L hneg (restrictedHessian f L w) = L w := by
    change L ((NegativeBilinearEquiv.toDualEquiv (restrictedHessian f L) hneg).symm
      (NegativeBilinearEquiv.toDualEquiv (restrictedHessian f L) hneg w)) = L w
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [← hh]
  exact ContinuousLinearMap.projKerOfRightInverse_comp_inv _ _ _ _

theorem projection_add_family (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) (z : E) (w : D) :
    projection f L hneg (z + L w) = projection f L hneg z := by
  rw [map_add, projection_apply_family, add_zero]

theorem projection_eq_iff (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) (z z' : E) :
    projection f L hneg z = projection f L hneg z' ↔ ∃ w : D, z' = z + L w := by
  constructor
  · intro h
    have hp : projection f L hneg (z' - z) = 0 := by rw [map_sub, ← h, sub_self]
    have he := congrArg Subtype.val hp
    change z' - z - rightInverse f L hneg (derivative f L (z' - z)) = 0 at he
    have hs := sub_eq_zero.mp he
    refine ⟨(NegativeBilinearEquiv.toDualEquiv (restrictedHessian f L) hneg).symm
      (derivative f L (z' - z)), ?_⟩
    change z' = z + rightInverse f L hneg (derivative f L (z' - z))
    rw [← hs]
    abel
  · rintro ⟨w, rfl⟩
    exact (projection_add_family f L hneg z w).symm

noncomputable def linearCoordinates (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0) :
    E ≃L[ℝ] (D →L[ℝ] ℝ) × (derivative f L).ker :=
  ContinuousLinearEquiv.equivOfRightInverse (derivative f L) (rightInverse f L hneg)
    (rightInverse_spec f L hneg)

noncomputable def coordinates (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0)
    (z : E) : (D →L[ℝ] ℝ) × (derivative f L).ker :=
  (gradient f L z, projection f L hneg z)

theorem coordinates_zero (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0)
    (hcrit : fderiv ℝ f 0 = 0) : coordinates f L hneg 0 = 0 := by
  simp [coordinates, gradient, hcrit]

theorem hasFDerivAt_coordinates (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0)
    (hf : ContDiffAt ℝ 2 f 0) :
    HasFDerivAt (coordinates f L hneg) (linearCoordinates f L hneg).toContinuousLinearMap 0 := by
  exact (hasFDerivAt_gradient f L hf).prodMk (projection f L hneg).hasFDerivAt

theorem contDiffOn_coordinates (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (coordinates f L hneg) U :=
  (contDiffOn_gradient f L U hU hf).prodMk (projection f L hneg).contDiff.contDiffOn

variable [CompleteSpace E]

theorem exists_localCoordinates (f : E → ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → fderiv ℝ (fderiv ℝ f) 0 (L w) (L w) < 0)
    (U : Set E) (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, (D →L[ℝ] ℝ) × (derivative f L).ker)
        E ((D →L[ℝ] ℝ) × (derivative f L).ker) ∞,
      (0 : E) ∈ Φ.source ∧ Φ.source ⊆ U ∧
        (Φ : E → (D →L[ℝ] ℝ) × (derivative f L).ker) = coordinates f L hneg := by
  have hc : ContDiffAt ℝ 2 f 0 :=
    (hf.contDiffAt (hU.mem_nhds hzero)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hi : (fderiv ℝ (coordinates f L hneg) 0).IsInvertible :=
    ⟨linearCoordinates f L hneg, (hasFDerivAt_coordinates f L hneg hc).fderiv.symm⟩
  exact exists_partialDiffeomorph_of_contDiffOn hU hzero
    (contDiffOn_coordinates f L hneg U hU hf) hi

omit [CompleteSpace E] [FiniteDimensional ℝ D] in
theorem gradient_zero_iff_inverse_zero_slice (f : E → ℝ) (L : D →L[ℝ] E)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, (D →L[ℝ] ℝ) × (derivative f L).ker)
      E ((D →L[ℝ] ℝ) × (derivative f L).ker) ∞)
    (hfst : ∀ z, (Φ z).1 = gradient f L z)
    (z : E) (hz : z ∈ Φ.source) :
    gradient f L z = 0 ↔ ∃ y : (derivative f L).ker,
      (0, y) ∈ Φ.target ∧ Φ.symm (0, y) = z := by
  constructor
  · intro hg
    have he : Φ z = (0, (Φ z).2) := by
      apply Prod.ext
      · rw [hfst]
        exact hg
      · rfl
    refine ⟨(Φ z).2, ?_, ?_⟩
    · rw [← he]
      exact Φ.map_source' hz
    · rw [← he]
      exact Φ.left_inv' hz
  · rintro ⟨y, hy, he⟩
    have hh := congrArg Prod.fst (Φ.right_inv' hy)
    change (Φ (Φ.symm (0, y))).1 = 0 at hh
    rw [he, hfst] at hh
    exact hh

end NoExoticSixSphere.PartialGradientCoordinates
