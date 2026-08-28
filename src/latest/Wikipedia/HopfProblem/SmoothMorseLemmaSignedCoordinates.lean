import Wikipedia.HopfProblem.SmoothMorseLemmaBilinear
import Mathlib.LinearAlgebra.QuadraticForm.Real

/-!
# Signed coordinates for a nondegenerate real Hessian

The quadratic function is the literal half-Hessian, not an independently
chosen quadratic model. Sylvester's law of inertia supplies linear coordinates;
finite dimensionality makes the coordinates and their inverse continuous.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic form given by the actual half-Hessian. -/
def halfHessianQuadratic (H : Bilinear E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((1 / 2 : ℝ) • H.toLinearMap₁₂)

@[simp] theorem halfHessianQuadratic_apply (H : Bilinear E) (x : E) :
    halfHessianQuadratic H x = (1 / 2 : ℝ) * H x x := rfl

/-- Polarization of a symmetric half-Hessian recovers that same bilinear form. -/
theorem halfHessianQuadratic_associated (H : Bilinear E)
    (hH : ∀ x y, H x y = H y x) :
    QuadraticMap.associated (halfHessianQuadratic H) =
      (1 / 2 : ℝ) • H.toLinearMap₁₂ := by
  apply QuadraticMap.associated_left_inverse ℝ
    (B₁ := (1 / 2 : ℝ) • H.toLinearMap₁₂)
  intro x y
  change (1 / 2 : ℝ) * H x y = (1 / 2 : ℝ) * H y x
  rw [hH]

/-- Injectivity of the actual Hessian makes its quadratic form nondegenerate. -/
theorem halfHessianQuadratic_separatingLeft (H : Bilinear E)
    (hH : ∀ x y, H x y = H y x) (hHinj : Function.Injective H) :
    (QuadraticMap.associated (halfHessianQuadratic H)).SeparatingLeft := by
  rw [halfHessianQuadratic_associated H hH]
  intro x hx
  apply hHinj
  ext y
  have hxy := hx y
  change (1 / 2 : ℝ) * H x y = 0 at hxy
  simpa using (mul_eq_zero.mp hxy).resolve_left (by norm_num)

variable [FiniteDimensional ℝ E]

/-- A nondegenerate real Hessian has genuine continuous signed coordinates. -/
theorem exists_signed_coordinates (H : Bilinear E)
    (hH : ∀ x y, H x y = H y x) (hHbij : Function.Bijective H) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
      ∃ C : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
        ∀ x, (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2 := by
  obtain ⟨w, hw, ⟨C⟩⟩ :=
    (halfHessianQuadratic H).equivalent_one_neg_one_weighted_sum_squared
      (halfHessianQuadratic_separatingLeft H hH hHbij.1)
  refine ⟨w, hw, C.toLinearEquiv.toContinuousLinearEquiv, ?_⟩
  intro x
  change (1 / 2 : ℝ) * H x x = ∑ i, w i * (C x i) ^ 2
  simpa only [QuadraticMap.weightedSumSquares_apply,
    halfHessianQuadratic_apply, smul_eq_mul, pow_two] using (C.map_app x).symm

end Wikipedia.HopfProblem.SmoothMorseLemma
