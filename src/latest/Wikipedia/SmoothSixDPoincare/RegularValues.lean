import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Dense regular values in equal dimensions

This is the analytic input for perturbing the derivative of a local real
function. It uses Mathlib's proved equal-dimensional Sard lemma, not an
assumed general transversality theorem.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure

namespace Wikipedia.SmoothSixDPoincare.RegularValues

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Points where the actual derivative is singular. -/
def singularPoints (f : E → E) : Set E := {x | (fderiv ℝ f x).det = 0}

/-- Values having no singular point in their fiber. -/
def regularValues (f : E → E) : Set E := (f '' singularPoints f)ᶜ

omit [FiniteDimensional ℝ E] in
theorem mem_regularValues_iff (f : E → E) (y : E) :
    y ∈ regularValues f ↔ ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  constructor
  · intro hy x hx hdet
    exact hy ⟨x, hdet, hx⟩
  · intro hy ⟨x, hx, hxy⟩
    exact hy x hxy hx

theorem bijective_iff_det_ne_zero (A : E →L[ℝ] E) :
    Function.Bijective A ↔ A.det ≠ 0 := by
  constructor
  · intro h hdet
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet) (LinearMap.ker_eq_bot.mpr h.1)
  · intro hdet
    have hker : A.toLinearMap.ker = ⊥ := by
      by_contra hn
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
    have hi := LinearMap.ker_eq_bot.mp hker
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem bijective_fderiv_of_mem_regularValues {f : E → E} {y : E}
    (hy : y ∈ regularValues f) {x : E} (hx : f x = y) :
    Function.Bijective (fderiv ℝ f x) := by
  have hdet := (mem_regularValues_iff f y).mp hy x hx
  exact (bijective_iff_det_ne_zero _).mpr hdet

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

/-- Critical values form a null set, with no global injectivity assumption. -/
theorem measure_singularValues_eq_zero {f : E → E} (hf : Differentiable ℝ f) :
    μ (f '' singularPoints f) = 0 :=
  addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)

include μ in
/-- Regular values of a differentiable map between equal-dimensional spaces are dense. -/
theorem dense_regularValues {f : E → E} (hf : Differentiable ℝ f) :
    Dense (regularValues f) := by
  have he : ∀ᵐ y ∂μ, y ∉ f '' singularPoints f := by
    rw [ae_iff]
    have hs : {y : E | ¬ y ∉ f '' singularPoints f} = f '' singularPoints f := by
      ext y
      simp
    rw [hs]
    exact measure_singularValues_eq_zero μ hf
  exact μ.dense_of_ae he

end Wikipedia.SmoothSixDPoincare.RegularValues
