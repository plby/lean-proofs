import Wikipedia.SmoothSixDPoincare.RegularValues

/-!
# Equal-dimensional Sard on a prescribed subset

Only differentiability at points of the supplied subset is required. This
form is suitable for chart coordinate functions, which need not be smooth
away from their chart domains.
-/

noncomputable section

open Set Function MeasureTheory MeasureTheory.Measure

namespace Wikipedia.SmoothSixDPoincare.RegularValues

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

/-- The exceptional values in a restricted domain form a Haar-null set. -/
theorem exists_null_exceptional_values_on {f : E → E} {s : Set E}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    ∃ T : Set E, μ T = 0 ∧ ∀ x ∈ s, f x ∉ T → Bijective (fderiv ℝ f x) := by
  let B : Set E := {x | x ∈ s ∧ (fderiv ℝ f x).det = 0}
  have hzero : μ (f '' B) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  refine ⟨f '' B, hzero, ?_⟩
  intro x hx hfx
  apply (bijective_iff_det_ne_zero _).mpr
  intro hdet
  exact hfx ⟨x, ⟨hx, hdet⟩, rfl⟩

end Wikipedia.SmoothSixDPoincare.RegularValues
