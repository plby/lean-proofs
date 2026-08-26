import ErdosProblems.Erdos1148.CuspVisitCountIntegral

/-! # A bounded visit count controls cusp mass through its exceedance event -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem integral_le_threshold_add_bound_mul_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hf : Integrable f μ) (hbound : ∀ x, f x ≤ b) (hs : MeasurableSet {x | a ≤ f x}) :
    (∫ x, f x ∂μ) ≤ a + b * μ.real {x | a ≤ f x} := by
  classical
  let s : Set X := {x | a ≤ f x}
  have hi : Integrable (s.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have hr : Integrable (fun x => a + b * s.indicator (fun _ : X => (1 : ℝ)) x) μ :=
    (integrable_const a).add (hi.const_mul b)
  have hpoint (x : X) : f x ≤ a + b * s.indicator (fun _ : X => (1 : ℝ)) x := by
    simp only [Set.indicator_apply]
    split_ifs with hx
    · simp only [mul_one]
      linarith [hbound x]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge hx).le
  have hle := integral_mono hf hr hpoint
  have hvalue : (∫ x, a + b * s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = a + b * μ.real s := by
    rw [integral_add (integrable_const a) (hi.const_mul b), integral_const_mul]
    have hsi : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
      simpa only [smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) hs
    rw [hsi]
    simp
  exact hle.trans_eq hvalue

theorem invariant_cusp_mass_le_visit_exceedance (μ : Measure ModularOrbitSpace)
    [IsProbabilityMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ)
    (H : ℝ) (n : ℕ) (hn : 0 < n) {α : ℝ} (hα : 0 ≤ α) :
    μ.real (modularCusp H) ≤ α + μ.real (modularCuspVisitExceedance H n (α * n)) := by
  have hs : MeasurableSet {x | α * (n : ℝ) ≤ modularCuspVisitCount H n x} :=
    measurableSet_modularCuspVisitExceedance H n (α * n)
  have h := integral_le_threshold_add_bound_mul_mass μ (modularCuspVisitCount H n)
    (show 0 ≤ α * (n : ℝ) by positivity) (integrable_modularCuspVisitCount μ H n)
    (modularCuspVisitCount_le H n) hs
  rw [integral_modularCuspVisitCount μ hinv] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (mul_le_mul_iff_right₀ hnR).mp
  change (n : ℝ) * μ.real (modularCusp H) ≤
    (n : ℝ) * (α + μ.real (modularCuspVisitExceedance H n (α * n)))
  change (n : ℝ) * μ.real (modularCusp H) ≤ α * n +
    (n : ℝ) * μ.real (modularCuspVisitExceedance H n (α * n)) at h
  nlinarith

end Erdos1148.DukeArithmetic
