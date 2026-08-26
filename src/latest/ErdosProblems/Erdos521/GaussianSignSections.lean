/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
One-dimensional sections of the Gaussian sign-change event.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianIntervals

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem standardGaussian_reflected_interval (t : ℝ) :
    gaussianReal 0 1 (Set.Ioo (-t) 0) = gaussianReal 0 1 (Set.Ioo 0 t) := by
  have heq : Set.Ioo (-t) 0 = (fun x : ℝ ↦ -x) ⁻¹' Set.Ioo 0 t := by
    ext x
    simp only [Set.mem_Ioo, Set.mem_preimage]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq, ← Measure.map_apply (by fun_prop) measurableSet_Ioo, gaussianReal_map_neg, neg_zero]

theorem sign_shift_set_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    {u : ℝ | u * (u + c) < 0} = Set.Ioo (-c) 0 := by
  ext u
  change u * (u + c) < 0 ↔ -c < u ∧ u < 0
  constructor
  · intro hu
    rcases mul_neg_iff.mp hu with h | h <;> constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    exact mul_neg_of_neg_of_pos h₂ (by linarith)

theorem sign_shift_set_of_nonpos {c : ℝ} (hc : c ≤ 0) :
    {u : ℝ | u * (u + c) < 0} = Set.Ioo 0 (-c) := by
  ext u
  change u * (u + c) < 0 ↔ 0 < u ∧ u < -c
  constructor
  · intro hu
    rcases mul_neg_iff.mp hu with h | h <;> constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    exact mul_neg_of_pos_of_neg h₁ (by linarith)

theorem standardGaussian_sign_section {α : ℝ} (hα : 0 ≤ α) (y : ℝ) :
    (gaussianReal 0 1).real {u : ℝ | u * (u + α * y) < 0} = standardGaussianInterval (α * |y|) := by
  by_cases hy : 0 ≤ y
  · have hc : 0 ≤ α * y := mul_nonneg hα hy
    rw [sign_shift_set_of_nonneg hc, abs_of_nonneg hy, standardGaussianInterval_eq_measure hc]
    exact congrArg ENNReal.toReal (standardGaussian_reflected_interval (α * y))
  · have hy₀ : y ≤ 0 := le_of_not_ge hy
    have hc : α * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hy₀
    rw [sign_shift_set_of_nonpos hc, ← standardGaussianInterval_eq_measure (neg_nonneg.mpr hc),
      abs_of_nonpos hy₀]
    congr 1
    ring

end Erdos521
