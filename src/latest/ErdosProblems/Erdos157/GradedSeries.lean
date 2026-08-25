import ErdosProblems.Erdos157.ScalarSeriesUniqueness
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Regrouping an absolutely convergent series by its natural-number degree. -/

namespace Erdos157.Elementary

variable {ι : Type*}

noncomputable def gradedCoefficient (degree : ι → ℕ) (c : ι → ℂ) (n : ℕ) : ℂ :=
  ∑' i : {i // degree i = n}, c i.1

theorem summable_norm_grade_fiber (degree : ι → ℕ) (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun i => ‖c i‖ * r ^ degree i)) (n : ℕ) :
    Summable (fun i : {i // degree i = n} => ‖c i.1‖) := by
  have h := (hc.subtype (fun i => degree i = n)).div_const (r ^ n)
  apply h.congr
  intro i
  simp only [Function.comp_def, i.2, mul_div_cancel_right₀ _ (pow_ne_zero n hr.ne')]

theorem norm_gradedCoefficient_mul_le (degree : ι → ℕ) (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun i => ‖c i‖ * r ^ degree i)) (n : ℕ) :
    ‖gradedCoefficient degree c n‖ * r ^ n ≤
      ∑' i : {i // degree i = n}, ‖c i.1‖ * r ^ degree i.1 := by
  have h := norm_tsum_le_tsum_norm (summable_norm_grade_fiber degree c r hr hc n)
  calc
    _ ≤ (∑' i : {i // degree i = n}, ‖c i.1‖) * r ^ n :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro i
      rw [i.2]

theorem summable_gradedCoefficient (degree : ι → ℕ) (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun i => ‖c i‖ * r ^ degree i)) :
    Summable (fun n => ‖gradedCoefficient degree c n‖ * r ^ n) := by
  have h := (hc.hasSum.tsum_fiberwise degree).summable
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (norm_gradedCoefficient_mul_le degree c r hr hc)
  exact h

theorem hasSum_gradedCoefficient (degree : ι → ℕ) (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hc : Summable (fun i => ‖c i‖ * r ^ degree i)) (z : ℂ) (hz : ‖z‖ ≤ r) :
    HasSum (fun n => gradedCoefficient degree c n * z ^ n)
      (∑' i, c i * z ^ degree i) := by
  have hs : Summable (fun i => c i * z ^ degree i) := by
    apply hc.of_norm_bounded
    intro i
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)
  have h := hs.hasSum.tsum_fiberwise degree
  apply h.congr_fun
  intro n
  unfold gradedCoefficient
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  rw [i.2]

end Erdos157.Elementary
