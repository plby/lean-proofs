/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalized means over a growing finite family with a uniform local limit.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open Filter
open scoped Topology BigOperators

theorem triangular_mean_error_tendsto_zero (S : ℕ → Finset ℕ) (F : ℕ → ℕ → ℝ) (c : ℝ)
    (hcard : ∀ᶠ j : ℕ in atTop, (S j).card ≤ j)
    (hlocal : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, ∀ i ∈ S j, |F j i - c| < η) :
    Tendsto (fun j ↦ ((∑ i ∈ S j, F j i) - (S j).card * c) / (j : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [hcard, hlocal (η / 2) (by positivity), eventually_ge_atTop 1] with j hj hF hj₁
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsum : |(∑ i ∈ S j, F j i) - (S j).card * c| ≤ (j : ℝ) * (η / 2) := by
    calc
      _ = |∑ i ∈ S j, (F j i - c)| := by rw [Finset.sum_sub_distrib]; simp
      _ ≤ ∑ i ∈ S j, |F j i - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S j, η / 2 := Finset.sum_le_sum (fun i hi ↦ (hF i hi).le)
      _ = (S j).card * (η / 2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hj₀]
  have h := div_le_div_of_nonneg_right hsum hj₀.le
  rw [mul_div_cancel_left₀ _ hj₀.ne'] at h
  exact h.trans_lt (by linarith)

theorem triangular_mean_limit (S : ℕ → Finset ℕ) (F : ℕ → ℕ → ℝ) (a c : ℝ)
    (hcard : ∀ᶠ j : ℕ in atTop, (S j).card ≤ j)
    (hratio : Tendsto (fun j ↦ ((S j).card : ℝ) / (j : ℝ)) atTop (𝓝 a))
    (hlocal : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, ∀ i ∈ S j, |F j i - c| < η) :
    Tendsto (fun j ↦ (∑ i ∈ S j, F j i) / (j : ℝ)) atTop (𝓝 (a * c)) := by
  have h := (triangular_mean_error_tendsto_zero S F c hcard hlocal).add (hratio.mul_const c)
  simp only [zero_add] at h
  convert h using 1
  funext j
  ring

end Erdos521
