import ErdosProblems.Erdos69.FiniteExpectation

/-!
# Finite moment comparison

A uniform error for each joint product gives a moment error controlled by
the full absolute coefficient mass. In particular there is no suppressed
dependence on the number of shifts.
-/

open scoped BigOperators

namespace Erdos69.Elementary

namespace FiniteLaw

variable {Ω Ω' ι : Type*} [Fintype Ω] [Fintype Ω'] [Fintype ι]

theorem mean_power_sum (μ : FiniteLaw Ω) (c : ι → ℝ) (X : ι → Ω → ℝ) (m : ℕ) :
    μ.mean (fun x ↦ (∑ i, c i * X i x) ^ m) =
      ∑ k : Fin m → ι, (∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [μ.mean_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact μ.mean_const_mul _ _

/-- Quantitative comparison of the `m`-th moments, from uniform joint-product errors. -/
theorem moment_error_le (μ : FiniteLaw Ω) (ν : FiniteLaw Ω')
    (c : ι → ℝ) (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ) (m : ℕ) (δ : ℝ)
    (hjoint : ∀ k : Fin m → ι,
      |μ.mean (fun x ↦ ∏ j, X (k j) x) - ν.mean (fun x ↦ ∏ j, Y (k j) x)| ≤ δ) :
    |μ.mean (fun x ↦ (∑ i, c i * X i x) ^ m) -
      ν.mean (fun x ↦ (∑ i, c i * Y i x) ^ m)| ≤
        δ * (∑ i, |c i|) ^ m := by
  rw [mean_power_sum, mean_power_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin m → ι,
        ((∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) -
          (∏ j, c (k j)) * ν.mean (fun x ↦ ∏ j, Y (k j) x))| ≤
        ∑ k : Fin m → ι,
          |(∏ j, c (k j)) * μ.mean (fun x ↦ ∏ j, X (k j) x) -
            (∏ j, c (k j)) * ν.mean (fun x ↦ ∏ j, Y (k j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin m → ι, |∏ j, c (k j)| * δ := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hjoint k) (abs_nonneg _)
    _ = δ * (∑ i, |c i|) ^ m := by
      rw [← Finset.sum_mul, Fintype.sum_pow]
      simp only [Finset.abs_prod]
      ring

end FiniteLaw

end Erdos69.Elementary
