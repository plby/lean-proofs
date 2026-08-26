import ErdosProblems.Erdos421.LogarithmicIntegerWeights
import ErdosProblems.Erdos421.FiniteWindowSupport

/-! # A uniform comparison of finite weighted additive and logarithmic windows -/

namespace Erdos421

theorem finite_integer_kernel_comparison (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) {A C δ x : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ A)
    (hnorm : ∀ t : ℝ, ‖oneSidedSchwartzWindow t‖ ≤ C)
    (hlip : ∀ s t : ℝ,
      ‖oneSidedSchwartzWindow s - oneSidedSchwartzWindow t‖ ≤ C * |s - t|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hx : 0 < x) :
    ‖(∑ n ∈ S, a n * logarithmicIntegerWeight δ (Real.log x) n) -
      ∑ n ∈ S, a n * additiveIntegerWeight (δ * x) x n‖ ≤ 12 * C * A * (δ + x⁻¹) := by
  classical
  let T := S.filter (fun n : ℕ ↦ x < (n : ℝ) ∧ (n : ℝ) ≤ (1 + 2 * δ) * x)
  have hsum : (∑ n ∈ T, a n * (logarithmicIntegerWeight δ (Real.log x) n -
      additiveIntegerWeight (δ * x) x n)) =
      ∑ n ∈ S, a n * (logarithmicIntegerWeight δ (Real.log x) n -
        additiveIntegerWeight (δ * x) x n) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnT
    have hzero : logarithmicIntegerWeight δ (Real.log x) n -
        additiveIntegerWeight (δ * x) x n = 0 := by
      by_contra hne
      exact hnT (Finset.mem_filter.mpr ⟨hn,
        integer_weight_difference_support hδ hδ1 hx (hS n hn) hne⟩)
    rw [hzero, mul_zero]
  have hcard := finite_window_band_card_le S hx.le hδ.le
  change (T.card : ℝ) ≤ 2 * δ * x + 1 at hcard
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ T, ‖a n * (logarithmicIntegerWeight δ (Real.log x) n -
        additiveIntegerWeight (δ * x) x n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ T, A * (6 * C / x) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      rw [norm_mul]
      exact mul_le_mul (ha n hnS)
        (integer_weight_difference_le hC hnorm hlip hδ hδ1 hx (hS n hnS))
        (norm_nonneg _) hA
    _ = T.card * (A * (6 * C / x)) := by simp
    _ ≤ (2 * δ * x + 1) * (A * (6 * C / x)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 12 * C * A * δ + 6 * C * A * x⁻¹ := by field_simp; ring
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC hA) (inv_nonneg.mpr hx.le)]

theorem exists_finite_integer_kernel_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, 0 < n) →
      ∀ A : ℝ, 0 ≤ A → (∀ n ∈ S, ‖a n‖ ≤ A) →
      ∀ δ x : ℝ, 0 < δ → δ ≤ 1 / 2 → 0 < x →
      ‖(∑ n ∈ S, a n * logarithmicIntegerWeight δ (Real.log x) n) -
        ∑ n ∈ S, a n * additiveIntegerWeight (δ * x) x n‖ ≤ K * A * (δ + x⁻¹) := by
  obtain ⟨C, hC, hnorm, hlip⟩ := exists_schwartz_uniform_lipschitz oneSidedSchwartzWindow
  refine ⟨12 * C, by positivity, ?_⟩
  intro S a hS A hA ha δ x hδ hδ1 hx
  exact finite_integer_kernel_comparison S a hS hA hC.le ha hnorm hlip hδ hδ1 hx

end Erdos421
