import ErdosProblems.Erdos421.AdditiveKernelScale
import ErdosProblems.Erdos421.LogarithmicRoughWindows

/-! # Uniform stability of finite additive windows -/

namespace Erdos421

theorem finite_additive_window_scale (S : Finset ℕ) (a : ℕ → ℂ) {A C Y Z η x : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : ∀ n ∈ S, ‖a n‖ ≤ A)
    (hnorm : ∀ t : ℝ, ‖oneSidedSchwartzWindow t‖ ≤ C)
    (hlip : ∀ s t : ℝ,
      ‖oneSidedSchwartzWindow s - oneSidedSchwartzWindow t‖ ≤ C * |s - t|)
    (hY : 0 < Y) (hYZ : Y ≤ Z) (hZη : Z ≤ (1 + η) * Y) (hη : 0 ≤ η)
    (hZ1 : 1 ≤ Z) (hx : 0 ≤ x) :
    ‖(∑ n ∈ S, a n * additiveIntegerWeight Y x n) -
      ∑ n ∈ S, a n * additiveIntegerWeight Z x n‖ ≤ 4 * C * A * η := by
  classical
  let T := S.filter (fun n : ℕ ↦ x < (n : ℝ) ∧ (n : ℝ) ≤ x + Z)
  have hZ : 0 < Z := hY.trans_le hYZ
  have hsum : (∑ n ∈ T, a n * (additiveIntegerWeight Y x n - additiveIntegerWeight Z x n)) =
      ∑ n ∈ S, a n * (additiveIntegerWeight Y x n - additiveIntegerWeight Z x n) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnT
    have hzero : additiveIntegerWeight Y x n - additiveIntegerWeight Z x n = 0 := by
      by_contra hne
      exact hnT (Finset.mem_filter.mpr ⟨hn, additive_weight_scale_support hY hYZ n hne⟩)
    rw [hzero, mul_zero]
  have hcard : (T.card : ℝ) ≤ Z + 1 := by
    have hb := finite_nat_interval_card_le T hx (by linarith : x ≤ x + Z)
      (fun n hn ↦ (Finset.mem_filter.mp hn).2)
    linarith
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ T, ‖a n * (additiveIntegerWeight Y x n - additiveIntegerWeight Z x n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ T, A * (2 * C * η / Z) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (ha n (Finset.mem_filter.mp hn).1)
        (additive_weight_scale_difference hC hnorm hlip hY hYZ hZη hη n) (norm_nonneg _) hA
    _ = T.card * (A * (2 * C * η / Z)) := by simp
    _ ≤ (Z + 1) * (A * (2 * C * η / Z)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((Z + 1) / Z) * (2 * C * A * η) := by ring
    _ ≤ 2 * (2 * C * A * η) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (div_le_iff₀ hZ).mpr (by linarith)
    _ = _ := by ring

theorem exists_additiveRoughWindow_scale_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B z : ℕ, ∀ Y Z η x : ℝ,
      0 < Y → Y ≤ Z → Z ≤ (1 + η) * Y → 0 ≤ η → 1 ≤ Z → 0 ≤ x →
      |additiveRoughWindow B z Y x - additiveRoughWindow B z Z x| ≤ K * η := by
  obtain ⟨C, hC, hnorm, hlip⟩ := exists_schwartz_uniform_lipschitz oneSidedSchwartzWindow
  refine ⟨4 * C, by positivity, ?_⟩
  intro B z Y Z η x hY hYZ hZη hη hZ1 hx
  have hcoef : ∀ n ∈ Finset.Icc 1 B, ‖(roughIndicator n z : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_real, Real.norm_eq_abs, roughIndicator]
    split_ifs <;> norm_num
  have hb := finite_additive_window_scale (Finset.Icc 1 B) (fun n ↦ (roughIndicator n z : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1) hC.le hcoef hnorm hlip hY hYZ hZη hη hZ1 hx
  have hre := Complex.abs_re_le_norm
    ((∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * additiveIntegerWeight Y x n) -
      ∑ n ∈ Finset.Icc 1 B, (roughIndicator n z : ℂ) * additiveIntegerWeight Z x n)
  rw [Complex.sub_re, additiveRoughWindow_complex, additiveRoughWindow_complex] at hre
  simpa only [mul_one] using hre.trans hb

end Erdos421
