import ErdosProblems.Erdos421.WindowRatioKernels
import ErdosProblems.Erdos421.PositiveDivisorWindows

/-! # Exact arithmetic kernels in logarithmic and additive coordinates -/

namespace Erdos421

noncomputable def logarithmicIntegerWeight (δ y : ℝ) (n : ℕ) : ℂ :=
  ((n : ℝ)⁻¹ : ℝ) • ((δ⁻¹ : ℝ) • oneSidedSchwartzWindow ((y - Real.log n) / δ))

theorem logarithmicIntegerWeight_ratio {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) :
    logarithmicIntegerWeight δ (Real.log x) n =
      ((δ * x)⁻¹ : ℝ) • (((n : ℝ) / x)⁻¹ •
        oneSidedSchwartzWindow ((-Real.log ((n : ℝ) / x)) / δ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : (Real.log x - Real.log n) / δ = (-Real.log ((n : ℝ) / x)) / δ := by
    rw [Real.log_div hnp.ne' hx.ne']
    ring
  rw [logarithmicIntegerWeight, harg, smul_smul, smul_smul]
  congr 1
  field_simp

theorem additiveIntegerWeight_ratio {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) (n : ℕ) :
    additiveIntegerWeight (δ * x) x n =
      ((δ * x)⁻¹ : ℝ) • oneSidedSchwartzWindow ((1 - (n : ℝ) / x) / δ) := by
  unfold additiveIntegerWeight
  congr 2
  field_simp

theorem integer_weight_difference_le {C δ x : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ t : ℝ, ‖oneSidedSchwartzWindow t‖ ≤ C)
    (hlip : ∀ s t : ℝ,
      ‖oneSidedSchwartzWindow s - oneSidedSchwartzWindow t‖ ≤ C * |s - t|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    ‖logarithmicIntegerWeight δ (Real.log x) n - additiveIntegerWeight (δ * x) x n‖ ≤
      6 * C / x := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logarithmicIntegerWeight_ratio hδ hx hn, additiveIntegerWeight_ratio hδ hx,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hδ hx))]
  calc
    _ ≤ (δ * x)⁻¹ * (6 * C * δ) :=
      mul_le_mul_of_nonneg_left (oneSided_ratio_kernel_difference hC hnorm hlip hδ hδ1
        (div_pos hnp hx)) (by positivity)
    _ = _ := by field_simp

theorem integer_weight_difference_support {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hx : 0 < x) {n : ℕ} (hn : 0 < n)
    (hne : logarithmicIntegerWeight δ (Real.log x) n - additiveIntegerWeight (δ * x) x n ≠ 0) :
    x < n ∧ (n : ℝ) ≤ (1 + 2 * δ) * x := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logarithmicIntegerWeight_ratio hδ hx hn, additiveIntegerWeight_ratio hδ hx,
    ← smul_sub] at hne
  have hraw : ((n : ℝ) / x)⁻¹ • oneSidedSchwartzWindow
      ((-Real.log ((n : ℝ) / x)) / δ) -
        oneSidedSchwartzWindow ((1 - (n : ℝ) / x) / δ) ≠ 0 := by
    intro hzero
    exact hne (by rw [hzero, smul_zero])
  have hratio : 1 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 1 + 2 * δ := by
    by_cases hlog : ((n : ℝ) / x)⁻¹ • oneSidedSchwartzWindow
        ((-Real.log ((n : ℝ) / x)) / δ) = 0
    · have hadd : oneSidedSchwartzWindow ((1 - (n : ℝ) / x) / δ) ≠ 0 := by
        intro hzero
        exact hraw (by rw [hlog, hzero, sub_self])
      exact additive_ratio_support hδ hadd
    · exact logarithmic_ratio_support hδ hδ1 (div_pos hnp hx) hlog
  exact ⟨by simpa using (lt_div_iff₀ hx).mp hratio.1, (div_le_iff₀ hx).mp hratio.2⟩

end Erdos421
