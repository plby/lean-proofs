import ErdosProblems.Erdos421.WindowKernelArithmetic
import ErdosProblems.Erdos421.OneSidedSchwartzWindow

/-! # Additive and logarithmic kernels at a fixed ratio -/

namespace Erdos421

open scoped SchwartzMap

theorem ratio_kernel_difference_le (φ : 𝓢(ℝ, ℂ)) {C δ r : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ t : ℝ, ‖φ t‖ ≤ C)
    (hlip : ∀ s t : ℝ, ‖φ s - φ t‖ ≤ C * |s - t|)
    (hδ : 0 < δ) (hr : 1 ≤ r) (hrδ : r ≤ 1 + 2 * δ) :
    ‖(r⁻¹ : ℝ) • φ ((-Real.log r) / δ) - φ ((1 - r) / δ)‖ ≤ 6 * C * δ := by
  have he : (r⁻¹ : ℝ) • φ ((-Real.log r) / δ) - φ ((1 - r) / δ) =
      (r⁻¹ - 1) • φ ((-Real.log r) / δ) +
        (φ ((-Real.log r) / δ) - φ ((1 - r) / δ)) := by
    rw [sub_smul, one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖(r⁻¹ - 1) • φ ((-Real.log r) / δ)‖ +
        ‖φ ((-Real.log r) / δ) - φ ((1 - r) / δ)‖ := norm_add_le _ _
    _ ≤ |r⁻¹ - 1| * C + C * |(-Real.log r) / δ - (1 - r) / δ| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (hnorm _) (abs_nonneg _)) (hlip _ _)
    _ ≤ (2 * δ) * C + C * (4 * δ) :=
      add_le_add (mul_le_mul_of_nonneg_right (reciprocal_window_ratio_difference hr hrδ) hC)
        (mul_le_mul_of_nonneg_left (log_window_argument_difference hδ hr hrδ) hC)
    _ = _ := by ring

theorem logarithmic_ratio_support {δ r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hr : 0 < r)
    (h : (r⁻¹ : ℝ) • oneSidedSchwartzWindow ((-Real.log r) / δ) ≠ 0) :
    1 < r ∧ r ≤ 1 + 2 * δ := by
  have hφ : oneSidedSchwartzWindow ((-Real.log r) / δ) ≠ 0 := by
    intro hzero
    exact h (by rw [hzero, smul_zero])
  obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero hφ
  have hlogpos : 0 < Real.log r := by
    have hb := (div_lt_iff₀ hδ).mp hhi
    linarith
  have hloglt : Real.log r < δ := by
    have hb := (lt_div_iff₀ hδ).mp hlo
    linarith
  constructor
  · simpa only [Real.exp_zero, Real.exp_log hr] using Real.exp_lt_exp.mpr hlogpos
  · have hb : r < Real.exp δ := by simpa only [Real.exp_log hr] using Real.exp_lt_exp.mpr hloglt
    exact hb.le.trans (exp_le_one_add_two_mul_half hδ.le hδ1)

theorem additive_ratio_support {δ r : ℝ} (hδ : 0 < δ)
    (h : oneSidedSchwartzWindow ((1 - r) / δ) ≠ 0) :
    1 < r ∧ r ≤ 1 + 2 * δ := by
  obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero h
  have hlow := (lt_div_iff₀ hδ).mp hlo
  have hhigh := (div_lt_iff₀ hδ).mp hhi
  constructor <;> linarith

theorem oneSided_ratio_kernel_difference {C δ r : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ t : ℝ, ‖oneSidedSchwartzWindow t‖ ≤ C)
    (hlip : ∀ s t : ℝ,
      ‖oneSidedSchwartzWindow s - oneSidedSchwartzWindow t‖ ≤ C * |s - t|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hr : 0 < r) :
    ‖(r⁻¹ : ℝ) • oneSidedSchwartzWindow ((-Real.log r) / δ) -
      oneSidedSchwartzWindow ((1 - r) / δ)‖ ≤ 6 * C * δ := by
  by_cases hlog : (r⁻¹ : ℝ) • oneSidedSchwartzWindow ((-Real.log r) / δ) = 0
  · by_cases hadd : oneSidedSchwartzWindow ((1 - r) / δ) = 0
    · rw [hlog, hadd, sub_self, norm_zero]
      positivity
    · obtain ⟨hr1, hrδ⟩ := additive_ratio_support hδ hadd
      exact ratio_kernel_difference_le _ hC hnorm hlip hδ hr1.le hrδ
  · obtain ⟨hr1, hrδ⟩ := logarithmic_ratio_support hδ hδ1 hr hlog
    exact ratio_kernel_difference_le _ hC hnorm hlip hδ hr1.le hrδ

end Erdos421
