import ErdosProblems.Erdos421.RealWindowKernel
import ErdosProblems.Erdos421.PositiveDivisorWindows
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Derivative and variation bounds for the actual additive kernel -/

namespace Erdos421

open MeasureTheory

noncomputable def realAdditiveKernel (Y x t : ℝ) : ℝ :=
  Y⁻¹ * oneSidedRealWindow ((x - t) / Y)

theorem realAdditiveKernel_nat (Y x : ℝ) (n : ℕ) :
    realAdditiveKernel Y x n = (additiveIntegerWeight Y x n).re := by
  simp only [additiveIntegerWeight, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem realAdditiveKernel_nonzero {Y x t : ℝ} (hY : 0 < Y)
    (ht : realAdditiveKernel Y x t ≠ 0) : x < t ∧ t < x + Y := by
  have hφ : oneSidedRealWindow ((x - t) / Y) ≠ 0 := (mul_ne_zero_iff.mp ht).2
  obtain ⟨hlo, hhi⟩ := oneSidedRealWindow_nonzero hφ
  have hl := (lt_div_iff₀ hY).mp hlo
  have hh := (div_lt_iff₀ hY).mp hhi
  constructor <;> linarith

theorem realAdditiveKernel_right {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    realAdditiveKernel Y x (x + Y) = 0 := by
  by_contra h
  exact (lt_irrefl _ (realAdditiveKernel_nonzero hY h).2)

theorem realAdditiveKernel_hasDerivAt {Y : ℝ} (hY : 0 < Y) (x t : ℝ) :
    HasDerivAt (realAdditiveKernel Y x)
      (-deriv (oneSidedRealWindow : ℝ → ℝ) ((x - t) / Y) / Y ^ 2) t := by
  have hd := ((oneSidedRealWindow.differentiableAt (x := (x - t) / Y)).hasDerivAt.comp t
    (((hasDerivAt_const t x).sub (hasDerivAt_id t)).div_const Y)).const_mul Y⁻¹
  dsimp only [Pi.sub_apply, id_eq] at hd
  convert hd using 1 <;> first | rfl | (field_simp; ring)

theorem realAdditiveKernel_deriv_continuous (Y x : ℝ) :
    Continuous (deriv (realAdditiveKernel Y x)) := by
  have hc : ContDiff ℝ 1 (realAdditiveKernel Y x) :=
    contDiff_const.mul ((oneSidedRealWindow.smooth 1).comp
      ((contDiff_const.sub contDiff_id).div_const Y))
  exact hc.continuous_deriv_one

theorem realAdditiveKernel_variation_le {C Y : ℝ}
    (hC : ∀ t : ℝ, |deriv (oneSidedRealWindow : ℝ → ℝ) t| ≤ C)
    (hY : 0 < Y) (x : ℝ) :
    |realAdditiveKernel Y x (x + Y)| +
      (∫ t in x..x + Y, |deriv (realAdditiveKernel Y x) t|) ≤ C / Y := by
  have hab : x ≤ x + Y := by linarith
  have hi : IntervalIntegrable (fun t ↦ |deriv (realAdditiveKernel Y x) t|) volume x (x + Y) :=
    (realAdditiveKernel_deriv_continuous Y x).abs.intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab hi
    (intervalIntegrable_const (c := C / Y ^ 2)) (by
      intro t ht
      rw [(realAdditiveKernel_hasDerivAt hY x t).deriv, abs_div, abs_neg,
        abs_of_nonneg (sq_nonneg Y)]
      exact div_le_div_of_nonneg_right (hC _) (sq_nonneg Y))
  rw [realAdditiveKernel_right hY x, abs_zero, zero_add]
  apply hm.trans_eq
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

end Erdos421
