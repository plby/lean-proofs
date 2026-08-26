import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Oscillatory interval and cylinder-sum bounds

The marked-Poisson argument integrates a nonzero Fourier phase over many
continued-fraction cylinders.  This file proves the exact one-interval
bound and its finite-family summation consequence, with the frequency lower
bound and the number of intervals explicit.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- The real-frequency phase `exp(2π i K x)`. -/
def oscillatoryPhase (K x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * K * x : ℝ) : ℂ) * Complex.I)

theorem intervalIntegral_oscillatoryPhase
    (a b K : ℝ) (hK : K ≠ 0) :
    (∫ x : ℝ in a..b, oscillatoryPhase K x) =
      (Complex.exp (((2 * Real.pi * K * b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * Real.pi * K * a : ℝ) : ℂ) * Complex.I)) /
          (((2 * Real.pi * K : ℝ) : ℂ) * Complex.I) := by
  let c : ℂ := (((2 * Real.pi * K : ℝ) : ℂ) * Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by
      norm_cast
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hK)
      Complex.I_ne_zero
  rw [show (fun x : ℝ ↦ oscillatoryPhase K x) =
      fun x : ℝ ↦ Complex.exp (c * x) by
    funext x
    unfold oscillatoryPhase c
    congr 1
    push_cast
    ring]
  rw [integral_exp_mul_complex hc]
  dsimp [c]
  congr 2 <;> push_cast <;> ring_nf

private theorem norm_pureImaginary_exp (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private theorem norm_oscillatory_denominator (K : ℝ) :
    ‖(((2 * Real.pi * K : ℝ) : ℂ) * Complex.I)‖ =
      2 * Real.pi * |K| := by
  rw [norm_mul, Complex.norm_real, Complex.norm_I]
  rw [mul_one, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos]

/-- Uniform oscillatory cancellation on one interval.  The bound is
independent of the interval length and both endpoints. -/
theorem norm_intervalIntegral_oscillatoryPhase_le
    (a b K : ℝ) (hK : K ≠ 0) :
    ‖∫ x : ℝ in a..b, oscillatoryPhase K x‖ ≤
      1 / (Real.pi * |K|) := by
  rw [intervalIntegral_oscillatoryPhase a b K hK, norm_div,
    norm_oscillatory_denominator]
  have hnum :
      ‖Complex.exp (((2 * Real.pi * K * b : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((2 * Real.pi * K * a : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (((2 * Real.pi * K * b : ℝ) : ℂ) * Complex.I)‖ +
          ‖Complex.exp (((2 * Real.pi * K * a : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [norm_pureImaginary_exp, norm_pureImaginary_exp]; norm_num
  have hden : 0 < 2 * Real.pi * |K| := by
    positivity
  calc
    _ ≤ 2 / (2 * Real.pi * |K|) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = 1 / (Real.pi * |K|) := by field_simp

/-- Manuscript normalization `K = N D`. -/
theorem norm_intervalIntegral_oscillatoryPhase_nat_mul_le
    (a b D : ℝ) (N : ℕ) (hN : 0 < N) (hD : D ≠ 0) :
    ‖∫ x : ℝ in a..b, oscillatoryPhase ((N : ℝ) * D) x‖ ≤
      1 / (Real.pi * (N : ℝ) * |D|) := by
  have hK : (N : ℝ) * D ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hN.ne') hD
  simpa [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) by positivity),
    mul_assoc] using
    norm_intervalIntegral_oscillatoryPhase_le a b ((N : ℝ) * D) hK

/-- Finite cylinder-sum form: if every retained frequency has magnitude at
least `κ`, the total absolute integral is at most the number of cylinders
times `1/(πκ)`. -/
theorem sum_norm_intervalIntegral_oscillatoryPhase_le
    {ι : Type*} (s : Finset ι) (a b K : ι → ℝ)
    {κ : ℝ} (hκ : 0 < κ)
    (hK : ∀ i ∈ s, κ ≤ |K i|) :
    (∑ i ∈ s,
      ‖∫ x : ℝ in a i..b i, oscillatoryPhase (K i) x‖) ≤
      (s.card : ℝ) / (Real.pi * κ) := by
  calc
    (∑ i ∈ s,
      ‖∫ x : ℝ in a i..b i, oscillatoryPhase (K i) x‖) ≤
        ∑ _i ∈ s, (1 / (Real.pi * κ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hKi : K i ≠ 0 := by
        intro hz
        have hbound := hK i hi
        rw [hz, abs_zero] at hbound
        exact (not_le_of_gt hκ) hbound
      calc
        ‖∫ x : ℝ in a i..b i, oscillatoryPhase (K i) x‖ ≤
            1 / (Real.pi * |K i|) :=
          norm_intervalIntegral_oscillatoryPhase_le (a i) (b i) (K i) hKi
        _ ≤ 1 / (Real.pi * κ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact mul_le_mul_of_nonneg_left (hK i hi) Real.pi_pos.le
    _ = (s.card : ℝ) / (Real.pi * κ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Version with an externally verified combinatorial cardinal bound.  This
separates the analytic cancellation from the cylinder-counting argument. -/
theorem sum_norm_intervalIntegral_oscillatoryPhase_le_of_card
    {ι : Type*} (s : Finset ι) (a b K : ι → ℝ)
    {κ : ℝ} (hκ : 0 < κ) (C : ℕ) (hcard : s.card ≤ C)
    (hK : ∀ i ∈ s, κ ≤ |K i|) :
    (∑ i ∈ s,
      ‖∫ x : ℝ in a i..b i, oscillatoryPhase (K i) x‖) ≤
      (C : ℝ) / (Real.pi * κ) := by
  calc
    _ ≤ (s.card : ℝ) / (Real.pi * κ) :=
      sum_norm_intervalIntegral_oscillatoryPhase_le s a b K hκ hK
    _ ≤ (C : ℝ) / (Real.pi * κ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity

end

end Erdos1002
