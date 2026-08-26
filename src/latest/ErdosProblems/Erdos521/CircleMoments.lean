/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expected circular mean squares without a maximal-in-degree logarithmic factor.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ComplexMoments
import ErdosProblems.Erdos521.CircularMaximal

namespace Erdos521

open MeasureTheory

noncomputable def circularMeanSquare (n : ℕ) (c : ℂ) (R : ℝ) (ε : ℕ → ℝ) : ℝ :=
  Real.circleAverage (fun z ↦ ‖complexPowerSum ε n z‖ ^ 2) c R

theorem circularMeanSquare_nonneg (n : ℕ) (c : ℂ) (R : ℝ) (ε : ℕ → ℝ) :
    0 ≤ circularMeanSquare n c R ε :=
  Real.circleAverage_nonneg_of_nonneg (fun _ _ ↦ sq_nonneg _)

theorem circular_mean_square_product_integrable (n : ℕ) (c : ℂ) (R : ℝ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) ↦ ‖complexPowerSum p.2 n (circleMap c R p.1)‖ ^ 2)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod sequenceLaw) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    constructor
    simp [Set.uIoc_of_le Real.two_pi_pos.le]
    finiteness
  have hcont : Continuous (fun p : ℝ × (ℕ → ℝ) ↦
      ‖complexPowerSum p.2 n (circleMap c R p.1)‖ ^ 2) := by
    unfold complexPowerSum
    fun_prop
  apply integrable_product_of_uniform_norm_bound
    (volume.restrict (Set.uIoc 0 (2 * Real.pi))) sequenceLaw hcont.stronglyMeasurable
    (fun θ ↦ complexPowerSum_norm_sq_integrable n (circleMap c R θ))
    (geometricVariance (‖c‖ + |R|) (n + 1))
  intro θ
  simp_rw [Real.norm_eq_abs, abs_pow, abs_norm, integral_complexPowerSum_norm_sq]
  exact geometricVariance_mono_base (norm_nonneg _) (norm_circleMap_le c R θ) (n + 1)

theorem circularMeanSquare_integrable (n : ℕ) (c : ℂ) (R : ℝ) :
    Integrable (circularMeanSquare n c R) sequenceLaw := by
  change Integrable (fun ε ↦ (2 * Real.pi)⁻¹ *
    ∫ θ in 0..(2 * Real.pi), ‖complexPowerSum ε n (circleMap c R θ)‖ ^ 2) sequenceLaw
  have h := (circular_mean_square_product_integrable n c R).integral_prod_right.const_mul
    (2 * Real.pi)⁻¹
  simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Set.uIoc_of_le Real.two_pi_pos.le] using h

theorem integral_circularMeanSquare_le (n : ℕ) (c : ℂ) (R : ℝ) :
    (∫ ε, circularMeanSquare n c R ε ∂sequenceLaw) ≤
      geometricVariance (‖c‖ + |R|) (n + 1) := by
  simp only [circularMeanSquare, Real.circleAverage, smul_eq_mul, integral_const_mul]
  rw [← intervalIntegral_integral_swap (circular_mean_square_product_integrable n c R)]
  simp_rw [integral_complexPowerSum_norm_sq]
  have hint : IntervalIntegrable (fun θ ↦ geometricVariance ‖circleMap c R θ‖ (n + 1))
      volume 0 (2 * Real.pi) := by
    have h := intervalIntegrable_iff.mpr
      (circular_mean_square_product_integrable n c R).integral_prod_left
    simpa only [integral_complexPowerSum_norm_sq] using h
  have hbound := intervalIntegral.integral_mono_on Real.two_pi_pos.le hint intervalIntegrable_const
    (fun θ _ ↦ geometricVariance_mono_base (norm_nonneg _) (norm_circleMap_le c R θ) (n + 1))
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr Real.two_pi_pos.le)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul] using h

end Erdos521
