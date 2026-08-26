/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integrability and mean bounds for the local second-derivative energy.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DerivativeMoments
import ErdosProblems.Erdos521.CircularMaximal

namespace Erdos521

open MeasureTheory Filter

noncomputable def secondDerivativeEnergy (n : ℕ) (a b : ℝ) (ε : ℕ → ℝ) : ℝ :=
  ∫ u in a..b, ((polynomial ε n).derivative.derivative.eval u) ^ 2

theorem secondDerivativeEnergy_nonneg (n : ℕ) {a b : ℝ} (hab : a ≤ b) (ε : ℕ → ℝ) :
    0 ≤ secondDerivativeEnergy n a b ε :=
  intervalIntegral.integral_nonneg_of_forall hab (fun _ ↦ sq_nonneg _)

theorem polynomial_second_derivative_joint_continuous (n : ℕ) :
    Continuous (fun p : ℝ × (ℕ → ℝ) ↦ (polynomial p.2 n).derivative.derivative.eval p.1) := by
  simp_rw [polynomial_second_derivative_eval]
  fun_prop

theorem second_derivative_product_integrable (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Integrable (fun p : ℝ × (ℕ → ℝ) ↦ ((polynomial p.2 n).derivative.derivative.eval p.1) ^ 2)
      ((volume.restrict (Set.uIoc a b)).prod sequenceLaw) := by
  have hcont := (polynomial_second_derivative_joint_continuous n).pow 2
  rw [Set.uIoc_of_le hab]
  have : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    constructor
    simp
  apply Integrable.mono' (integrable_const ((n + 1 : ℝ) ^ 6)) hcont.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hcont.norm.measurable measurable_const)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  filter_upwards [ae_sequence_signs] with ε hε
  have hεabs : ∀ k, |ε k| ≤ 1 := by
    intro k
    rcases hε k with h | h <;> simp [h]
  have huabs : |u| ≤ 1 := by rw [abs_of_nonneg (ha.trans hu.1.le)]; exact hu.2.trans hb
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (polynomial_second_derivative_abs_le ε hεabs n huabs) 2
  change ‖((polynomial ε n).derivative.derivative.eval u) ^ 2‖ ≤ (n + 1 : ℝ) ^ 6
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((polynomial ε n).derivative.derivative.eval u))]
  simpa only [sq_abs, ← pow_mul] using h

theorem secondDerivativeEnergy_integrable (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Integrable (secondDerivativeEnergy n a b) sequenceLaw := by
  change Integrable (fun ε ↦ ∫ u in a..b, ((polynomial ε n).derivative.derivative.eval u) ^ 2)
    sequenceLaw
  have h := (second_derivative_product_integrable n ha hab hb).integral_prod_right
  simpa only [secondDerivativeEnergy, intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab] using h

theorem integral_secondDerivativeEnergy_le (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (∫ ε, secondDerivativeEnergy n a b ε ∂sequenceLaw) ≤ 24 * (b - a) / (1 - b) ^ 5 := by
  have hprod := second_derivative_product_integrable n ha hab hb.le
  change (∫ ε, (∫ u in a..b, ((polynomial ε n).derivative.derivative.eval u) ^ 2) ∂sequenceLaw) ≤ _
  rw [← intervalIntegral_integral_swap hprod]
  have hint : IntervalIntegrable (fun u ↦
      ∫ ε, ((polynomial ε n).derivative.derivative.eval u) ^ 2 ∂sequenceLaw) volume a b :=
    intervalIntegrable_iff.mpr hprod.integral_prod_left
  have hbound (u : ℝ) (hu : u ∈ Set.Icc a b) :
      (∫ ε, ((polynomial ε n).derivative.derivative.eval u) ^ 2 ∂sequenceLaw) ≤ 24 / (1 - b) ^ 5 := by
    apply (polynomial_second_derivative_moment_le n (ha.trans hu.1) (hu.2.trans_lt hb)).trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by linarith : 0 ≤ 1 - b) (sub_le_sub_left hu.2 1) 5)
  have h := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_div_assoc, mul_comm] using h

end Erdos521
