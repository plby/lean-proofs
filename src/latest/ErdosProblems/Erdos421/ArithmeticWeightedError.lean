import ErdosProblems.Erdos421.ArithmeticAbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Weighted counting errors relative to a constant local density -/

namespace Erdos421

open MeasureTheory

theorem integrableOn_arithmetic_weighted_error (c : ℕ → ℝ) (d : ℝ)
    {g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b)) :
    IntegrableOn (fun t ↦ deriv g t *
      ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a))) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t : ℝ ↦ d * (t - a)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
  have h := (integrableOn_deriv_mul_intervalSum c ha hg'.integrableOn_Icc).sub
    (hg'.mul hc).integrableOn_Icc
  change IntegrableOn (fun t ↦ deriv g t * (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) -
    deriv g t * (d * (t - a))) (Set.Icc a b) at h
  simpa only [mul_sub] using h

theorem arithmetic_weighted_discrepancy_eq (c : ℕ → ℝ) (d : ℝ)
    {g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hg : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * c n) - d * (∫ t in a..b, g t) =
      g b * ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n) - d * (b - a)) -
        ∫ t in a..b, deriv g t * ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a)) := by
  have hgc : ContinuousOn g (Set.Icc a b) :=
    fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hgi : IntervalIntegrable g volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hgc
  have hgdi : IntervalIntegrable (deriv g) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hg'
  have hlin : ContinuousOn (fun t : ℝ ↦ t - a) (Set.uIcc a b) :=
    continuousOn_id.sub continuousOn_const
  have hftc := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := g) (v := fun t : ℝ ↦ t - a) (u' := deriv g) (v' := fun _ ↦ (1 : ℝ))
    (by simpa only [Set.uIcc_of_le hab] using hgc) hlin
    (by
      intro t ht
      rw [min_eq_left hab, max_eq_right hab] at ht
      exact (hg t ⟨ht.1.le, ht.2.le⟩).hasDerivAt)
    (fun t _ ↦ (hasDerivAt_id t).sub_const a) hgdi intervalIntegrable_const
  have hdti : IntervalIntegrable (fun t ↦ deriv g t * (t - a)) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (hg'.mul (continuousOn_id.sub continuousOn_const))
  simp only [mul_one, sub_self, mul_zero, sub_zero] at hftc
  rw [intervalIntegral.integral_add hdti hgi] at hftc
  have hmain : (∫ t in a..b, g t) = g b * (b - a) - ∫ t in a..b, deriv g t * (t - a) := by
    linarith only [hftc]
  have hcounti : IntervalIntegrable (fun t ↦ deriv g t *
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_mul_intervalSum c ha hg'.integrableOn_Icc)
  have heq : (∫ t in a..b, deriv g t *
      ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a))) =
      (∫ t in a..b, deriv g t * ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) -
        d * ∫ t in a..b, deriv g t * (t - a) := by
    have hfun : (fun t ↦ deriv g t *
        ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a))) =
        (fun t ↦ deriv g t * (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) -
          d * (deriv g t * (t - a))) := by funext t; ring
    rw [hfun, intervalIntegral.integral_sub hcounti (hdti.const_mul d),
      intervalIntegral.integral_const_mul]
  rw [arithmetic_interval_weighted_sum_eq c ha hab hg hg'.integrableOn_Icc, hmain, heq]
  ring

theorem arithmetic_weighted_error_le (c : ℕ → ℝ) (d : ℝ) {g : ℝ → ℝ} {a b E : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hg : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b))
    (herr : ∀ t ∈ Set.Icc a b, |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a)| ≤ E) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * c n) - d * (∫ t in a..b, g t)| ≤
      E * (|g b| + ∫ t in a..b, |deriv g t|) := by
  have hei : IntervalIntegrable (fun t ↦ deriv g t *
      ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a))) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_arithmetic_weighted_error c d ha hg')
  have hright : ContinuousOn (fun t ↦ E * |deriv g t|) (Set.Icc a b) :=
    continuousOn_const.mul hg'.abs
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab hei.abs
    (ContinuousOn.intervalIntegrable_of_Icc hab hright) (by
      intro t ht
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (herr t ht) (abs_nonneg _)).trans_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at hm
  have hi := (intervalIntegral.abs_integral_le_integral_abs hab).trans hm
  rw [arithmetic_weighted_discrepancy_eq c d ha hab hg hg']
  calc
    _ ≤ |g b * ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n) - d * (b - a))| +
        |∫ t in a..b, deriv g t *
          ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) - d * (t - a))| := abs_sub _ _
    _ ≤ |g b| * E + E * ∫ t in a..b, |deriv g t| := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (herr b ⟨hab, le_rfl⟩) (abs_nonneg _)) hi
    _ = _ := by ring

end Erdos421
