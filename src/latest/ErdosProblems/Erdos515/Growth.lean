import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Erdős Problem 515: elementary growth facts

This file isolates the only facts about transcendental entire functions needed by the
potential-theoretic part of the proof.  We use the Cauchy power series at the origin and prove
directly that its coefficients cannot be eventually zero.  Cauchy's estimate then turns any
nonzero high coefficient into a lower bound on a value of the function on every sufficiently
large circle.
-/

open Filter Set
open scoped ENNReal Polynomial Topology

namespace Erdos515

/-- An exact predicate saying that `f` is the function represented by a complex polynomial. -/
def IsPolynomialFunction (f : ℂ → ℂ) : Prop :=
  ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z

/-- The Taylor series at the origin, canonically chosen using Cauchy's integral formula on the
unit circle.  For an entire function this series has infinite radius. -/
noncomputable def taylorSeries (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries f 0 1

/-- The scalar coefficient of `z ^ n` in `taylorSeries f`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (taylorSeries f).coeff n

lemma differentiable_hasFPowerSeriesOnBall_taylorSeries {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    HasFPowerSeriesOnBall f (taylorSeries f) 0 ∞ := by
  simpa [taylorSeries] using
    hf.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)

/-- If the Taylor coefficients of an entire function vanish from some index onward, the
function is represented everywhere by the corresponding finite complex polynomial. -/
theorem isPolynomialFunction_of_taylorCoeff_eventually_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {N : ℕ}
    (hzero : ∀ n, N ≤ n → taylorCoeff f n = 0) :
    IsPolynomialFunction f := by
  let p : ℂ[X] := ∑ n ∈ Finset.range N, Polynomial.monomial n (taylorCoeff f n)
  refine ⟨p, fun z ↦ ?_⟩
  have hsum : HasSum (fun n : ℕ ↦ z ^ n * taylorCoeff f n) (f z) := by
    have h := (differentiable_hasFPowerSeriesOnBall_taylorSeries hf).hasSum (y := z) (by simp)
    simpa [taylorCoeff, smul_eq_mul] using h
  have hfinite : HasSum (fun n : ℕ ↦ z ^ n * taylorCoeff f n)
      (∑ n ∈ Finset.range N, z ^ n * taylorCoeff f n) :=
    hasSum_sum_of_ne_finset_zero fun n hn ↦ by
      rw [Finset.mem_range, not_lt] at hn
      simp [hzero n hn]
  have heq : f z = ∑ n ∈ Finset.range N, z ^ n * taylorCoeff f n :=
    hsum.unique hfinite
  calc
    p.eval z = ∑ n ∈ Finset.range N, z ^ n * taylorCoeff f n := by
      simp [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]
    _ = f z := heq.symm

/-- A non-polynomial entire function has nonzero Taylor coefficients in arbitrarily high
degrees. -/
theorem exists_taylorCoeff_ne_zero_ge {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) (N : ℕ) :
    ∃ n, N ≤ n ∧ taylorCoeff f n ≠ 0 := by
  by_contra h
  push Not at h
  exact htrans (isPolynomialFunction_of_taylorCoeff_eventually_zero hf h)

/-- Cauchy's estimate, in the precise witness form used below: on every positive-radius circle,
some value of an entire function dominates each Taylor monomial in norm. -/
theorem exists_norm_eq_taylorCoeff_mul_pow_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ = r ∧ ‖taylorCoeff f n‖ * r ^ n ≤ ‖f z‖ := by
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hf.continuous.continuousOn.norm
  refine ⟨z, ?_, ?_⟩
  · simpa [mem_sphere_iff_norm] using hz
  have hcircle : ∀ θ : ℝ, ‖f (circleMap 0 r θ)‖ ≤ ‖f z‖ := fun θ ↦
    hzmax (circleMap_mem_sphere 0 hr.le θ)
  have hint : IntervalIntegrable (fun θ : ℝ ↦ ‖f (circleMap 0 r θ)‖)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (hf.continuous.comp (continuous_circleMap 0 r)).norm.intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ ‖f z‖) MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have havg_le :
      (2 * Real.pi)⁻¹ * (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤ ‖f z‖ := by
    have hi := intervalIntegral.integral_mono_on Real.two_pi_pos.le hint hconst
      (fun θ _ ↦ hcircle θ)
    calc
      (2 * Real.pi)⁻¹ * (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) ≤
          (2 * Real.pi)⁻¹ * (∫ _ : ℝ in 0..2 * Real.pi, ‖f z‖) := by
            exact mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.two_pi_pos.le)
      _ = ‖f z‖ := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul]
        field_simp
  let R : NNReal := ⟨r, hr.le⟩
  have hseriesR : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 r) 0 ∞ := by
    have h := hf.hasFPowerSeriesOnBall 0 (R := R) (by exact_mod_cast hr)
    change HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 r) 0 ∞ at h
    exact h
  have hseries_eq : taylorSeries f = cauchyPowerSeries f 0 r :=
    (differentiable_hasFPowerSeriesOnBall_taylorSeries hf).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries hseriesR.hasFPowerSeriesAt
  have hcauchy := norm_cauchyPowerSeries_le f 0 r n
  rw [← hseries_eq, FormalMultilinearSeries.norm_apply_eq_norm_coef] at hcauchy
  have hcauchy' : ‖taylorCoeff f n‖ ≤
      ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 r θ)‖) * r⁻¹ ^ n := by
    simpa [taylorCoeff, abs_of_pos hr] using hcauchy
  have hcoeff_le : ‖taylorCoeff f n‖ ≤ ‖f z‖ * r⁻¹ ^ n := by
    exact hcauchy'.trans
      (mul_le_mul_of_nonneg_right havg_le (pow_nonneg (inv_nonneg.mpr hr.le) n))
  calc
    ‖taylorCoeff f n‖ * r ^ n ≤ (‖f z‖ * r⁻¹ ^ n) * r ^ n :=
      mul_le_mul_of_nonneg_right hcoeff_le (pow_nonneg hr.le n)
    _ = ‖f z‖ := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, mul_one]

/-- The maximum modulus of a transcendental entire function grows faster than every fixed
power, expressed without introducing a choice of maximum: for every real exponent `A`, on every
sufficiently large circle there is a point whose positive logarithmic modulus is at least
`A * log r`.  The extra assertion `1 < r` records the positive-radius condition explicitly. -/
theorem eventually_exists_norm_eq_posLog_ge {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) (A : ℝ) :
    ∀ᶠ r : ℝ in atTop,
      1 < r ∧ ∃ z : ℂ, ‖z‖ = r ∧ A * Real.log r ≤ Real.posLog ‖f z‖ := by
  obtain ⟨N : ℕ, hAN⟩ := exists_nat_gt A
  obtain ⟨n, hNn, hn0⟩ := exists_taylorCoeff_ne_zero_ge hf htrans N
  have hAn : A < (n : ℝ) := hAN.trans_le (by exact_mod_cast hNn)
  have hcoeff : 0 < ‖taylorCoeff f n‖ := norm_pos_iff.mpr hn0
  have htend : Tendsto (fun r : ℝ ↦ ((n : ℝ) - A) * Real.log r) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (sub_pos.mpr hAn)
  filter_upwards [htend.eventually_ge_atTop (-Real.log ‖taylorCoeff f n‖),
    eventually_gt_atTop (1 : ℝ)] with r hgrowth hr
  refine ⟨hr, ?_⟩
  obtain ⟨z, hz, hzlower⟩ := exists_norm_eq_taylorCoeff_mul_pow_le hf n (one_pos.trans hr)
  refine ⟨z, hz, ?_⟩
  have hlog_algebra :
      A * Real.log r ≤ Real.log ‖taylorCoeff f n‖ + (n : ℝ) * Real.log r := by
    linarith
  have hprod_pos : 0 < ‖taylorCoeff f n‖ * r ^ n :=
    mul_pos hcoeff (pow_pos (one_pos.trans hr) n)
  calc
    A * Real.log r ≤ Real.log (‖taylorCoeff f n‖ * r ^ n) := by
      rw [Real.log_mul hcoeff.ne' (pow_pos (one_pos.trans hr) n).ne', Real.log_pow]
      exact hlog_algebra
    _ ≤ Real.posLog (‖taylorCoeff f n‖ * r ^ n) := le_max_right _ _
    _ ≤ Real.posLog ‖f z‖ := Real.posLog_le_posLog hprod_pos.le hzlower

/-- A slightly streamlined form of `eventually_exists_norm_eq_posLog_ge`, omitting the redundant
eventual assertion `1 < r`. -/
theorem eventually_exists_on_circle_posLog_ge {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) (A : ℝ) :
    ∀ᶠ r : ℝ in atTop, ∃ z : ℂ, ‖z‖ = r ∧ A * Real.log r ≤ Real.posLog ‖f z‖ :=
  (eventually_exists_norm_eq_posLog_ge hf htrans A).mono fun _ h ↦ h.2

/-- The same growth statement in the literal `log (max 1 ‖f z‖)` formulation. -/
theorem eventually_exists_on_circle_log_max_ge {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) (A : ℝ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ z : ℂ, ‖z‖ = r ∧ A * Real.log r ≤ Real.log (max 1 ‖f z‖) := by
  filter_upwards [eventually_exists_on_circle_posLog_ge hf htrans A] with r hr
  obtain ⟨z, hz, hAz⟩ := hr
  exact ⟨z, hz, by simpa [Real.posLog_eq_log_max_one (norm_nonneg (f z))] using hAz⟩

end Erdos515
