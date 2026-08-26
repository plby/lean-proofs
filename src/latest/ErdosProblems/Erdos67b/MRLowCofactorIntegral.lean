import ErdosProblems.Erdos67b.MRTypicalLowHigh

/-!
# Denominator averaging on the positive low-prime half-plane

The beta identity only needs absolute convergence of the unscaled series.
In particular it remains valid for the nonmultiplicative typical low
coefficient at the left line of the moving Perron contour.
-/

open scoped BigOperators Classical Interval LSeries.notation
open Finset MeasureTheory

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrNorm_primeScaledCoefficient_le
    (A : Finset ℕ) (f : ℕ → ℂ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    ‖mrPrimeScaledCoefficient A f u n‖ ≤ ‖f n‖ := by
  rw [mrPrimeScaledCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 _)]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hu0 hu1)

theorem mrCofactorLSeries_eq_intervalIntegral_of_summable
    (A : Finset ℕ) {f : ℕ → ℂ} {s : ℂ} (hs : LSeriesSummable f s) :
    mrCofactorLSeries A f s =
      ∫ u in (0 : ℝ)..1, LSeries (mrPrimeScaledCoefficient A f u) s := by
  let F : ℕ → ℝ → ℂ := fun n u ↦ LSeries.term (mrPrimeScaledCoefficient A f u) s n
  have hFi : ∀ n, IntervalIntegrable (F n) volume (0 : ℝ) 1 :=
    fun n ↦ (continuous_mrPrimeScaledCoefficient_LSeries_term A f s n).intervalIntegrable _ _
  have hFset : ∀ n, IntegrableOn (F n) (Set.Ioc (0 : ℝ) 1) :=
    fun n ↦ (continuous_mrPrimeScaledCoefficient_LSeries_term A f s n).integrableOn_Ioc
  have htermBound (n : ℕ) : (∫ u in (0 : ℝ)..1, ‖F n u‖) ≤ ‖LSeries.term f s n‖ := by
    have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖F n u‖ ≤ ‖LSeries.term f s n‖ := by
      intro u hu
      exact LSeries.norm_term_le s (mrNorm_primeScaledCoefficient_le A f hu.1 hu.2 n)
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hFi n).norm (continuous_const.intervalIntegrable 0 1) hpoint
    simpa using hmono
  have hintsum : Summable (fun n : ℕ ↦ ∫ u in (0 : ℝ)..1, ‖F n u‖) :=
    hs.norm.of_nonneg_of_le
      (fun n ↦ intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ norm_nonneg _))
      htermBound
  have hinterchange : (∑' n : ℕ, ∫ u in (0 : ℝ)..1, F n u) =
      ∫ u in (0 : ℝ)..1, ∑' n : ℕ, F n u := by
    have hset : Summable (fun n : ℕ ↦ ∫ u in Set.Ioc (0 : ℝ) 1, ‖F n u‖) := by
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hintsum
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      integral_tsum_of_summable_integral_norm hFset hset
  rw [mrCofactorLSeries, LSeries]
  calc
    _ = ∑' n : ℕ, ∫ u in (0 : ℝ)..1, F n u := by
      apply tsum_congr
      intro n
      exact (intervalIntegral_mrPrimeScaledCoefficient_LSeries_term A f s n).symm
    _ = _ := hinterchange

theorem mrPrimeScaled_indexedTypicalCoefficient {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ) (u : ℝ) :
    mrPrimeScaledCoefficient A (mrIndexedTypicalCoefficient J B f) u =
      mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u) := by
  funext n
  unfold mrPrimeScaledCoefficient mrIndexedTypicalCoefficient
  split_ifs <;> simp

theorem mrLSeries_typicalCofactorLow_eq_intervalIntegral {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeries (mrTypicalCofactorLowArithmetic A J B f y) s =
      ∫ u in (0 : ℝ)..1,
        LSeries (gsA9Low (mrIndexedTypicalCoefficient J B (mrPrimeScaledCoefficient A f u)) y) s := by
  have hlow : LSeriesSummable (gsA9Low (mrIndexedTypicalCoefficient J B f) y) s :=
    mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re
      (fun n hn ↦ mrIndexedTypicalCoefficient_norm_le J B hbound hn)
      (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) hs
  have hid : LSeries (mrTypicalCofactorLowArithmetic A J B f y) s =
      mrCofactorLSeries A (gsA9Low (mrIndexedTypicalCoefficient J B f) y) s := by
    apply LSeries_congr
    intro n hn
    simp only [mrTypicalCofactorLowArithmetic, toArithmeticFunction]
    change (if n = 0 then 0 else
      gsA9Low (mrIndexedTypicalCofactorCoefficient A J B f) y n) = _
    rw [if_neg hn]
    exact congrFun (mrPrimeBandCoefficient_div (mrIndexedTypicalCoefficient J B f)
      (fun n ↦ (mrCommonDenominator A n : ℂ)) (fun p ↦ p ≤ y)) n
  rw [hid, mrCofactorLSeries_eq_intervalIntegral_of_summable A hlow]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [gsA9Low, mrPrimeScaled_primeBandCoefficient, mrPrimeScaled_indexedTypicalCoefficient]
  rfl

end

end Erdos67b
