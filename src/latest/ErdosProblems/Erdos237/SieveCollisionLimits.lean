import BoundedGaps.Maynard.MaynardYDiagonalCollisionMass
import BoundedGaps.Maynard.MaynardS1CrossCorrectionBound
import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit
import BoundedGaps.Maynard.ConcreteS1CrossLimit

/-!
# Generic vanishing of coordinate collisions and S1 cross terms

The elementary collision bounds and the one-dimensional reciprocal-totient
asymptotic already in `BoundedGaps` apply in every fixed finite dimension.
Normalize directly by the natural-radius leading term, avoiding the fixed
105-dimensional real-radius normalization used by the concrete application.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def sieveCoordinateScale (alpha : ℝ) (N : ℕ) : ℝ :=
  preSieveSingularSeries (tripleLogCutoff (N - 1)) *
    Real.log (engelsmaMaynardRadius alpha N)

theorem eventually_sieveCoordinateScale_pos {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < sieveCoordinateScale alpha N := by
  filter_upwards [eventually_one_lt_engelsmaMaynardRadius halpha] with N hN
  exact mul_pos (preSieveSingularSeries_pos _)
    (Real.log_pos (by exact_mod_cast hN))

theorem tendsto_mean_div_sieveCoordinateScale {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean (engelsmaMaynardModulus N)
        (engelsmaMaynardRadius alpha N) / sieveCoordinateScale alpha N)
      atTop (nhds 1) :=
  tendsto_engelsmaSquarefreeMean_div_leadingTerm_one halpha

theorem tendsto_normalized_collision_mass {H : Finset ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexCollisionSupport H
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds 0) := by
  have hratio := (tendsto_mean_div_sieveCoordinateScale halpha).pow (Fintype.card H)
  have hcutoff : Tendsto (fun N : ℕ => (8 : ℝ) / tripleLogCutoff (N - 1))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp tendsto_shifted_tripleLogCutoff
  have henv : Tendsto (fun N : ℕ =>
      ((offDiagonalPairs H).card : ℝ) *
        (squarefreeCoprimeInvTotientMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) / sieveCoordinateScale alpha N) ^ Fintype.card H *
        (8 / (tripleLogCutoff (N - 1) : ℝ))) atTop (nhds 0) := by
    simpa using (hratio.const_mul ((offDiagonalPairs H).card : ℝ)).mul hcutoff
  apply squeeze_zero' ?_ ?_ henv
  · filter_upwards [eventually_sieveCoordinateScale_pos halpha] with N hscale
    exact div_nonneg (sum_nonneg fun u _ => by
      unfold reciprocalTotientTupleWeight
      positivity) (pow_nonneg hscale.le _)
  · filter_upwards [eventually_sieveCoordinateScale_pos halpha,
      tendsto_shifted_tripleLogCutoff.eventually_gt_atTop 0] with N hscale hD
    have hbound := collisionWeightSum_le_explicit (H := H)
      (R := engelsmaMaynardRadius alpha N) hD
    have hdiv := div_le_div_of_nonneg_right hbound
      (pow_nonneg hscale.le (Fintype.card H))
    convert hdiv using 1
    all_goals try rfl
    all_goals try simp only [engelsmaMaynardModulus, div_pow]
    all_goals ring

theorem tendsto_normalized_s1_cross {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (y : ℕ → (H → ℕ) → ℝ)
    (hy : ∀ N, IsSupportedMaynardY H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) (y N))
    (hbound : ∀ N r, |y N r| ≤ B) :
    Tendsto (fun N : ℕ =>
      incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N))
        (maynardCoefficientFromY H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (y N)) /
        sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds 0) := by
  let C : ℝ := B ^ 2 * (8 * Real.exp 8) * ((offDiagonalPairs H).card : ℝ) *
    Real.exp 8 ^ ((offDiagonalPairs H).card - 1)
  have hratio := (tendsto_mean_div_sieveCoordinateScale halpha).pow (Fintype.card H)
  have hcutoff : Tendsto (fun N : ℕ => C / tripleLogCutoff (N - 1))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp tendsto_shifted_tripleLogCutoff
  have henv : Tendsto (fun N : ℕ =>
      (C / tripleLogCutoff (N - 1)) *
        (squarefreeCoprimeInvTotientMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) / sieveCoordinateScale alpha N) ^ Fintype.card H)
      atTop (nhds 0) := by simpa using hcutoff.mul hratio
  apply squeeze_zero_norm' ?_ henv
  filter_upwards [eventually_sieveCoordinateScale_pos halpha,
    eventually_one_lt_engelsmaMaynardRadius halpha,
    tendsto_shifted_tripleLogCutoff.eventually_gt_atTop 0] with N hscale hR hD
  have hb := abs_incompatibleSum_le_explicit
    (H := H) (R := engelsmaMaynardRadius alpha N) (y := y N)
    (zero_lt_one.trans hR) hD hB (hbound N) (hy N)
  have hd := div_le_div_of_nonneg_right hb (pow_nonneg hscale.le (Fintype.card H))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hscale _)]
  convert hd using 1
  all_goals try rfl
  all_goals try simp only [engelsmaMaynardModulus, C, div_pow]
  all_goals ring

theorem tendsto_normalized_weighted_collision {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (f : ℕ → (H → ℕ) → ℝ)
    (hbound : ∀ N r, |f N r| ≤ B) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexCollisionSupport H
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        f N u ^ 2 * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds 0) := by
  have henv := (tendsto_normalized_collision_mass (H := H) halpha).const_mul (B ^ 2)
  simp only [mul_zero] at henv
  apply squeeze_zero' ?_ ?_ henv
  · filter_upwards [eventually_sieveCoordinateScale_pos halpha] with N hscale
    apply div_nonneg _ (pow_nonneg hscale.le _)
    apply sum_nonneg
    intro u _
    unfold reciprocalTotientTupleWeight
    positivity
  · filter_upwards [eventually_sieveCoordinateScale_pos halpha] with N hscale
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hscale.le _)
    rw [mul_sum]
    apply sum_le_sum
    intro u _
    have hsq : f N u ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f N u)) hB).mpr (hbound N u)
    exact mul_le_mul_of_nonneg_right hsq (by
      unfold reciprocalTotientTupleWeight
      positivity)

end Erdos237
