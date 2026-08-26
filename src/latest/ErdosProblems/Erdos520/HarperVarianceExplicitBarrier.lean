import ErdosProblems.Erdos520.HarperScheduledOffDiagonalBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos
namespace Problem520

noncomputable section

/-!
# Variance-explicit scheduled barrier comparison

The fixed-height-window versions of the scheduled Gaussian replacement are
convenient for a compact interval, but their eventual threshold depends on
that fixed window.  In the final Harper specialization the vertical cutoff
grows with the Euler cutoff.  The analytic replacement itself does not need
the fixed window: after the prime arithmetic has put every block variance in
`[1/4, 1/2]`, all remaining CDF, relative-cell, product, and ballot estimates
are uniform.

This file exposes that stronger interface.  The only eventual threshold left
below is the universal comparison between the doubly-exponential Fejer error
and a moderate Gaussian cell; it is independent of the tilt height.
-/

/-! ## One-block replacement from an explicit variance lower bound -/

/-- Strong-frequency Kolmogorov replacement at arbitrary tilt and evaluation
heights.  The sole arithmetic input is nondegeneracy of the actual block
variance. -/
theorem harperScheduledOffDiagonalCDFDistance_le_strong_of_variance_quarter
    {y j : ℕ} {t u : ℝ}
    (hvar : (1 / 4 : ℝ) <
      harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t u) :
    harperCDFDistance
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u)
        (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u) ≤
      130 / harperScheduledStrongComparisonFrequency j := by
  let V : ℝ := harperLinearBlockVariance y
    (harperScheduledPrimeBlock y j) t u
  let T : ℝ := harperScheduledStrongComparisonFrequency j
  have hV : (1 / 4 : ℝ) < V := hvar
  have hVnn : harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t u ≠ 0 := by
    intro hzero
    have hcoezero : V = 0 := by
      simpa only [V, coe_harperLinearBlockVarianceNNReal] using!
        congrArg ((↑·) : NNReal → ℝ) hzero
    linarith
  have hT : 0 < T := harperScheduledStrongComparisonFrequency_pos j
  have hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ) :=
    harperScheduledStrongComparisonFrequency_condition j
  have hbase := harperCDFDistance_scheduledBlock_le_of_fejer_identity
    y j t u T hT hfrequency hVnn
      (by simpa only [T] using!
        harperScheduledStrongFejerSmoothedCDFIdentity y j t u)
  have hkernel :
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    simpa only [T] using!
      harperScheduledStrongComparisonFrequency_kernel_budget j
  have hkernel' :
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    calc
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) =
          (2 * Real.pi)⁻¹ *
            ((Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
              (32 * T ^ 3 + T ^ 4)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (33 / T) := by gcongr
      _ ≤ 1 * (33 / T) := by
        gcongr
        exact fejer_coefficient_le_one
      _ = 33 / T := by ring
  have hvarinv : (Real.sqrt V)⁻¹ ≤ 2 :=
    inv_sqrt_le_two_of_one_quarter_lt hV
  have hvariance : 16 * (Real.sqrt V)⁻¹ / T ≤ 32 / T := by
    rw [div_le_div_iff_of_pos_right hT]
    nlinarith
  calc
    harperCDFDistance
          (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y j) t u)
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t u) ≤
        2 * ((2 * Real.pi)⁻¹ *
            (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
              (32 * T ^ 3 + T ^ 4) +
          16 * (Real.sqrt V)⁻¹ / T) := by
      simpa only [T, V, coe_harperLinearBlockVarianceNNReal] using! hbase
    _ ≤ 2 * (33 / T + 32 / T) := by gcongr
    _ = 130 / T := by ring
    _ = 130 / harperScheduledStrongComparisonFrequency j := rfl

/-! ## Relative cells with explicit variance bounds -/

/-- Once the universal Fejer budget is small enough, a moderate cell is
dominated by `1 + width` times its variance-matched Gaussian cell. -/
theorem eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian_of_variance :
    ∀ᶠ j : ℕ in atTop, ∀ y : ℕ, ∀ t u a : ℝ,
      (1 / 4 : ℝ) <
          harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u →
      harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u < (1 / 2 : ℝ) →
      |a| + 1 ≤ (1 / 4 : ℝ) *
          Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
      (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u).real
            (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
        (1 + harperScheduledRelativeIntervalWidth j) *
          (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t u).real
              (Ioc a (a + harperScheduledRelativeIntervalWidth j)) := by
  filter_upwards
    [eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass]
      with j hbudget
  intro y t u a hvarLower hvarUpper ha
  let rho := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let delta := harperScheduledRelativeIntervalWidth j
  have hdist : harperCDFDistance rho nu ≤
      130 / harperScheduledStrongComparisonFrequency j :=
    harperScheduledOffDiagonalCDFDistance_le_strong_of_variance_quarter
      hvarLower
  have habs : |rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta))| ≤ 2 * harperCDFDistance rho nu :=
    abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith [harperScheduledRelativeIntervalWidth_pos j])
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|a| + 1) ^ 2) ≤
        nu.real (Ioc a (a + delta)) := by
    dsimp only [nu, harperGaussianBlockLaw]
    exact gaussianReal_real_Ioc_ge_of_variance_quarter_half
      (v := harperLinearBlockVarianceNNReal y
        (harperScheduledPrimeBlock y j) t u)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvarLower.le)
      (by simpa only [coe_harperLinearBlockVarianceNNReal] using! hvarUpper.le)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using! harperScheduledRelativeIntervalWidth_le_one j)
  have hbudget' := hbudget a ha
  have herr : rho.real (Ioc a (a + delta)) -
      nu.real (Ioc a (a + delta)) ≤
        delta * nu.real (Ioc a (a + delta)) := by
    calc
      rho.real (Ioc a (a + delta)) - nu.real (Ioc a (a + delta)) ≤
          |rho.real (Ioc a (a + delta)) -
            nu.real (Ioc a (a + delta))| := le_abs_self _
      _ ≤ 2 * harperCDFDistance rho nu := habs
      _ ≤ 2 * (130 / harperScheduledStrongComparisonFrequency j) := by
        gcongr
      _ = 260 / harperScheduledStrongComparisonFrequency j := by ring
      _ ≤ delta * ((delta / 2) *
          Real.exp (-2 * (|a| + 1) ^ 2)) := by
        simpa only [delta] using! hbudget'
      _ ≤ delta * nu.real (Ioc a (a + delta)) := by
        gcongr
        exact (harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

/-! ## Product cells and barriers -/

/-- Every moderate off-diagonal product cell is dominated by its Gaussian
counterpart with the fixed factor `exp 2`, assuming the actual coordinate
variances lie in `(1/4,1/2)`. -/
theorem eventually_harperScheduledOffDiagonalModerateCoordinateCell_le_exp_two_mul_gaussian_of_variance :
    ∀ᶠ start : ℕ in atTop, ∀ n y : ℕ, ∀ t : ℝ,
      ∀ u : Fin n → ℝ,
      (∀ i : Fin n,
        (1 / 4 : ℝ) <
            harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ∧
          harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) <
            (1 / 2 : ℝ)) →
      ∀ z : Fin n → ℤ,
        (∀ i : Fin n,
          |(z i : ℝ) *
              harperScheduledRelativeIntervalWidth
                (start + (i : ℕ))| + 1 ≤
            (1 / 4 : ℝ) *
              Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ))) →
        (Measure.pi (fun i : Fin n ↦
          harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y
              (start + (i : ℕ))) t (u i))).real
            (harperLatticeIocCell
              (fun i : Fin n ↦
                harperScheduledRelativeIntervalWidth
                  (start + (i : ℕ))) z) ≤
          Real.exp 2 *
            (Measure.pi (fun i : Fin n ↦
              harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t (u i))).real
              (harperLatticeIocCell
                (fun i : Fin n ↦
                  harperScheduledRelativeIntervalWidth
                    (start + (i : ℕ))) z) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian_of_variance
  filter_upwards [eventually_ge_atTop J] with start hstart
  intro n y t u hvar z hz
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let nu : Fin n → Measure ℝ := fun i ↦
    harperGaussianBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let delta : Fin n → ℝ := fun i ↦
    harperScheduledRelativeIntervalWidth (start + (i : ℕ))
  let C : Fin n → ℝ := fun i ↦ 1 + delta i
  have hcoord (i : Fin n) :
      (rho i).real (Ioc ((z i : ℝ) * delta i)
        ((z i : ℝ) * delta i + delta i)) ≤
        C i * (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) := by
    exact hJ (start + (i : ℕ))
      (hstart.trans (Nat.le_add_right start (i : ℕ))) y t (u i)
      ((z i : ℝ) * delta i) (hvar i).1 (hvar i).2
      (by simpa only [delta] using! hz i)
  have hprod := measureReal_pi_coordinateCell_le_prod_mul rho nu C
    (fun i ↦ (z i : ℝ) * delta i) delta hcoord
  have hCprod : (∏ i, C i) ≤ Real.exp 2 := by
    simpa only [C, delta] using!
      prod_one_add_harperScheduledRelativeIntervalWidth_le_exp_two start n
  calc
    (Measure.pi rho).real (harperLatticeIocCell delta z) ≤
        (∏ i, C i) *
          (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      simpa only [harperLatticeIocCell] using! hprod
    _ ≤ Real.exp 2 *
        (Measure.pi nu).real (harperLatticeIocCell delta z) := by
      exact mul_le_mul_of_nonneg_right hCprod (by positivity)

/-- Finite slicing of a variance-controlled off-diagonal product law. -/
theorem eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian_of_variance :
    ∀ᶠ start : ℕ in atTop, ∀ n y : ℕ, ∀ t : ℝ,
      ∀ u : Fin n → ℝ,
      (∀ i : Fin n,
        (1 / 4 : ℝ) <
            harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ∧
          harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) <
            (1 / 2 : ℝ)) →
      ∀ lower upper : Fin n → ℝ,
        (Measure.pi (fun i : Fin n ↦
          harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y
              (start + (i : ℕ))) t (u i))).real
            (harperPartialSumBarrierSet lower upper ∩
              harperCoordinateBox
                (harperScheduledModerateRadius start n)) ≤
          Real.exp 2 *
            (Measure.pi (fun i : Fin n ↦
              harperGaussianBlockLaw y
                (harperScheduledPrimeBlock y
                  (start + (i : ℕ))) t (u i))).real
              (harperExpandedPartialSumBarrierSet lower upper
                (harperScheduledRelativeCellWidth start n)) := by
  filter_upwards
    [eventually_harperScheduledOffDiagonalModerateCoordinateCell_le_exp_two_mul_gaussian_of_variance]
      with start hcell
  intro n y t u hvar lower upper
  apply measureReal_inter_barrier_box_le_expandedBarrier
    (P := Measure.pi (fun i : Fin n ↦
      harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)))
    (Q := Measure.pi (fun i : Fin n ↦
      harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)))
    (C := Real.exp 2) (by positivity)
    (delta := harperScheduledRelativeCellWidth start n)
    (R := harperScheduledModerateRadius start n)
    (lower := lower) (upper := upper)
    (harperScheduledRelativeCellWidth_pos start n)
  intro z hz
  have hmoderate : ∀ i : Fin n,
      |(z i : ℝ) *
          harperScheduledRelativeIntervalWidth (start + (i : ℕ))| + 1 ≤
        (1 / 4 : ℝ) *
          Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ)) := by
    intro i
    simpa only [harperScheduledRelativeCellWidth,
      harperScheduledModerateThreshold] using!
        abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
          hz i
  simpa only [harperScheduledRelativeCellWidth] using!
    hcell n y t u hvar z hmoderate

/-! ## The variance-explicit reverse-log ballot endpoint -/

/-- The entire Gaussian walk part of the argument, with no height-window or
eventual arithmetic hypothesis. -/
theorem harperScheduledOffDiagonalGaussianWalk_expandedReverseLogBarrier_probability_le_of_variance
    {y start n : ℕ} (hn : 0 < n) (t : ℝ) (u : Fin n → ℝ)
    (hvar : ∀ i : Fin n,
      (1 / 4 : ℝ) <
          harperLinearBlockVariance y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ∧
        harperLinearBlockVariance y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) <
          (1 / 2 : ℝ))
    {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (lower : Fin n → ℝ) :
    (harperScheduledOffDiagonalGaussianProductMeasure
      y start n t u).real
        (harperExpandedPartialSumBarrierSet lower
          (harperNormalizedReverseLogBarrier n x c)
          (harperScheduledRelativeCellWidth start n)) ≤
      64 * (x + 4) / Real.sqrt (n : ℝ) := by
  have hvariance : ∀ i : Fin n,
      (1 / 4 : ℝ≥0) ≤
          harperScheduledOffDiagonalGaussianVariance y start n t u i ∧
        harperScheduledOffDiagonalGaussianVariance y start n t u i ≤
          (1 / 2 : ℝ≥0) := by
    intro i
    constructor
    · exact_mod_cast (hvar i).1.le
    · exact_mod_cast (hvar i).2.le
  have hbarrier : ∀ k : Fin n,
      harperNormalizedReverseLogBarrier n x c k +
          harperCumulativeCellWidth
            (harperScheduledRelativeCellWidth start n) k ≤ x + 2 := by
    intro k
    have hreverse := harperNormalizedReverseLogBarrier_le n x hc k
    have hwidth := harperCumulativeScheduledRelativeCellWidth_le_two start n k
    linarith
  have hsubset :
      harperExpandedPartialSumBarrierSet lower
          (harperNormalizedReverseLogBarrier n x c)
          (harperScheduledRelativeCellWidth start n) ⊆
        gaussianWalkSurvivalSet n (x + 2) :=
    harperExpandedPartialSumBarrierSet_subset_gaussianWalkSurvivalSet
      (lower := lower) hbarrier
  have hwalk := gaussianVarianceWalk_quarter_half_probability_le_fin
    n hn (harperScheduledOffDiagonalGaussianVariance y start n t u)
      (by linarith : 0 ≤ x + 2)
      (fun i ↦ (hvariance i).1) (fun i ↦ (hvariance i).2)
  calc
    (harperScheduledOffDiagonalGaussianProductMeasure
        y start n t u).real
          (harperExpandedPartialSumBarrierSet lower
            (harperNormalizedReverseLogBarrier n x c)
            (harperScheduledRelativeCellWidth start n)) ≤
        (harperScheduledOffDiagonalGaussianProductMeasure
          y start n t u).real (gaussianWalkSurvivalSet n (x + 2)) :=
      measureReal_mono hsubset
    _ ≤ 64 * (x + 2 + 2) / Real.sqrt (n : ℝ) := by
      simpa only [harperScheduledOffDiagonalGaussianProductMeasure] using! hwalk
    _ = 64 * (x + 4) / Real.sqrt (n : ℝ) := by ring

/-- Variance-explicit moderate-box reverse-log probability.  Its eventual
threshold is universal and independent of every vertical cutoff. -/
theorem eventually_harperScheduledOffDiagonalModerateBoxReverseLogBarrier_probability_le_of_variance :
    ∀ᶠ start : ℕ in atTop, ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      ∀ t : ℝ, ∀ u : Fin n → ℝ,
      (∀ i : Fin n,
        (1 / 4 : ℝ) <
            harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ∧
          harperLinearBlockVariance y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) <
            (1 / 2 : ℝ)) →
      ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
        (Measure.pi (fun i : Fin n ↦
          harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y
              (start + (i : ℕ))) t (u i))).real
            (harperPartialSumBarrierSet lower
                (harperNormalizedReverseLogBarrier n x c) ∩
              harperCoordinateBox
                (harperScheduledModerateRadius start n)) ≤
          Real.exp 2 *
            (64 * (x + 4) / Real.sqrt (n : ℝ)) := by
  filter_upwards
    [eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian_of_variance]
      with start hslice
  intro n hn y t u hvar x c hx hc lower
  have hslice' := hslice n y t u hvar lower
    (harperNormalizedReverseLogBarrier n x c)
  have hwalk :=
    harperScheduledOffDiagonalGaussianWalk_expandedReverseLogBarrier_probability_le_of_variance
      hn t u hvar hx hc lower
  have hgaussian :
      (Measure.pi (fun i : Fin n ↦
        harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y
            (start + (i : ℕ))) t (u i))).real
        (harperExpandedPartialSumBarrierSet lower
          (harperNormalizedReverseLogBarrier n x c)
          (harperScheduledRelativeCellWidth start n)) ≤
        64 * (x + 4) / Real.sqrt (n : ℝ) := by
    simpa only [harperScheduledOffDiagonalGaussianProductMeasure,
      harperScheduledOffDiagonalGaussianVariance,
      harperGaussianBlockLaw] using! hwalk
  exact hslice'.trans
    (mul_le_mul_of_nonneg_left hgaussian (by positivity))

end
end Problem520
end Erdos
