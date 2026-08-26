import ErdosProblems.Erdos520.HarperScheduledSummableErrors
import ErdosProblems.Erdos520.HarperScheduledOffDiagonal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Scheduled moments on shrinking central bands

On the `d`-th central band the tilt height has size `2^-d`.  The Abel
boundary term in the prime oscillation estimate therefore loses `2^d`.
Starting the scheduled blocks at `J + d` pays for that loss geometrically.
The resulting variance and logarithmic-drift windows are uniform in `d`,
the ambient prime cutoff, and the number of later blocks.
-/

/-- After a fixed extra shift, the second-harmonic prime mass is uniformly
smaller than `10^-3` on every shrinking central band. -/
theorem exists_harperScheduledCentralBandOscillation_le_milli :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            |harperScheduledOscillationMass y j (2 * t)| ≤
              (1 / 1000 : ℝ) := by
  obtain ⟨c, hc, C, hC, Josc, hosc⟩ :=
    exists_harperScheduledDyadicOscillationBounds
  have hthetaTendsto : Tendsto
      (harperScheduledThetaEnvelope c C) atTop (𝓝 0) :=
    (summable_harperScheduledThetaEnvelope hc hC.le).tendsto_atTop_zero
  have hthetaEventually : ∀ᶠ j : ℕ in atTop,
      harperScheduledThetaEnvelope c C j < (1 / 14000 : ℝ) :=
    (tendsto_order.mp hthetaTendsto).2 (1 / 14000 : ℝ) (by norm_num)
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1 hthetaEventually
  let J := max Josc (max 14 Jtheta)
  refine ⟨J, ?_⟩
  intro d j y hj hy t htLower htUpper
  have hjOsc : Josc + d ≤ j := by
    have : Josc ≤ J := le_max_left _ _
    omega
  have hjTheta : Jtheta ≤ j := by
    have : Jtheta ≤ J :=
      (le_max_right 14 Jtheta).trans (le_max_right Josc (max 14 Jtheta))
    omega
  have hjd : d ≤ j := by omega
  have hgap : 14 ≤ j - d := by
    have hfourteen : 14 ≤ J :=
      (le_max_left 14 Jtheta).trans (le_max_right Josc (max 14 Jtheta))
    omega
  have htUpperOne : |t| ≤ 1 :=
    htUpper.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hraw := hosc d j y hjOsc hy t t htLower htUpperOne (by simp)
  have hboundary := harperScheduledDyadicBoundary_le_geometric hjd
  have hpow :
      (1 / 2 : ℝ) ^ (j - d) ≤ (1 / 2 : ℝ) ^ 14 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap
  have hboundarySmall :
      4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j) ≤
        4 * (1 / 2 : ℝ) ^ 14 :=
    hboundary.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hthetaSmall :
      harperScheduledThetaEnvelope c C j < (1 / 14000 : ℝ) :=
    htheta j hjTheta
  have hnumerical :
      4 * (1 / 2 : ℝ) ^ 14 + 7 * (1 / 14000 : ℝ) <
        (1 / 1000 : ℝ) := by norm_num
  apply le_of_lt
  calc
    |harperScheduledOscillationMass y j (2 * t)| ≤
        harperScheduledDyadicOscillationEnvelope d c C j := hraw
    _ = 4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j) +
          7 * harperScheduledThetaEnvelope c C j := rfl
    _ < 4 * (1 / 2 : ℝ) ^ 14 + 7 * (1 / 14000 : ℝ) := by
      nlinarith
    _ < (1 / 1000 : ℝ) := hnumerical

/-- The diagonal centered variance stays in the sharp numerical window
needed by the local off-diagonal comparison, uniformly over central bands. -/
theorem exists_harperScheduledCentralBandDiagonalVariance_third_threeEighths :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            (1 / 3 : ℝ) <
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t t ∧
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t < 3 / 8 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    exists_harperScheduledCentralBandOscillation_le_milli
  obtain ⟨Jloss, hloss⟩ :=
    exists_eventually_harperScheduledVarianceBiasLoss_lt
      (by norm_num : (0 : ℝ) < 1 / 1000)
  refine ⟨max Jmass (max Josc Jloss), ?_⟩
  intro d j y hj hy t htLower htUpper
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + d ≤ j := by omega
  have hjloss : Jloss ≤ j := by omega
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let biasLoss : ℝ := harperScheduledVarianceBiasLoss y j t
  have hmassj : |reciprocalMass - Real.log 2| < (1 / 1000 : ℝ) :=
    hmass j hjmass y hy
  have hoscj : |oscillatoryMass| ≤ (1 / 1000 : ℝ) := by
    simpa only [oscillatoryMass, harperScheduledOscillationMass] using!
      hosc d j y hjosc hy t htLower htUpper
  have hlossj : biasLoss < (1 / 1000 : ℝ) :=
    hloss j hjloss y hy t
  have hlossNonneg : 0 ≤ biasLoss :=
    harperScheduledVarianceBiasLoss_nonneg y j t
  have hvarianceIdentity :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t t =
        (1 / 2 : ℝ) * (reciprocalMass + oscillatoryMass) - biasLoss := by
    rw [harperScheduledDiagonalVariance_eq_cosineMass_sub_biasLoss,
      sum_harperScheduledPrimeBlock_cos_sq_div]
  rw [hvarianceIdentity]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The diagonal quadratic logarithmic drift remains bounded away from zero
and infinity uniformly over all shrinking central bands. -/
theorem exists_harperScheduledCentralBandDiagonalMainMean_half_one :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            (1 / 2 : ℝ) <
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t t ∧
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t < 1 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    exists_harperScheduledCentralBandOscillation_le_milli
  obtain ⟨Jcorrection, hcorrection⟩ :=
    exists_eventually_harperScheduledDiagonalCorrection_lt
      (by norm_num : (0 : ℝ) < 1 / 1000)
  refine ⟨max Jmass (max Josc Jcorrection), ?_⟩
  intro d j y hj hy t htLower htUpper
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + d ≤ j := by omega
  have hjcorrection : Jcorrection ≤ j := by omega
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let correction : ℝ := harperScheduledDiagonalCorrection y j t
  have hmassj : |reciprocalMass - Real.log 2| < (1 / 1000 : ℝ) :=
    hmass j hjmass y hy
  have hoscj : |oscillatoryMass| ≤ (1 / 1000 : ℝ) := by
    simpa only [oscillatoryMass, harperScheduledOscillationMass] using!
      hosc d j y hjosc hy t htLower htUpper
  have hcorrectionj : correction < (1 / 1000 : ℝ) :=
    hcorrection j hjcorrection y hy t
  have hcorrectionNonneg : 0 ≤ correction :=
    harperScheduledDiagonalCorrection_nonneg y j t
  have hmeanIdentity :
      harperLogMainBlockMean y
          (harperScheduledPrimeBlock y j) t t =
        reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction := by
    simpa only [reciprocalMass, oscillatoryMass, correction,
      harperScheduledDiagonalCorrection] using!
        harperScheduledDiagonalMainMean_eq y j t
  rw [hmeanIdentity]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A local reciprocal-log displacement preserves the Gaussian variance
window on every central band. -/
theorem exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                (1 / 4 : ℝ) <
                    harperLinearBlockVariance y
                      (harperScheduledPrimeBlock y j) t u ∧
                  harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t u < 1 / 2 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_harperScheduledCentralBandDiagonalVariance_third_threeEighths
  refine ⟨max Jmass Jdiag, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale
  have hjmass : Jmass ≤ j := by omega
  have hjdiag : Jdiag + d ≤ j := by omega
  have hdiag := hJdiag d j y hjdiag hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j hjmass y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-- The same local displacement preserves a positive bounded quadratic
logarithmic drift on every central band. -/
theorem exists_harperScheduledCentralBandOffDiagonalMainMean_threeEighths_nineEighths :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                (3 / 8 : ℝ) <
                    harperLogMainBlockMean y
                      (harperScheduledPrimeBlock y j) t u ∧
                  harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t u < 9 / 8 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_harperScheduledCentralBandDiagonalMainMean_half_one
  refine ⟨max Jmass Jdiag, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale
  have hjmass : Jmass ≤ j := by omega
  have hjdiag : Jdiag + d ≤ j := by omega
  have hdiag := hJdiag d j y hjdiag hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j hjmass y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-- Uniform scheduled variance and drift bounds on all central dyadic bands. -/
theorem exists_harperScheduledCentralBandOffDiagonalMoment_bounds :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                ((1 / 4 : ℝ) <
                    harperLinearBlockVariance y
                      (harperScheduledPrimeBlock y j) t u ∧
                  harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t u < 1 / 2) ∧
                ((3 / 8 : ℝ) <
                    harperLogMainBlockMean y
                      (harperScheduledPrimeBlock y j) t u ∧
                  harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t u < 9 / 8) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half
  obtain ⟨Jmean, hJmean⟩ :=
    exists_harperScheduledCentralBandOffDiagonalMainMean_threeEighths_nineEighths
  refine ⟨max Jvar Jmean, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale
  exact ⟨
    hJvar d j y (by omega) hy t htLower htUpper u hscale,
    hJmean d j y (by omega) hy t htLower htUpper u hscale⟩

end Problem520
end Erdos
