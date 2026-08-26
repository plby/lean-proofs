import ErdosProblems.Erdos520.HarperCentralBandMoments
import ErdosProblems.Erdos520.HarperVarianceExplicitBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos
namespace Problem520

noncomputable section

/-!
# Gaussian comparison and ballot bounds on shrinking central bands

The arithmetic input is now explicit: after the `J + d` shift, each actual
scheduled-block variance lies in `(1/4,1/2)`.  The variance-explicit CDF,
finite-slicing, and Gaussian-ballot theorems then apply with universal
constants and no residual height-window hypothesis.
-/

/-- Central-band specialization of the variance-explicit one-block CDF
comparison. -/
theorem exists_harperScheduledCentralBandCDFDistance_le_strong :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                harperCDFDistance
                    (harperCenteredLinearBlockLaw y
                      (harperScheduledPrimeBlock y j) t u)
                    (harperGaussianBlockLaw y
                      (harperScheduledPrimeBlock y j) t u) ≤
                  130 / harperScheduledStrongComparisonFrequency j := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half
  refine ⟨J, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale
  exact harperScheduledOffDiagonalCDFDistance_le_strong_of_variance_quarter
    (hJ d j y hj hy t htLower htUpper u hscale).1

/-- Central-band relative-cell replacement, with the same universal
summable loss as in the noncentral window. -/
theorem exists_harperScheduledCentralBandRelativeIntervalProbability_le_one_add_width_mul_gaussian :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : ℝ,
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                    (1 / 64 : ℝ) →
                ∀ a : ℝ,
                  |a| + 1 ≤ (1 / 4 : ℝ) *
                    Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
                  (harperCenteredLinearBlockLaw y
                    (harperScheduledPrimeBlock y j) t u).real
                      (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
                    (1 + harperScheduledRelativeIntervalWidth j) *
                      (harperGaussianBlockLaw y
                        (harperScheduledPrimeBlock y j) t u).real
                          (Ioc a
                            (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half
  obtain ⟨Jcell, hJcell⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian_of_variance
  refine ⟨max Jvar Jcell, ?_⟩
  intro d j y hj hy t htLower htUpper u hscale a ha
  have hvar := hJvar d j y (by omega) hy t htLower htUpper u hscale
  exact hJcell j (by omega) y t u a hvar.1 hvar.2 ha

/-- Every coordinate variance in a central-band scheduled path lies in the
uniform Gaussian window.  The threshold is independent of the path length. -/
theorem exists_harperScheduledCentralBandVarianceVector_quarter_half :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : Fin n → ℝ,
              (∀ i : Fin n,
                |u i - t| *
                    Real.log (harperBlockEndpoint
                      (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
                ∀ i : Fin n,
                  (1 / 4 : ℝ) <
                      harperLinearBlockVariance y
                        (harperScheduledPrimeBlock y
                          (start + (i : ℕ))) t (u i) ∧
                    harperLinearBlockVariance y
                      (harperScheduledPrimeBlock y
                        (start + (i : ℕ))) t (u i) < (1 / 2 : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledCentralBandOffDiagonalVariance_quarter_half
  refine ⟨J, ?_⟩
  intro d start hstart n y hy t htLower htUpper u hscale i
  have hindex : J + d ≤ start + (i : ℕ) := by omega
  have hendpoint :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  exact hJ d (start + (i : ℕ)) y hindex hendpoint
    t htLower htUpper (u i) (hscale i)

/-- Variance-explicit finite slicing specialized to a central band. -/
theorem exists_harperScheduledCentralBandModerateBoxBarrierProbability_le_exp_two_mul_gaussian :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ u : Fin n → ℝ,
              (∀ i : Fin n,
                |u i - t| *
                    Real.log (harperBlockEndpoint
                      (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
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
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledCentralBandVarianceVector_quarter_half
  obtain ⟨Jslice, hJslice⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian_of_variance
  refine ⟨max Jvar Jslice, ?_⟩
  intro d start hstart n y hy t htLower htUpper u hscale lower upper
  have hvar := hJvar d start (by omega) n y hy t htLower htUpper u hscale
  exact hJslice start (by omega) n y t u hvar lower upper

/-- The expanded reverse-log barrier has the universal Gaussian ballot
bound on every central band. -/
theorem exists_harperScheduledCentralBandGaussianWalk_expandedReverseLogBarrier_probability_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d →
              ∀ u : Fin n → ℝ,
                (∀ i : Fin n,
                  |u i - t| *
                      Real.log (harperBlockEndpoint
                        (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
                  ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
                    (harperScheduledOffDiagonalGaussianProductMeasure
                      y start n t u).real
                        (harperExpandedPartialSumBarrierSet lower
                          (harperNormalizedReverseLogBarrier n x c)
                          (harperScheduledRelativeCellWidth start n)) ≤
                      64 * (x + 4) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨J, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have hvar := hJ d start hstart n y hy t htLower htUpper u hscale
  exact
    harperScheduledOffDiagonalGaussianWalk_expandedReverseLogBarrier_probability_le_of_variance
      hn t u hvar hx hc lower

/-- Unconditional central-band tilted-event endpoint: after the explicit
`J + d` shift, the moderate centered Harper path obeys the normalized
reverse-log upper barrier with probability `O((x+1)/sqrt n)`, uniformly in
the band depth and prefix length. -/
theorem exists_harperScheduledCentralBandModerateBoxReverseLogBarrier_probability_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d →
              ∀ u : Fin n → ℝ,
                (∀ i : Fin n,
                  |u i - t| *
                      Real.log (harperBlockEndpoint
                        (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
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
  obtain ⟨Jslice, hJslice⟩ :=
    exists_harperScheduledCentralBandModerateBoxBarrierProbability_le_exp_two_mul_gaussian
  obtain ⟨Jwalk, hJwalk⟩ :=
    exists_harperScheduledCentralBandGaussianWalk_expandedReverseLogBarrier_probability_le
  refine ⟨max Jslice Jwalk, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have hslice := hJslice d start (by omega) n y hy t htLower htUpper
    u hscale lower (harperNormalizedReverseLogBarrier n x c)
  have hwalk := hJwalk d start (by omega) n hn y hy t htLower htUpper
    u hscale x c hx hc lower
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
  exact hslice.trans
    (mul_le_mul_of_nonneg_left hgaussian (by positivity))

end
end Problem520
end Erdos
