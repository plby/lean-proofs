import ErdosProblems.Erdos520.HarperGaussianEnvelopeMixture
import ErdosProblems.Erdos520.HarperGaussianLogBallot
import ErdosProblems.Erdos520.HarperTiltedLargeCoordinate
import ErdosProblems.Erdos520.HarperCentralPositiveLogCells
import ErdosProblems.Erdos520.HarperMovingHeightPositiveLogCells
import ErdosProblems.Erdos520.HarperPositiveLogRestrictedRecursion
import ErdosProblems.Erdos520.HarperScheduledGaussianSlicing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Unconditional tilted positive-log ballot estimate

This is the actual-law endpoint.  The local limit estimate controls moderate
cells, a variance-one Gaussian controls every remaining cell, and the
coordinatewise alternatives are expanded into one finite Gaussian mixture.
Global lattice slicing introduces no truncation error.  Every mixture
component has variances in `[1/4,1]`, so the sharp positive-log Gaussian
ballot theorem retains the full `1 / sqrt n` decay.
-/

/-- The explicit probability budget for the positive-log tilted witness.
The `+2` in the sliced barrier becomes `x + 3` in the Gaussian theorem's
`x + 1` numerator. -/
noncomputable def harperTiltedPositiveLogProbabilityBound
    (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp 4 *
    (44000000 * (x + 3) / Real.sqrt (n : ℝ))

theorem harperTiltedPositiveLogProbabilityBound_nonneg
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ harperTiltedPositiveLogProbabilityBound n x := by
  unfold harperTiltedPositiveLogProbabilityBound
  positivity

/-- The cumulatively expanded prefix-log barrier lies below the same
positive-log barrier with its intercept increased by two. -/
theorem harperExpandedPrefixPositiveLogBarrier_subset
    {n : ℕ} (start : ℕ) (x : ℝ) (lower : Fin n → ℝ) :
    harperExpandedPartialSumBarrierSet lower
        (harperPrefixPositiveLogBarrier x)
        (harperScheduledRelativeCellWidth start n) ⊆
      gaussianWalkTimeBarrierSet n 0
        (fun k ↦ x + 2 + 8 *
          Real.log ((k.val + 2 : ℕ) : ℝ)) := by
  simpa only [harperPrefixPositiveLogBarrier, add_assoc] using!
    harperExpandedLogBarrierSet_subset_gaussianWalkTimeBarrierSet
      lower (harperScheduledRelativeCellWidth start n) x 8 2
      (harperCumulativeScheduledRelativeCellWidth_le_two start n)

/-- Generic scheduled-mixture transfer used by both the noncentral and
shrinking central bands. -/
theorem measureReal_pi_prefixPositiveLogBarrier_le_of_gaussianMixtureCell
    {n : ℕ} (start : ℕ) (hn : 0 < n)
    (rho : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (rho i)]
    (variance : Fin n → ℝ≥0)
    (hvariance : ∀ i,
      (1 / 4 : ℝ≥0) ≤ variance i ∧ variance i ≤ (1 / 2 : ℝ≥0))
    (hcoord : ∀ z : Fin n → ℤ, ∀ i : Fin n,
      (rho i).real
          (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
            ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
              harperScheduledRelativeCellWidth start n i)) ≤
        (1 + harperScheduledRelativeIntervalWidth
              (start + (i : ℕ))) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)) +
          harperScheduledRelativeIntervalWidth (start + (i : ℕ)) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)))
    (x : ℝ) (hx : 0 ≤ x) (lower : Fin n → ℝ) :
    (Measure.pi rho).real
        (harperPartialSumBarrierSet lower
          (harperPrefixPositiveLogBarrier x)) ≤
      harperTiltedPositiveLogProbabilityBound n x := by
  let widthNN : Fin n → ℝ≥0 := fun i ↦
    ⟨harperScheduledRelativeIntervalWidth (start + (i : ℕ)),
      (harperScheduledRelativeIntervalWidth_pos _).le⟩
  let delta : Fin n → ℝ := harperScheduledRelativeCellWidth start n
  let expanded : Set (Fin n → ℝ) :=
    harperExpandedPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x) delta
  have hcoord' (z : Fin n → ℤ) (i : Fin n) :
      (rho i).real
          (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) ≤
        (1 + (widthNN i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i)) +
          (widthNN i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i)) := by
    simpa only [widthNN, delta, NNReal.coe_mk] using! hcoord z i
  have hslice :
      (Measure.pi rho).real
          (harperPartialSumBarrierSet lower
            (harperPrefixPositiveLogBarrier x)) ≤
        (harperGaussianEnvelopeMixture variance widthNN).real expanded := by
    simpa only [expanded, delta] using!
      measureReal_pi_barrier_le_expandedBarrier_gaussianEnvelope
        rho variance widthNN
        (delta := delta) (lower := lower)
        (upper := harperPrefixPositiveLogBarrier x)
        (fun i ↦ by
          simpa only [delta] using!
            harperScheduledRelativeCellWidth_pos start n i)
        hcoord'
  let B : ℝ := 44000000 * (x + 3) / Real.sqrt (n : ℝ)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hcomponent (s : Finset (Fin n)) :
      (harperGaussianEnvelopeComponent variance s).real expanded ≤ B := by
    let selected : Fin n → ℝ≥0 :=
      harperGaussianEnvelopeVariance variance s
    have hselected (i : Fin n) :
        (1 / 4 : ℝ≥0) ≤ selected i ∧ selected i ≤ (1 : ℝ≥0) := by
      exact harperGaussianEnvelopeVariance_mem variance s
        (fun j ↦ (hvariance j).1)
        (fun j ↦ (hvariance j).2.trans (by norm_num)) i
    have hsubset : expanded ⊆
        gaussianWalkTimeBarrierSet n 0
          (fun k ↦ x + 2 + 8 *
            Real.log ((k.val + 2 : ℕ) : ℝ)) := by
      simpa only [expanded, delta] using!
        harperExpandedPrefixPositiveLogBarrier_subset start x lower
    have hgaussian :=
      gaussianVarianceWalk_quarter_one_positiveLogBarrier_probability_le_fin
        n hn selected (x := x + 2) (by linarith)
        (fun i ↦ (hselected i).1) (fun i ↦ (hselected i).2)
    calc
      (harperGaussianEnvelopeComponent variance s).real expanded ≤
          (harperGaussianEnvelopeComponent variance s).real
            (gaussianWalkTimeBarrierSet n 0
              (fun k ↦ x + 2 + 8 *
                Real.log ((k.val + 2 : ℕ) : ℝ))) :=
        measureReal_mono hsubset
      _ ≤ B := by
        change (Measure.pi (fun i : Fin n ↦ gaussianReal 0
          (selected i))).real
            (gaussianWalkTimeBarrierSet n 0
              (fun k ↦ x + 2 + 8 *
                Real.log ((k.val + 2 : ℕ) : ℝ))) ≤ B
        dsimp only [B]
        convert! hgaussian using 1 <;> ring
  have hmixture :
      (harperGaussianEnvelopeMixture variance widthNN).real expanded ≤
        Real.exp 4 * B := by
    simpa only [widthNN] using!
      measureReal_harperScheduledGaussianEnvelopeMixture_le_exp_four_mul
        start variance expanded B hB hcomponent
  simpa only [B, harperTiltedPositiveLogProbabilityBound] using!
    hslice.trans hmixture

/-- Product-law form of the unconditional positive-log estimate.  The
evaluation height may vary by coordinate, subject only to the standard
scheduled off-diagonal condition. -/
theorem
    exists_eventually_harperScheduledOffDiagonalPositiveLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ, harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x : ℝ, 0 ≤ x → ∀ lower : Fin n → ℝ,
              (Measure.pi (fun i : Fin n ↦
                harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y (start + (i : ℕ)))
                    t (u i))).real
                  (harperPartialSumBarrierSet lower
                    (harperPrefixPositiveLogBarrier x)) ≤
                harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨Jcell, hJcell⟩ :=
    exists_eventually_harperScheduledOffDiagonalGlobalCellProbability_le_gaussianMixture M
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledOffDiagonalGaussianVariance_quarter_half M
  refine ⟨max Jcell Jvar, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale x hx lower
  have hstartCell : Jcell ≤ start :=
    (le_max_left Jcell Jvar).trans hstart
  have hstartVar : Jvar ≤ start :=
    (le_max_right Jcell Jvar).trans hstart
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let variance : Fin n → ℝ≥0 :=
    harperScheduledOffDiagonalGaussianVariance y start n t u
  let widthNN : Fin n → ℝ≥0 := fun i ↦
    ⟨harperScheduledRelativeIntervalWidth (start + (i : ℕ)),
      (harperScheduledRelativeIntervalWidth_pos _).le⟩
  let delta : Fin n → ℝ := harperScheduledRelativeCellWidth start n
  let expanded : Set (Fin n → ℝ) :=
    harperExpandedPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x) delta
  have hendpoint (i : Fin n) :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (z : Fin n → ℤ) (i : Fin n) :
      (rho i).real
          (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) ≤
        (1 + (widthNN i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i)) +
          (widthNN i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i)) := by
    have hiStart : Jcell ≤ start + (i : ℕ) := by omega
    have h := hJcell (start + (i : ℕ)) hiStart y (hendpoint i)
      t htLower htUpper (u i) (hscale i)
      ((z i : ℝ) * delta i)
    simpa only [rho, variance, widthNN, delta,
      harperScheduledRelativeCellWidth,
      harperScheduledOffDiagonalGaussianVariance,
      harperGaussianBlockLaw, NNReal.coe_mk] using! h
  have hslice :
      (Measure.pi rho).real
          (harperPartialSumBarrierSet lower
            (harperPrefixPositiveLogBarrier x)) ≤
        (harperGaussianEnvelopeMixture variance widthNN).real expanded := by
    simpa only [expanded, delta] using!
      measureReal_pi_barrier_le_expandedBarrier_gaussianEnvelope
        rho variance widthNN
        (delta := delta) (lower := lower)
        (upper := harperPrefixPositiveLogBarrier x)
        (fun i ↦ by
          simpa only [delta] using!
            harperScheduledRelativeCellWidth_pos start n i)
        hcoord
  have hvariance (i : Fin n) :
      (1 / 4 : ℝ≥0) ≤ variance i ∧ variance i ≤ (1 / 2 : ℝ≥0) := by
    exact hJvar start hstartVar n y hy t htLower htUpper u hscale i
  let B : ℝ := 44000000 * (x + 3) / Real.sqrt (n : ℝ)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hcomponent (s : Finset (Fin n)) :
      (harperGaussianEnvelopeComponent variance s).real expanded ≤ B := by
    let selected : Fin n → ℝ≥0 :=
      harperGaussianEnvelopeVariance variance s
    have hselected (i : Fin n) :
        (1 / 4 : ℝ≥0) ≤ selected i ∧ selected i ≤ (1 : ℝ≥0) := by
      exact harperGaussianEnvelopeVariance_mem variance s
        (fun j ↦ (hvariance j).1)
        (fun j ↦ (hvariance j).2.trans (by norm_num)) i
    have hsubset : expanded ⊆
        gaussianWalkTimeBarrierSet n 0
          (fun k ↦ x + 2 + 8 *
            Real.log ((k.val + 2 : ℕ) : ℝ)) := by
      simpa only [expanded, delta] using!
        harperExpandedPrefixPositiveLogBarrier_subset start x lower
    have hgaussian :=
      gaussianVarianceWalk_quarter_one_positiveLogBarrier_probability_le_fin
        n hn selected (x := x + 2) (by linarith)
        (fun i ↦ (hselected i).1) (fun i ↦ (hselected i).2)
    calc
      (harperGaussianEnvelopeComponent variance s).real expanded ≤
          (harperGaussianEnvelopeComponent variance s).real
            (gaussianWalkTimeBarrierSet n 0
              (fun k ↦ x + 2 + 8 *
                Real.log ((k.val + 2 : ℕ) : ℝ))) :=
        measureReal_mono hsubset
      _ ≤ B := by
        change (Measure.pi (fun i : Fin n ↦ gaussianReal 0
          (selected i))).real
            (gaussianWalkTimeBarrierSet n 0
              (fun k ↦ x + 2 + 8 *
                Real.log ((k.val + 2 : ℕ) : ℝ))) ≤ B
        dsimp only [B]
        convert! hgaussian using 1 <;> ring
  have hmixture :
      (harperGaussianEnvelopeMixture variance widthNN).real expanded ≤
        Real.exp 4 * B := by
    simpa only [widthNN] using!
      measureReal_harperScheduledGaussianEnvelopeMixture_le_exp_four_mul
        start variance expanded B hB hcomponent
  simpa only [rho, B, harperTiltedPositiveLogProbabilityBound] using!
    hslice.trans hmixture

/-- Moving-height product-law endpoint.  Unlike the fixed-window theorem
above, one absolute cutoff works simultaneously for every height cutoff
`M`; the dependence on `M` is isolated in the explicit logarithmic shift. -/
theorem
    exists_harperScheduledMovingHeightPositiveLogBarrier_probability_le :
    ∃ J : ℕ, ∀ M start : ℕ,
      J + Nat.clog 2 (M + 1) ≤ start →
        ∀ n : ℕ, 0 < n → ∀ y : ℕ,
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
              (∀ i : Fin n,
                |u i - t| *
                    Real.log (harperBlockEndpoint
                      (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
                ∀ x : ℝ, 0 ≤ x → ∀ lower : Fin n → ℝ,
                  (Measure.pi (fun i : Fin n ↦
                    harperCenteredLinearBlockLaw y
                      (harperScheduledPrimeBlock y
                        (start + (i : ℕ))) t (u i))).real
                      (harperPartialSumBarrierSet lower
                        (harperPrefixPositiveLogBarrier x)) ≤
                    harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨Jcell, hJcell⟩ :=
    exists_harperScheduledMovingHeightGlobalCellProbability_le_gaussianMixture
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledMovingHeightVarianceVector_quarter_half
  refine ⟨max Jcell Jvar, ?_⟩
  intro M start hstart n hn y hy t htLower htUpper u hscale x hx lower
  have hstartCell : Jcell + Nat.clog 2 (M + 1) ≤ start := by
    omega
  have hstartVar : Jvar + Nat.clog 2 (M + 1) ≤ start := by
    omega
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let variance : Fin n → ℝ≥0 :=
    harperScheduledOffDiagonalGaussianVariance y start n t u
  have hendpoint (i : Fin n) :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (z : Fin n → ℤ) (i : Fin n) :
      (rho i).real
          (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
            ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
              harperScheduledRelativeCellWidth start n i)) ≤
        (1 + harperScheduledRelativeIntervalWidth
              (start + (i : ℕ))) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)) +
          harperScheduledRelativeIntervalWidth (start + (i : ℕ)) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)) := by
    have h := hJcell M (start + (i : ℕ)) y (by omega)
      (hendpoint i) t htLower htUpper (u i) (hscale i)
      ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
    simpa only [rho, variance, harperScheduledRelativeCellWidth,
      harperScheduledOffDiagonalGaussianVariance,
      harperGaussianBlockLaw] using! h
  have hvariance (i : Fin n) :
      (1 / 4 : ℝ≥0) ≤ variance i ∧
        variance i ≤ (1 / 2 : ℝ≥0) := by
    have hv := hJvar M start n y hstartVar hy t htLower htUpper u hscale i
    constructor
    · change (1 / 4 : ℝ≥0) ≤
        harperLinearBlockVarianceNNReal y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
      exact_mod_cast hv.1.le
    · change harperLinearBlockVarianceNNReal y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ≤
        (1 / 2 : ℝ≥0)
      exact_mod_cast hv.2.le
  simpa only [rho] using!
    measureReal_pi_prefixPositiveLogBarrier_le_of_gaussianMixtureCell
      start hn rho variance hvariance hcoord x hx lower

/-- Shrinking-central-band product-law endpoint.  The only change from the
noncentral result is the explicit `J + d` scale shift supplied by the
central-band variance arithmetic. -/
theorem
    exists_harperScheduledCentralBandPositiveLogBarrier_probability_le :
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
                  ∀ x : ℝ, 0 ≤ x → ∀ lower : Fin n → ℝ,
                    (Measure.pi (fun i : Fin n ↦
                      harperCenteredLinearBlockLaw y
                        (harperScheduledPrimeBlock y
                          (start + (i : ℕ))) t (u i))).real
                        (harperPartialSumBarrierSet lower
                          (harperPrefixPositiveLogBarrier x)) ≤
                      harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨Jcell, hJcell⟩ :=
    exists_harperScheduledCentralBandGlobalCellProbability_le_gaussianMixture
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max Jcell Jvar, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper u hscale x hx lower
  have hstartCell : Jcell + d ≤ start := by omega
  have hstartVar : Jvar + d ≤ start := by omega
  let rho : Fin n → Measure ℝ := fun i ↦
    harperCenteredLinearBlockLaw y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
  let variance : Fin n → ℝ≥0 :=
    harperScheduledOffDiagonalGaussianVariance y start n t u
  have hendpoint (i : Fin n) :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (z : Fin n → ℤ) (i : Fin n) :
      (rho i).real
          (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
            ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
              harperScheduledRelativeCellWidth start n i)) ≤
        (1 + harperScheduledRelativeIntervalWidth
              (start + (i : ℕ))) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)) +
          harperScheduledRelativeIntervalWidth (start + (i : ℕ)) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
                ((z i : ℝ) * harperScheduledRelativeCellWidth start n i +
                  harperScheduledRelativeCellWidth start n i)) := by
    have h := hJcell d (start + (i : ℕ)) y (by omega)
      (hendpoint i) t htLower htUpper (u i) (hscale i)
      ((z i : ℝ) * harperScheduledRelativeCellWidth start n i)
    simpa only [rho, variance, harperScheduledRelativeCellWidth,
      harperScheduledOffDiagonalGaussianVariance,
      harperGaussianBlockLaw] using! h
  have hvariance (i : Fin n) :
      (1 / 4 : ℝ≥0) ≤ variance i ∧
        variance i ≤ (1 / 2 : ℝ≥0) := by
    have hv := hJvar d start hstartVar n y hy t htLower htUpper u hscale i
    constructor
    · change (1 / 4 : ℝ≥0) ≤
        harperLinearBlockVarianceNNReal y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)
      exact_mod_cast hv.1.le
    · change harperLinearBlockVarianceNNReal y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) ≤
        (1 / 2 : ℝ≥0)
      exact_mod_cast hv.2.le
  simpa only [rho] using!
    measureReal_pi_prefixPositiveLogBarrier_le_of_gaussianMixtureCell
      start hn rho variance hvariance hcoord x hx lower

/-- Literal tilted-cube form consumed by the restricted first-moment
recursion.  Every premise is structural or arithmetic; there is no abstract
probability hypothesis and no additive fixed tail error. -/
theorem exists_eventually_harperPrefixGoodPositiveLogWitness_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ, harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x : ℝ, 0 ≤ x →
          ∀ lower : Fin n → ℝ,
            (harperTiltedCubeLaw y t).real
                (harperPrefixGoodPositiveLogWitnessEvent
                  y start n t x lower) ≤
              harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalPositiveLogBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x hx lower
  let u : Fin n → ℝ := harperScheduledVerticalCheckpoint start n t
  have hscale : ∀ i : Fin n,
      |u i - t| *
          Real.log (harperBlockEndpoint
            (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ) := by
    exact harperScheduledVerticalCheckpoint_offDiagonalCondition start n t
  have hproduct := hJ start hstart n hn y hy t htLower htUpper
    u hscale x hx lower
  unfold harperPrefixGoodPositiveLogWitnessEvent
  rw [harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
    y start n t u
    (harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))
    (measurableSet_harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))]
  simpa only [u] using! hproduct

/-- Literal tilted-cube endpoint with one absolute cutoff for all growing
noncentral height windows. -/
theorem exists_harperMovingHeightPrefixGoodPositiveLogWitness_probability_le :
    ∃ J : ℕ, ∀ M start : ℕ,
      J + Nat.clog 2 (M + 1) ≤ start →
        ∀ n : ℕ, 0 < n → ∀ y : ℕ,
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x : ℝ, 0 ≤ x →
              ∀ lower : Fin n → ℝ,
                (harperTiltedCubeLaw y t).real
                    (harperPrefixGoodPositiveLogWitnessEvent
                      y start n t x lower) ≤
                  harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledMovingHeightPositiveLogBarrier_probability_le
  refine ⟨J, ?_⟩
  intro M start hstart n hn y hy t htLower htUpper x hx lower
  let u : Fin n → ℝ := harperScheduledVerticalCheckpoint start n t
  have hscale : ∀ i : Fin n,
      |u i - t| *
          Real.log (harperBlockEndpoint
            (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ) := by
    exact harperScheduledVerticalCheckpoint_offDiagonalCondition start n t
  have hproduct := hJ M start hstart n hn y hy t htLower htUpper
    u hscale x hx lower
  unfold harperPrefixGoodPositiveLogWitnessEvent
  rw [harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
    y start n t u
    (harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))
    (measurableSet_harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))]
  simpa only [u] using! hproduct

/-- Literal tilted-cube endpoint on every shrinking central shell. -/
theorem exists_harperCentralBandPrefixGoodPositiveLogWitness_probability_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d →
              ∀ x : ℝ, 0 ≤ x → ∀ lower : Fin n → ℝ,
                (harperTiltedCubeLaw y t).real
                    (harperPrefixGoodPositiveLogWitnessEvent
                      y start n t x lower) ≤
                  harperTiltedPositiveLogProbabilityBound n x := by
  obtain ⟨J, hJ⟩ :=
    exists_harperScheduledCentralBandPositiveLogBarrier_probability_le
  refine ⟨J, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper x hx lower
  let u : Fin n → ℝ := harperScheduledVerticalCheckpoint start n t
  have hscale : ∀ i : Fin n,
      |u i - t| *
          Real.log (harperBlockEndpoint
            (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ) := by
    exact harperScheduledVerticalCheckpoint_offDiagonalCondition start n t
  have hproduct := hJ d start hstart n hn y hy t htLower htUpper
    u hscale x hx lower
  unfold harperPrefixGoodPositiveLogWitnessEvent
  rw [harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
    y start n t u
    (harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))
    (measurableSet_harperPartialSumBarrierSet lower
      (harperPrefixPositiveLogBarrier x))]
  simpa only [u] using! hproduct

theorem harperExplicitPrefixPositiveLogOffset_nonneg
    (start M : ℕ) {B E D : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    0 ≤ harperExplicitPrefixPositiveLogOffset start M B E D := by
  unfold harperExplicitPrefixPositiveLogOffset
    harperExplicitPrefixEntropyBase
    harperExplicitPrefixEntropyCoefficient
    harperScheduledLogTaylorAllowance
  have hcoef : (1 : ℝ) ≤ ((4096 * M + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 4096 * M + 1 by omega)
  positivity

/-- The noncentral explicit positive-log recursion with its former abstract
probability premise fully instantiated by the actual tilted law.  One
absolute cutoff works simultaneously for all growing height windows. -/
theorem
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixPositiveLog_unconditional
    : ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, 1 ≤ |t|) → (∀ t ∈ I, |t| ≤ M) →
      ∀ B : ℝ, 0 ≤ B → ∀ q r : ℝ, 0 < q → q < r → r ≤ 1 →
        (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
          (harperExplicitMertensConstant *
            (volume.real I *
              harperTiltedPositiveLogProbabilityBound n
                (harperExplicitPrefixPositiveLogOffset start M B E D))) ^ q +
            Real.exp (-2 * B) ^ (1 - q / r) *
              (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
                (q / r) := by
  obtain ⟨E, hE, D, hD, Jrec, hrec⟩ :=
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixPositiveLog
  obtain ⟨Jprob, hprob⟩ :=
    exists_harperMovingHeightPrefixGoodPositiveLogWitness_probability_le
  refine ⟨E, hE, D, hD, max Jrec Jprob, ?_⟩
  intro M
  intro start n y hstart hn hyEndpoint hy I hI hIfinite
    htLower htUpper B hB q r hq hqr hr1
  have hstartRec : Jrec + Nat.clog 2 (M + 1) ≤ start :=
    by omega
  have hstartProb : Jprob + Nat.clog 2 (M + 1) ≤ start :=
    by omega
  let x : ℝ := harperExplicitPrefixPositiveLogOffset start M B E D
  let H : ℝ := harperTiltedPositiveLogProbabilityBound n x
  have hx : 0 ≤ x := by
    exact harperExplicitPrefixPositiveLogOffset_nonneg
      start M hB hE hD
  have hH : 0 ≤ H := by
    exact harperTiltedPositiveLogProbabilityBound_nonneg n hx
  have hprobability : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real
          (harperPrefixGoodPositiveLogWitnessEvent y start n t x
            (harperExplicitPrefixPositiveLogLowerBarrier
              y start n M B D t)) ≤ H := by
    intro t ht
    exact hprob M start hstartProb n hn y hyEndpoint t
      (htLower t ht) (htUpper t ht) x hx
      (harperExplicitPrefixPositiveLogLowerBarrier
        y start n M B D t)
  have hmain := hrec M start n y hstartRec hn hyEndpoint hy
    I hI hIfinite htLower htUpper B H hH
    (by simpa only [x] using! hprobability) q r hq hqr hr1
  simpa only [x, H] using! hmain

/-- The shrinking-central-shell positive-log recursion with its probability
premise fully discharged. -/
theorem
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixCentralPositiveLog_unconditional
    : ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ,
        J + d ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, (1 / 2 : ℝ) ^ (d + 1) < |t|) →
      (∀ t ∈ I, |t| ≤ (1 / 2 : ℝ) ^ d) →
      ∀ B : ℝ, 0 ≤ B → ∀ q r : ℝ, 0 < q → q < r → r ≤ 1 →
        (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
          (harperExplicitMertensConstant *
            (volume.real I *
              harperTiltedPositiveLogProbabilityBound n
                (harperExplicitPrefixPositiveLogOffset start 1 B E D))) ^ q +
            Real.exp (-2 * B) ^ (1 - q / r) *
              (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
                (q / r) := by
  obtain ⟨E, hE, D, hD, Jrec, hrec⟩ :=
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixCentralPositiveLog
  obtain ⟨Jprob, hprob⟩ :=
    exists_harperCentralBandPrefixGoodPositiveLogWitness_probability_le
  refine ⟨E, hE, D, hD, max Jrec Jprob, ?_⟩
  intro d start n y hstart hn hyEndpoint hy I hI hIfinite
    htLower htUpper B hB q r hq hqr hr1
  have hstartRec : Jrec + d ≤ start := by omega
  have hstartProb : Jprob + d ≤ start := by omega
  let x : ℝ := harperExplicitPrefixPositiveLogOffset start 1 B E D
  let H : ℝ := harperTiltedPositiveLogProbabilityBound n x
  have hx : 0 ≤ x := by
    exact harperExplicitPrefixPositiveLogOffset_nonneg
      start 1 hB hE hD
  have hH : 0 ≤ H := by
    exact harperTiltedPositiveLogProbabilityBound_nonneg n hx
  have hprobability : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real
          (harperPrefixGoodPositiveLogWitnessEvent y start n t x
            (harperExplicitPrefixPositiveLogLowerBarrier
              y start n 1 B D t)) ≤ H := by
    intro t ht
    exact hprob d start hstartProb n hn y hyEndpoint t
      (htLower t ht) (htUpper t ht) x hx
      (harperExplicitPrefixPositiveLogLowerBarrier
        y start n 1 B D t)
  have hmain := hrec d start n y hstartRec hn hyEndpoint hy
    I hI hIfinite htLower htUpper B H hH
    (by simpa only [x] using! hprobability) q r hq hqr hr1
  simpa only [x, H] using! hmain

end Problem520
end Erdos
