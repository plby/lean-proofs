import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFactorizedLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperBoundaryProductAsymptotic
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperGoodDepthSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The final factorized bridge for the contracted upper-retained family

This module combines the two estimates which still retain the complete
future mean:

* affine freezing differs negligibly from the live delayed prefix;
* the live delayed prefix differs negligibly from the shallow
  good-cylinder prefix.

The second comparison uses the exact depth-slice decomposition.  Thus no
future event is discarded before the factorized error has been summed.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 3000000

/-- Named form of the factorized prefix-boundary estimate used by the
freezing squeeze. -/
theorem
    tendsto_annularContractedUpperRetainedGoodPrefixBoundaryProductSum_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (_heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedGoodPrefixBoundaryProductSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  simpa only [
    annularContractedUpperRetainedGoodPrefixBoundaryProductSum,
    annularContractedUpperRetainedGoodPrefixBoundaryEvent] using!
    tendsto_sum_gaussMeasure_real_goodPrefixBoundary_mul_norm_futureMean_zero
      hrho hε hεA hgrid k hr htime hsigned mode hmode

/-- The factorized affine-freezing error tends to zero.  The phase and
endpoint errors are summed with the complete future mean still attached;
the endpoint part is precisely the factorized boundary-product estimate. -/
theorem
    tendsto_annularContractedUpperRetainedAffineFactorizedMeanSum_sub_livePrefix_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedAffineFactorizedMeanSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedLivePrefixFactorizedMeanSum
              ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let phase : ℕ → ℝ := fun N ↦
    ∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      annularContractedUpperRetainedPhaseFreezingMajorant
        eta rho N k hr mode hmode p
  let boundary : ℕ → ℝ := fun N ↦
    annularContractedUpperRetainedGoodPrefixBoundaryProductSum
      ε A eta rho N k hr mode hmode
  have hphase : Tendsto phase atTop (nhds 0) := by
    simpa only [phase] using!
      tendsto_sum_annularContractedUpperRetainedPhaseFreezingMajorant_zero
        hrho hgrid k hr htime mode hmode
  have hboundary : Tendsto boundary atTop (nhds 0) := by
    simpa only [boundary] using!
      tendsto_annularContractedUpperRetainedGoodPrefixBoundaryProductSum_zero
        hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hmajor :
      Tendsto
        (fun N : ℕ ↦
          (2 * Real.log 2) * (phase N + boundary N))
        atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using!
      (tendsto_const_nhds.mul (hphase.add hboundary) :
        Tendsto
          (fun N : ℕ ↦
            (2 * Real.log 2) * (phase N + boundary N))
          atTop (nhds ((2 * Real.log 2) * (0 + 0))))
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N :=
    eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    have hlogTwoA :
        ∀ᶠ N : ℕ in atTop,
          2 * A < Real.log (N : ℝ) :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
    filter_upwards
      [hlogTwoA,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N htwoA hlog
    exact (div_lt_iff₀ hlog).2 (by linarith)
  have hmargin :
      ∀ᶠ N : ℕ in atTop,
        upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ) ≤
          eta * Real.log (N : ℝ) :=
    eventually_upperGoodTransferDenominatorTolerance_mul_ambient_le_margin
      heta hrho
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (by
      filter_upwards [hN, hW, hsmall, hmargin] with
        N hN' hW' hsmall' hmargin'
      simpa only [phase, boundary] using!
        norm_affineFactorizedMeanSum_sub_livePrefix_le
          hε hεA hgrid k htime hsigned hr mode hmode
          hN' hW' hsmall' hmargin')
    hmajor

/-- The delayed live-prefix factorized sum and the shallow cylinder sum
have the same limit.  The finite comparison is exactly the
shallow-minus-delayed good-depth slice, multiplied by its original future
mean. -/
theorem
    tendsto_annularContractedUpperRetainedLivePrefixFactorizedMeanSum_sub_shallow_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedLivePrefixFactorizedMeanSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedShallowFactorizedMeanSum
              ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hslice :=
    tendsto_sum_norm_annularContractedUpperRetainedGoodDepthSliceIntegral_mul_futureMean_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N :=
    eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hDeltaUpper :
      upperGoodTransferDenominatorTolerance eta rho ≤
        upperRetainedShallowDenominatorTolerance rho :=
    upperGoodTransferDenominatorTolerance_le_rhoSixth hrho.le
  have hstandard :=
    eventually_upperRetainedShallowUniformExponent_le_neg_log hrho
  have hexponent :
      ∀ᶠ N : ℕ in atTop,
        upperRetainedShallowUniformExponent rho
            (upperGoodTransferDenominatorTolerance eta rho) N ≤ 0 := by
    filter_upwards
      [hstandard,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hstandard' hlog
    calc
      upperRetainedShallowUniformExponent rho
          (upperGoodTransferDenominatorTolerance eta rho) N ≤
        upperRetainedShallowUniformExponent rho
          (upperRetainedShallowDenominatorTolerance rho) N :=
        upperRetainedShallowUniformExponent_mono_tolerance hDeltaUpper
      _ ≤ -(rho / 4) * Real.log (N : ℝ) := hstandard'
      _ ≤ 0 := by nlinarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (by
      filter_upwards [hN, hW, hexponent] with
        N hN' hW' hexponent'
      exact
        norm_annularContractedUpperRetainedLivePrefixFactorizedMeanSum_sub_shallow_le
          heta hrho hgrid k htime hr mode hmode
          hN' hW' hexponent')
    hslice

/-- Final factorized bridge: affine freezing and the shallow
good-cylinder expression have the same limit. -/
theorem
    tendsto_annularContractedUpperRetainedAffineFactorizedMeanSum_sub_shallow_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedAffineFactorizedMeanSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedShallowFactorizedMeanSum
              ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have haffine :=
    tendsto_annularContractedUpperRetainedAffineFactorizedMeanSum_sub_livePrefix_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hlive :=
    tendsto_annularContractedUpperRetainedLivePrefixFactorizedMeanSum_sub_shallow_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  convert! haffine.add hlive using 1
  · funext N
    ring
  · norm_num

end

end Erdos1002
