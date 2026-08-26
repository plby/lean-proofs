import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingPointwise
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperCovarianceAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform decay of the corrected upper freezing phase coefficient

The phase carrier in the delayed-prefix freezing estimate is stopped at
the actual last nonzero Fourier depth `s`.  This file records the exact
integer midpoint arithmetic which is essential for that choice.

Writing `H` for the ambient depth, `m = (H+s)/2` for the integer
midpoint, `G = ⌊W/2⌋` for the retained half-band, and
`O = ⌊G/2⌋` for the delayed-freezing offset, the freezing depth is
`b=m+O`.  Thus the exponential part of the phase error is

`log N + μ s - 2 μ b + 3 Δ H`.

For the literal tolerance `Δ = μ min(eta,rho)/8`, this is at most

`- μ rho H / 8 + 3 μ / 2`.

In particular, the estimate is uniform in the location of `s` and its
exponential decay absorbs the polynomial number of contracted tags.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperFreezingPhaseAsymptoticPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exponent obtained after combining the factor `N`, the center-depth
carrier bound, and the two denominator factors in the phase radius. -/
def annularContractedUpperRetainedPhaseExponent
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℝ :=
  Real.log (N : ℝ) +
      (annularContractedUpperRetainedCenterDepth p : ℝ) *
        gaussRoofMean -
    2 * (annularContractedUpperRetainedDelayedDepth p : ℝ) *
        gaussRoofMean +
    3 * upperGoodTransferDenominatorTolerance eta rho *
      (annularDepthAmbientSize N : ℝ)

/-- The two nested natural divisions used by the retained band lose at
most three integer units. -/
theorem annularMidpointBandWidth_le_four_freezingOffset_add_three
    (rho : ℝ) (N : ℕ) :
    annularMidpointBandWidth rho N ≤
      4 * annularUpperRetainedFreezingOffset rho N + 3 := by
  unfold annularUpperRetainedFreezingOffset
    annularUpperRetainedGap midpointPrefixFutureGap
  omega

/-- The natural midpoint loses at most one integer unit. -/
theorem ambient_add_center_le_two_split_add_one
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularDepthAmbientSize N +
        annularContractedUpperRetainedCenterDepth p ≤
      2 * annularUpperRetainedSplitDepth
          (annularContractedUpperRetainedToUpper p) + 1 := by
  let q := annularContractedUpperRetainedToUpper p
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  change
    annularDepthAmbientSize N + annularUpperRetainedTimes q s ≤
      2 * ((annularDepthAmbientSize N +
        annularUpperRetainedTimes q s) / 2) + 1
  omega

/-- The logarithmic scale is below the ambient-depth scale. -/
theorem log_natCast_le_ambient_sub_one_mul_gaussRoofMean
    {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N : ℝ) ≤
      ((annularDepthAmbientSize N : ℝ) - 1) * gaussRoofMean := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hceil :
      Real.log (N : ℝ) / gaussRoofMean ≤
        (gaussLogDepthEndpoint N 1 : ℝ) := by
    simpa only [gaussLogDepthEndpoint, one_mul] using!
      (Nat.le_ceil (Real.log (N : ℝ) / gaussRoofMean))
  have hmul :=
    mul_le_mul_of_nonneg_right hceil gaussRoofMean_pos.le
  have hmuNe : gaussRoofMean ≠ 0 := ne_of_gt gaussRoofMean_pos
  unfold annularDepthAmbientSize
  push_cast
  calc
    Real.log (N : ℝ) =
        (Real.log (N : ℝ) / gaussRoofMean) * gaussRoofMean := by
          field_simp
    _ ≤ (gaussLogDepthEndpoint N 1 : ℝ) * gaussRoofMean := hmul
    _ = (((gaussLogDepthEndpoint N 1 : ℕ) : ℝ) + 1 - 1) *
          gaussRoofMean := by ring

/-- Exact uniform negative margin for the corrected center-depth phase
exponent.  The literal `/8` in the tolerance is used here; replacing it
by the weaker `/6` bound would exhaust the available margin. -/
theorem annularContractedUpperRetainedPhaseExponent_le
    {eta rho : ℝ} (_hrho : 0 < rho)
    {N grid : ℕ} (hN : 1 ≤ N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedPhaseExponent
        eta rho N k hr mode hmode p ≤
      -(gaussRoofMean * rho *
          (annularDepthAmbientSize N : ℝ)) / 8 +
        3 * gaussRoofMean / 2 := by
  let H := annularDepthAmbientSize N
  let s := annularContractedUpperRetainedCenterDepth p
  let m :=
    annularUpperRetainedSplitDepth
      (annularContractedUpperRetainedToUpper p)
  let W := annularMidpointBandWidth rho N
  let O := annularUpperRetainedFreezingOffset rho N
  let Delta := upperGoodTransferDenominatorTolerance eta rho
  have hlog :
      Real.log (N : ℝ) ≤ ((H : ℝ) - 1) * gaussRoofMean := by
    simpa only [H] using!
      log_natCast_le_ambient_sub_one_mul_gaussRoofMean hN
  have hmidNat : H + s ≤ 2 * m + 1 := by
    simpa only [H, s, m] using!
      ambient_add_center_le_two_split_add_one p
  have hmid : (H : ℝ) + (s : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    exact_mod_cast hmidNat
  have hwidthNat : W ≤ 4 * O + 3 := by
    simpa only [W, O] using!
      annularMidpointBandWidth_le_four_freezingOffset_add_three rho N
  have hwidth : (W : ℝ) ≤ 4 * (O : ℝ) + 3 := by
    exact_mod_cast hwidthNat
  have hrhoH : rho * (H : ℝ) ≤ (W : ℝ) := by
    simpa only [W, H, annularMidpointBandWidth] using!
      (Nat.le_ceil (rho * (annularDepthAmbientSize N : ℝ)))
  have hDelta :
      Delta ≤ gaussRoofMean * rho / 8 := by
    unfold Delta upperGoodTransferDenominatorTolerance
    have hmin : min eta rho ≤ rho := min_le_right _ _
    have hmul :
        gaussRoofMean * min eta rho ≤ gaussRoofMean * rho :=
      mul_le_mul_of_nonneg_left hmin gaussRoofMean_pos.le
    nlinarith
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  have hDeltaH :
      3 * Delta * (H : ℝ) ≤
        3 * (gaussRoofMean * rho / 8) * (H : ℝ) := by
    gcongr
  have hmu : 0 < gaussRoofMean := gaussRoofMean_pos
  have hdelayed :
      annularContractedUpperRetainedDelayedDepth p = m + O := by
    rfl
  unfold annularContractedUpperRetainedPhaseExponent
  rw [hdelayed]
  dsimp only [H, s, m, W, O, Delta] at hlog hmid hwidth hrhoH hDeltaH ⊢
  push_cast
  nlinarith

/-! ## From the exponent to the literal phase majorant -/

/-- A fixed total absolute Fourier weight, summed over the finitely many
chronological orders. -/
def annularUpperRetainedTotalModeWeight
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ∑ z : GaussPrefixMixedOccurrence k,
      |(unflattenedAnnularFourierMode e (mode e)
        z.1 z.2 : ℝ)|

theorem annularUpperRetainedTotalModeWeight_nonneg
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) :
    0 ≤ annularUpperRetainedTotalModeWeight k mode := by
  unfold annularUpperRetainedTotalModeWeight
  exact Finset.sum_nonneg fun _e _he ↦
    Finset.sum_nonneg fun _z _hz ↦ abs_nonneg _

/-- The selected delayed-prefix weight is bounded by the preceding fixed
total weight. -/
theorem sum_abs_delayedPrefixMode_le_totalModeWeight
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    (∑ z : GaussPrefixMixedPrefixOccurrence N k
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p),
        |(unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1.1 z.1.2 : ℝ)|) ≤
      annularUpperRetainedTotalModeWeight k mode := by
  let weight : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    |(unflattenedAnnularFourierMode p.1 (mode p.1)
      z.1 z.2 : ℝ)|
  have hprefix :
      (∑ z : GaussPrefixMixedPrefixOccurrence N k
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p),
          weight z.1) ≤
        ∑ z : GaussPrefixMixedOccurrence k, weight z := by
    change
      (∑ z : {z : GaussPrefixMixedOccurrence k //
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) ≤
              annularContractedUpperRetainedDelayedDepth p},
        weight z.1) ≤
          ∑ z : GaussPrefixMixedOccurrence k, weight z
    rw [← Finset.sum_subtype
      (p := fun z : GaussPrefixMixedOccurrence k ↦
        ((annularContractedUpperRetainedRealization p).1
          z.1 z.2 : ℕ) ≤
            annularContractedUpperRetainedDelayedDepth p)
      ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
        (fun z ↦
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) ≤
              annularContractedUpperRetainedDelayedDepth p))
      (by intro z; simp) weight]
    exact Finset.sum_le_univ_sum_of_nonneg
      (fun z ↦ abs_nonneg
        (unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1 z.2 : ℝ))
  have horder :
      (∑ z : GaussPrefixMixedOccurrence k, weight z) ≤
        annularUpperRetainedTotalModeWeight k mode := by
    unfold annularUpperRetainedTotalModeWeight
    exact Finset.single_le_sum
      (fun e _he ↦
        Finset.sum_nonneg fun (z : GaussPrefixMixedOccurrence k) _hz ↦
          abs_nonneg
            (unflattenedAnnularFourierMode e (mode e)
              z.1 z.2 : ℝ))
      (Finset.mem_univ p.1)
  exact hprefix.trans horder

/-- Tuple-independent scalar which dominates the corrected phase
majorant. -/
def annularContractedUpperRetainedPhaseUniformMajorant
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) : ℝ :=
  4 * Real.pi * annularUpperRetainedTotalModeWeight k mode *
    Real.exp
      (-(gaussRoofMean * rho *
          (annularDepthAmbientSize N : ℝ)) / 8 +
        3 * gaussRoofMean / 2)

/-- The literal phase majorant is bounded by the uniform exponentially
decaying scalar. -/
theorem annularContractedUpperRetainedPhaseFreezingMajorant_le_uniform
    {eta rho : ℝ} (hrho : 0 < rho)
    {N grid : ℕ} (hN : 1 ≤ N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedPhaseFreezingMajorant
        eta rho N k hr mode hmode p ≤
      annularContractedUpperRetainedPhaseUniformMajorant
        rho N k mode := by
  let weight : ℝ :=
    ∑ z : GaussPrefixMixedPrefixOccurrence N k
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p),
      |(unflattenedAnnularFourierMode p.1 (mode p.1)
        z.1.1 z.1.2 : ℝ)|
  let exponent :=
    annularContractedUpperRetainedPhaseExponent
      eta rho N k hr mode hmode p
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hrewrite :
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p =
        4 * Real.pi * weight * Real.exp exponent := by
    dsimp only [weight, exponent]
    unfold annularContractedUpperRetainedPhaseFreezingMajorant
      annularContractedUpperRetainedPhaseExponent
    dsimp only
    have hexponent :
        Real.log (N : ℝ) +
              (annularContractedUpperRetainedCenterDepth p : ℝ) *
                gaussRoofMean -
            2 * (annularContractedUpperRetainedDelayedDepth p : ℝ) *
                gaussRoofMean +
            3 * upperGoodTransferDenominatorTolerance eta rho *
              (annularDepthAmbientSize N : ℝ) =
          Real.log (N : ℝ) +
              ((annularContractedUpperRetainedCenterDepth p : ℝ) *
                  gaussRoofMean +
                upperGoodTransferDenominatorTolerance eta rho *
                  (annularDepthAmbientSize N : ℝ)) -
            2 *
              ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                  gaussRoofMean -
                upperGoodTransferDenominatorTolerance eta rho *
                  (annularDepthAmbientSize N : ℝ)) := by
      ring
    have hexpFormula :
        Real.exp
            (Real.log (N : ℝ) +
                (annularContractedUpperRetainedCenterDepth p : ℝ) *
                  gaussRoofMean -
              2 * (annularContractedUpperRetainedDelayedDepth p : ℝ) *
                  gaussRoofMean +
              3 * upperGoodTransferDenominatorTolerance eta rho *
                (annularDepthAmbientSize N : ℝ)) =
          (N : ℝ) *
              Real.exp
                ((annularContractedUpperRetainedCenterDepth p : ℝ) *
                    gaussRoofMean +
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ)) /
            Real.exp
                ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                    gaussRoofMean -
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ)) ^ 2 := by
      calc
        _ = Real.exp
            (Real.log (N : ℝ) +
                ((annularContractedUpperRetainedCenterDepth p : ℝ) *
                    gaussRoofMean +
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ)) -
              2 *
                ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                    gaussRoofMean -
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ))) :=
          congrArg Real.exp hexponent
        _ = Real.exp
              (Real.log (N : ℝ) +
                ((annularContractedUpperRetainedCenterDepth p : ℝ) *
                    gaussRoofMean +
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ))) /
            Real.exp
              (2 *
                ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                    gaussRoofMean -
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ))) :=
          Real.exp_sub _ _
        _ = (Real.exp (Real.log (N : ℝ)) *
              Real.exp
                ((annularContractedUpperRetainedCenterDepth p : ℝ) *
                    gaussRoofMean +
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ))) /
            Real.exp
                ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                    gaussRoofMean -
                  upperGoodTransferDenominatorTolerance eta rho *
                    (annularDepthAmbientSize N : ℝ)) ^ 2 := by
          rw [Real.exp_add]
          have hden :
              Real.exp
                  (2 *
                    ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                        gaussRoofMean -
                      upperGoodTransferDenominatorTolerance eta rho *
                        (annularDepthAmbientSize N : ℝ))) =
                Real.exp
                    ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                        gaussRoofMean -
                      upperGoodTransferDenominatorTolerance eta rho *
                        (annularDepthAmbientSize N : ℝ)) ^ 2 := by
            rw [show
              2 *
                    ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                        gaussRoofMean -
                      upperGoodTransferDenominatorTolerance eta rho *
                        (annularDepthAmbientSize N : ℝ)) =
                ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                      gaussRoofMean -
                    upperGoodTransferDenominatorTolerance eta rho *
                      (annularDepthAmbientSize N : ℝ)) +
                  ((annularContractedUpperRetainedDelayedDepth p : ℝ) *
                      gaussRoofMean -
                    upperGoodTransferDenominatorTolerance eta rho *
                      (annularDepthAmbientSize N : ℝ)) by ring,
              Real.exp_add]
            ring
          rw [hden]
        _ = _ := by rw [Real.exp_log hNpos]
    rw [hexpFormula]
    ring
  rw [hrewrite]
  unfold annularContractedUpperRetainedPhaseUniformMajorant
  have hweight :
      weight ≤ annularUpperRetainedTotalModeWeight k mode := by
    simpa only [weight] using!
      sum_abs_delayedPrefixMode_le_totalModeWeight p
  have hexponent :=
    annularContractedUpperRetainedPhaseExponent_le
      hrho hN k hr mode hmode p
  have hexp := Real.exp_le_exp.mpr hexponent
  have hfactor : 0 ≤ 4 * Real.pi := by positivity
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hweight hfactor)
    hexp (Real.exp_pos _).le
    (mul_nonneg hfactor
      (annularUpperRetainedTotalModeWeight_nonneg k mode))

/-! ## Polynomial absorption and the aggregate phase limit -/

/-- A fixed polynomial in the annular depth is absorbed by every fixed
negative exponential in that depth. -/
theorem tendsto_annularDepth_pow_mul_exp_neg_const_zero
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp (-c * (annularDepthAmbientSize N : ℝ)))
      atTop (nhds 0) := by
  have hH :
      Tendsto
        (fun N : ℕ ↦ c * (annularDepthAmbientSize N : ℝ))
        atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp
      tendsto_annularDepthAmbientSize_atTop).const_mul_atTop hc
  have hraw :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r).comp hH
  have hscaled := hraw.const_mul (c⁻¹ ^ r)
  convert! hscaled using 1
  · funext N
    dsimp only [Function.comp_apply]
    have hcne : c ≠ 0 := ne_of_gt hc
    calc
      (annularDepthAmbientSize N : ℝ) ^ r *
            Real.exp (-c * (annularDepthAmbientSize N : ℝ)) =
          ((c⁻¹ * c) ^ r *
              (annularDepthAmbientSize N : ℝ) ^ r) *
            Real.exp (-c * (annularDepthAmbientSize N : ℝ)) := by
              rw [inv_mul_cancel₀ hcne, one_pow, one_mul]
      _ = c⁻¹ ^ r *
          ((c * (annularDepthAmbientSize N : ℝ)) ^ r *
            Real.exp (-(c *
              (annularDepthAmbientSize N : ℝ)))) := by
              rw [mul_pow]
              ring_nf
  · simp

/-- The uniform phase scalar, multiplied by any fixed ambient polynomial,
tends to zero. -/
theorem
    tendsto_annularDepth_pow_mul_phaseUniformMajorant_zero
    (r : ℕ) {rho : ℝ} (hrho : 0 < rho)
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) :
    Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          annularContractedUpperRetainedPhaseUniformMajorant
            rho N k mode)
      atTop (nhds 0) := by
  let c : ℝ := gaussRoofMean * rho / 8
  let C : ℝ :=
    4 * Real.pi * annularUpperRetainedTotalModeWeight k mode *
      Real.exp (3 * gaussRoofMean / 2)
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (mul_pos gaussRoofMean_pos hrho) (by norm_num)
  have hraw :=
    (tendsto_annularDepth_pow_mul_exp_neg_const_zero r hc).const_mul C
  convert! hraw using 1
  · funext N
    unfold annularContractedUpperRetainedPhaseUniformMajorant
    dsimp only [c, C]
    rw [show
      -(gaussRoofMean * rho *
          (annularDepthAmbientSize N : ℝ)) / 8 +
            3 * gaussRoofMean / 2 =
        -(gaussRoofMean * rho / 8) *
            (annularDepthAmbientSize N : ℝ) +
          3 * gaussRoofMean / 2 by ring,
      Real.exp_add]
    ring
  · simp

/-- The absolute sum of all corrected phase coefficients tends to zero.
Consequently the same holds after multiplication by any event mass bounded
by one. -/
theorem
    tendsto_sum_annularContractedUpperRetainedPhaseFreezingMajorant_zero
    {eta rho : ℝ} (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPhaseFreezingMajorant
            eta rho N k hr mode hmode p)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k + 1
  have hzero :=
    tendsto_annularDepth_pow_mul_phaseUniformMajorant_zero
      r hrho k mode
  have hcard :=
    eventually_nestedPairCount_contractedAnnularUpperRetained_le_ambient_pow
      eta rho hgrid k hr htime mode hmode
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        (∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPhaseFreezingMajorant
            eta rho N k hr mode hmode p) ≤
          (annularDepthAmbientSize N : ℝ) ^ r *
            annularContractedUpperRetainedPhaseUniformMajorant
              rho N k mode := by
    filter_upwards [eventually_ge_atTop 1, hcard] with N hN hcardN
    have hcardTagged :
        Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) ≤
          annularDepthAmbientSize N ^ r := by
      rw [
        card_annularContractedUpperRetainedTaggedTuple_eq_nestedPairCount]
      simpa only [r] using! hcardN
    have hmajorNonneg :
        0 ≤ annularContractedUpperRetainedPhaseUniformMajorant
          rho N k mode := by
      unfold annularContractedUpperRetainedPhaseUniformMajorant
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (annularUpperRetainedTotalModeWeight_nonneg k mode))
        (Real.exp_pos _).le
    calc
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p) ≤
          ∑ _p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            annularContractedUpperRetainedPhaseUniformMajorant
              rho N k mode := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          annularContractedUpperRetainedPhaseFreezingMajorant_le_uniform
            hrho hN k hr mode hmode p
      _ =
          (Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) *
            annularContractedUpperRetainedPhaseUniformMajorant
              rho N k mode := by simp
      _ ≤
          (annularDepthAmbientSize N : ℝ) ^ r *
            annularContractedUpperRetainedPhaseUniformMajorant
              rho N k mode := by
        apply mul_le_mul_of_nonneg_right _ hmajorNonneg
        exact_mod_cast hcardTagged
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun p _hp ↦ by
        unfold annularContractedUpperRetainedPhaseFreezingMajorant
        positivity
  · exact hupper
  · exact hzero

/-! ## Uniform value-radius decay -/

/-- Exponent in the common value-coordinate freezing radius.  Unlike the
phase exponent, this uses the shallow depth `d`; the empty interval from
`d=m-G` to `b=m+O` supplies still stronger decay. -/
def annularContractedUpperRetainedValueExponent
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℝ :=
  2 *
    (((annularContractedUpperRetainedShallowDepth p : ℝ) -
        (annularContractedUpperRetainedDelayedDepth p : ℝ)) *
        gaussRoofMean +
      2 * upperGoodTransferDenominatorTolerance eta rho *
        (annularDepthAmbientSize N : ℝ))

/-- Exact uniform bound for the value-radius exponent. -/
theorem annularContractedUpperRetainedValueExponent_le
    {eta rho : ℝ} {N grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedValueExponent
        eta rho N k hr mode hmode p ≤
      -(gaussRoofMean * rho *
          (annularDepthAmbientSize N : ℝ)) +
        5 * gaussRoofMean / 2 := by
  let q := annularContractedUpperRetainedUpperTag p
  let H := annularDepthAmbientSize N
  let W := annularMidpointBandWidth rho N
  let m := annularUpperRetainedSplitDepth q
  let G := annularUpperRetainedGap rho N
  let O := annularUpperRetainedFreezingOffset rho N
  let d := annularContractedUpperRetainedShallowDepth p
  let b := annularContractedUpperRetainedDelayedDepth p
  let Delta := upperGoodTransferDenominatorTolerance eta rho
  have hWG : W ≤ 2 * G + 1 := by
    dsimp only [W, G]
    unfold annularUpperRetainedGap midpointPrefixFutureGap
    omega
  have hGO : G ≤ 2 * O + 1 := by
    dsimp only [G, O]
    unfold annularUpperRetainedFreezingOffset
    omega
  have hrhoH : rho * (H : ℝ) ≤ (W : ℝ) := by
    simpa only [W, H, annularMidpointBandWidth] using!
      (Nat.le_ceil (rho * (annularDepthAmbientSize N : ℝ)))
  have hDelta : Delta ≤ gaussRoofMean * rho / 8 := by
    unfold Delta upperGoodTransferDenominatorTolerance
    have hmin : min eta rho ≤ rho := min_le_right _ _
    have hmul :
        gaussRoofMean * min eta rho ≤ gaussRoofMean * rho :=
      mul_le_mul_of_nonneg_left hmin gaussRoofMean_pos.le
    nlinarith
  have hDeltaH :
      4 * Delta * (H : ℝ) ≤
        (gaussRoofMean * rho / 2) * (H : ℝ) := by
    have hH : 0 ≤ (H : ℝ) := by positivity
    nlinarith
  have hdG : d + G = m := by
    simpa only [d, G, m, q,
      annularContractedUpperRetainedShallowDepth,
      annularContractedUpperRetainedUpperTag] using!
      annularUpperRetained_shallowSplit_add_gap
        hgrid htime q hN hW
  have hb : b = m + O := by rfl
  have hWGr : (W : ℝ) ≤ 2 * (G : ℝ) + 1 := by
    exact_mod_cast hWG
  have hGOr : (G : ℝ) ≤ 2 * (O : ℝ) + 1 := by
    exact_mod_cast hGO
  have hdGr : (d : ℝ) + (G : ℝ) = (m : ℝ) := by
    exact_mod_cast hdG
  have hbr : (b : ℝ) = (m : ℝ) + (O : ℝ) := by
    exact_mod_cast hb
  unfold annularContractedUpperRetainedValueExponent
  dsimp only [H, W, m, G, O, d, b, Delta, q] at hrhoH hDeltaH hWGr hGOr hdGr hbr ⊢
  nlinarith [gaussRoofMean_pos]

/-- Tuple-independent upper envelope for the common value radius. -/
def annularUpperFreezingValueRadiusEnvelope
    (rho : ℝ) (N : ℕ) : ℝ :=
  2 * Real.log (N : ℝ) *
    Real.exp
      (-(gaussRoofMean * rho *
          (annularDepthAmbientSize N : ℝ)) +
        5 * gaussRoofMean / 2)

/-- Every tuple's literal common value radius is below the preceding
uniform envelope. -/
theorem
    gaussPrefixGoodValueFreezingRadius_le_annularUpperEnvelope
    {eta rho : ℝ} {N grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    gaussPrefixGoodValueFreezingRadius N
        (annularContractedUpperRetainedShallowDepth p)
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho) ≤
      annularUpperFreezingValueRadiusEnvelope rho N := by
  have hlog :
      0 ≤ 2 * Real.log (N : ℝ) := by
    have hcast : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show 1 ≤ N by omega)
    exact mul_nonneg (by norm_num) (Real.log_nonneg hcast)
  unfold gaussPrefixGoodValueFreezingRadius
    annularUpperFreezingValueRadiusEnvelope
  apply mul_le_mul_of_nonneg_left _ hlog
  apply Real.exp_le_exp.mpr
  simpa only [annularContractedUpperRetainedValueExponent] using!
    annularContractedUpperRetainedValueExponent_le
      hgrid k hr htime mode hmode hN hW p

/-- Any fixed ambient polynomial times the uniform value-radius envelope
tends to zero. -/
theorem
    tendsto_const_mul_annularDepth_pow_mul_valueRadiusEnvelope_zero
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto
      (fun N : ℕ ↦
        C * (annularDepthAmbientSize N : ℝ) ^ r *
          annularUpperFreezingValueRadiusEnvelope rho N)
      atTop (nhds 0) := by
  let c := gaussRoofMean * rho
  let D :=
    2 * C * gaussRoofMean *
      Real.exp (5 * gaussRoofMean / 2)
  have hc : 0 < c := mul_pos gaussRoofMean_pos hrho
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC)
        gaussRoofMean_pos.le)
      (Real.exp_pos _).le
  have hzero :=
    (tendsto_annularDepth_pow_mul_exp_neg_const_zero
      (r + 1) hc).const_mul D
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        C * (annularDepthAmbientSize N : ℝ) ^ r *
            annularUpperFreezingValueRadiusEnvelope rho N ≤
          D * ((annularDepthAmbientSize N : ℝ) ^ (r + 1) *
            Real.exp (-c *
              (annularDepthAmbientSize N : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog :=
      log_natCast_le_ambient_sub_one_mul_gaussRoofMean hN
    have hHnat : 1 ≤ annularDepthAmbientSize N := by
      unfold annularDepthAmbientSize
      omega
    have hH : (1 : ℝ) ≤
        (annularDepthAmbientSize N : ℝ) := by
      exact_mod_cast hHnat
    have hlogUpper :
        Real.log (N : ℝ) ≤
          gaussRoofMean *
            (annularDepthAmbientSize N : ℝ) := by
      calc
        Real.log (N : ℝ) ≤
            ((annularDepthAmbientSize N : ℝ) - 1) *
              gaussRoofMean := hlog
        _ ≤ gaussRoofMean *
            (annularDepthAmbientSize N : ℝ) := by
          nlinarith [gaussRoofMean_pos]
    unfold annularUpperFreezingValueRadiusEnvelope
    dsimp only [c, D]
    calc
      C * (annularDepthAmbientSize N : ℝ) ^ r *
          (2 * Real.log (N : ℝ) *
            Real.exp
              (-(gaussRoofMean * rho *
                  (annularDepthAmbientSize N : ℝ)) +
                5 * gaussRoofMean / 2)) ≤
        C * (annularDepthAmbientSize N : ℝ) ^ r *
          (2 *
            (gaussRoofMean *
              (annularDepthAmbientSize N : ℝ)) *
            Real.exp
              (-(gaussRoofMean * rho *
                  (annularDepthAmbientSize N : ℝ)) +
                5 * gaussRoofMean / 2)) := by
          gcongr
      _ =
        (2 * C * gaussRoofMean *
            Real.exp (5 * gaussRoofMean / 2)) *
          ((annularDepthAmbientSize N : ℝ) ^ (r + 1) *
            Real.exp (-(gaussRoofMean * rho) *
              (annularDepthAmbientSize N : ℝ))) := by
        rw [Real.exp_add, pow_succ]
        ring_nf
  have hlower :
      ∀ᶠ N : ℕ in atTop,
        0 ≤ C * (annularDepthAmbientSize N : ℝ) ^ r *
          annularUpperFreezingValueRadiusEnvelope rho N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    unfold annularUpperFreezingValueRadiusEnvelope
    have hlog :
        0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  exact squeeze_zero' hlower hupper
    (by simpa only [mul_zero] using! hzero)

/-- In particular, the uniform value radius itself tends to zero. -/
theorem tendsto_annularUpperFreezingValueRadiusEnvelope_zero
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto
      (annularUpperFreezingValueRadiusEnvelope rho)
      atTop (nhds 0) := by
  simpa only [one_mul, pow_zero] using!
    tendsto_const_mul_annularDepth_pow_mul_valueRadiusEnvelope_zero
      1 0 (by norm_num) hrho

end

end Erdos1002
