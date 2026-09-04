import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform shallow-cylinder cancellation in the upper retained family

This file applies the generic shallow-carrier estimate to each canonical
upper-retained tuple.  The carrier is the last nonzero chronological
Fourier coordinate.  Its separation from all earlier nonzero coordinates
comes from the canonical annular separation, while the decay in the
cylinder count comes from the much larger retained midpoint gap.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperShallowCancellationPropDecidable
    (P : Prop) : Decidable P :=
  gaussPrefixDelayedCarrierPropDecidable P

variable {rho A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- The labeled occurrence corresponding to the last nonzero
chronological mode. -/
def annularUpperRetainedCenterOccurrence
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    GaussPrefixMixedOccurrence k :=
  p.1 (annularLastNonzeroIndex (mode p.1) (hmode p.1))

theorem annularUpperRetained_centerOccurrence_depth
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    ((annularUpperRetainedRealization p).1
        (annularUpperRetainedCenterOccurrence p).1
        (annularUpperRetainedCenterOccurrence p).2 : ℕ) =
      annularUpperRetainedTimes p
        (annularLastNonzeroIndex (mode p.1) (hmode p.1)) := by
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have htimes :=
    congrFun (annularUpperRetainedRealization_times p) s
  change
    ((annularUpperRetainedRealization p).1
        (p.1 s).1 (p.1 s).2 : ℕ) =
      annularUpperRetainedTimes p s at htimes
  simpa only [annularUpperRetainedCenterOccurrence, s] using! htimes

theorem annularUpperRetained_centerOccurrence_coeff_ne_zero
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    unflattenedAnnularFourierMode p.1 (mode p.1)
        (annularUpperRetainedCenterOccurrence p).1
        (annularUpperRetainedCenterOccurrence p).2 ≠ 0 := by
  unfold annularUpperRetainedCenterOccurrence
    unflattenedAnnularFourierMode
  simpa only [p.1.symm_apply_apply] using!
    annularLastNonzeroIndex_ne_zero (mode p.1) (hmode p.1)

/-- Every other nonzero labeled Fourier coordinate lies one canonical
separation gap before the center occurrence. -/
theorem annularUpperRetained_nonzero_gap_before_centerOccurrence
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    ∀ z : GaussPrefixMixedOccurrence k,
      z ≠ annularUpperRetainedCenterOccurrence p →
      unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2 ≠ 0 →
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) +
            annularSeparationGap N ≤
          ((annularUpperRetainedRealization p).1
            (annularUpperRetainedCenterOccurrence p).1
            (annularUpperRetainedCenterOccurrence p).2 : ℕ) := by
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have hupper :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp p.2.2).1
  have hlate :=
    (mem_lateFirstNatTupleFamily_iff.mp hupper).1
  have hsep :
      IsSeparatedNatTuple (annularSeparationGap N)
        (annularUpperRetainedTimes p) :=
    (mem_separatedNatTupleFamily_iff.mp hlate).2
  intro z hz hzMode
  let j : Fin (MixedOccurrenceCount k) := p.1.symm z
  have hjNe : j ≠ s := by
    intro hjs
    apply hz
    unfold annularUpperRetainedCenterOccurrence
    calc
      z = p.1 j := (p.1.apply_symm_apply z).symm
      _ = p.1 s := congrArg p.1 hjs
  have hjMode : mode p.1 j ≠ 0 := by
    simpa only [unflattenedAnnularFourierMode, j] using! hzMode
  have hjGap :=
    gap_before_annularLastNonzeroIndex
      (mode p.1) (hmode p.1) (annularUpperRetainedTimes p)
      hsep j hjNe hjMode
  have hjTime :
      ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) =
        annularUpperRetainedTimes p j := by
    have htimes :=
      congrFun (annularUpperRetainedRealization_times p) j
    change
      ((annularUpperRetainedRealization p).1
          (p.1 j).1 (p.1 j).2 : ℕ) =
        annularUpperRetainedTimes p j at htimes
    have hej : p.1 j = z := p.1.apply_symm_apply z
    rw [hej] at htimes
    exact htimes
  rw [hjTime, annularUpperRetained_centerOccurrence_depth p]
  simpa only [s] using! hjGap

set_option maxHeartbeats 800000 in
/-- Direct application of the generic carrier theorem at the shallow
cutoff.  The bound is uniform in the tagged tuple. -/
theorem
    norm_sum_annularUpperRetained_shallowPrefixGoodCells_le_envelope
    (hN : 2 ≤ N) (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hW : 0 < annularMidpointBandWidth rho N)
    {Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hweightBudget :
      2 * (∑ z : GaussPrefixMixedOccurrence k,
        |(unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1 z.2 : ℝ)|) ≤
        ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ))
    (lower upper : AnnularGridIndex grid → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∑ w ∈ shallowExactDepthPrefixGoodCells N
          (annularUpperRetainedShallowSplitDepth p)
          (annularDepthAmbientSize N) Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularUpperRetainedRealization p).1
            (annularUpperRetainedShallowSplitDepth p) y
            ∂uniform01Measure‖ ≤
      shallowPrefixCylinderEnvelope N (annularDepthAmbientSize N)
        (annularUpperRetainedShallowSplitDepth p)
        (annularUpperRetainedTimes p
          (annularLastNonzeroIndex (mode p.1) (hmode p.1)))
        Delta := by
  let : DecidableEq (AnnularGridIndex grid) :=
    fun a b ↦ gaussPrefixDelayedCarrierPropDecidable (a = b)
  let z₀ := annularUpperRetainedCenterOccurrence p
  have hcenter :
      ((annularUpperRetainedRealization p).1 z₀.1 z₀.2 : ℕ) ≤
        annularUpperRetainedShallowSplitDepth p := by
    rw [annularUpperRetained_centerOccurrence_depth p]
    exact annularUpperRetained_centerDepth_le_shallow
      hgrid htime p hN hW
  have hbudgetFiltered :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦
              ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
                annularUpperRetainedShallowSplitDepth p)).erase z₀,
        |(unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1 z.2 : ℝ)|) ≤
        ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) := by
    calc
      2 * (∑ z ∈
          ((Finset.univ :
              Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦
              ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
                annularUpperRetainedShallowSplitDepth p)).erase z₀,
        |(unflattenedAnnularFourierMode p.1 (mode p.1)
          z.1 z.2 : ℝ)|) ≤
          2 * ∑ z : GaussPrefixMixedOccurrence k,
            |(unflattenedAnnularFourierMode p.1 (mode p.1)
              z.1 z.2 : ℝ)| := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_univ_sum_of_nonneg
          (fun z ↦ abs_nonneg
            (unflattenedAnnularFourierMode p.1 (mode p.1)
              z.1 z.2 : ℝ))
      _ ≤ ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) :=
        hweightBudget
  have hraw :=
    norm_sum_exactDepthPrefixGoodCells_mixedPrefixCharacter_le_centerEnvelope
      N hN k (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularUpperRetainedRealization p).1
      (L := annularDepthAmbientSize N)
      (m := annularUpperRetainedShallowSplitDepth p)
      (gap := annularSeparationGap N)
      (Delta := Delta) (A := A) hDelta z₀ hcenter
      (annularUpperRetained_centerOccurrence_coeff_ne_zero p)
      (annularUpperRetained_nonzero_gap_before_centerOccurrence p)
      hbudgetFiltered lower upper hlower hupper hsmall
  simpa only [z₀, annularUpperRetained_centerOccurrence_depth p] using! hraw

/-- Denominator tolerance used for upper-retained shallow cancellation. -/
def upperRetainedShallowDenominatorTolerance (rho : ℝ) : ℝ :=
  gaussRoofMean * rho / 6

theorem upperRetainedShallowDenominatorTolerance_pos
    (hrho : 0 < rho) :
    0 < upperRetainedShallowDenominatorTolerance rho := by
  unfold upperRetainedShallowDenominatorTolerance
  exact div_pos (mul_pos gaussRoofMean_pos hrho) (by norm_num)

/-- Tuple-independent exponent dominating every shallow carrier
envelope.  The final `gaussRoofMean` absorbs the parity of the natural
half-band division. -/
def upperRetainedShallowUniformExponent
    (rho Delta : ℝ) (N : ℕ) : ℝ :=
  (annularDepthAmbientSize N : ℝ) * gaussRoofMean -
    (annularMidpointBandWidth rho N : ℝ) * gaussRoofMean -
    Real.log (N : ℝ) +
    3 * Delta * (annularDepthAmbientSize N : ℝ) +
    gaussRoofMean

/-- The exact shallow exponent is bounded by the tuple-independent
uniform exponent. -/
theorem shallowPrefixCylinderEnvelope_le_upperUniform
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    {Delta : ℝ} :
    shallowPrefixCylinderEnvelope N (annularDepthAmbientSize N)
        (annularUpperRetainedShallowSplitDepth p)
        (annularUpperRetainedTimes p
          (annularLastNonzeroIndex (mode p.1) (hmode p.1)))
        Delta ≤
      (36 / Real.pi) *
        Real.exp (upperRetainedShallowUniformExponent rho Delta N) := by
  have hnat :=
    annularUpperRetained_two_shallow_add_two_gap_le_ambient_add_center
      hgrid htime p hN hW
  have hnatReal :
      2 * (annularUpperRetainedShallowSplitDepth p : ℝ) +
          2 * (annularUpperRetainedGap rho N : ℝ) ≤
        (annularDepthAmbientSize N : ℝ) +
          (annularUpperRetainedTimes p
            (annularLastNonzeroIndex (mode p.1) (hmode p.1)) : ℝ) := by
    exact_mod_cast hnat
  have hroundNat :
      annularMidpointBandWidth rho N ≤
        2 * annularUpperRetainedGap rho N + 1 := by
    unfold annularUpperRetainedGap midpointPrefixFutureGap
    omega
  have hroundReal :
      (annularMidpointBandWidth rho N : ℝ) ≤
        2 * (annularUpperRetainedGap rho N : ℝ) + 1 := by
    exact_mod_cast hroundNat
  have hmu₁ :=
    mul_le_mul_of_nonneg_right hnatReal gaussRoofMean_pos.le
  have hmu₂ :=
    mul_le_mul_of_nonneg_right hroundReal gaussRoofMean_pos.le
  have hexponent :
      2 * (annularUpperRetainedShallowSplitDepth p : ℝ) *
            gaussRoofMean -
          (annularUpperRetainedTimes p
            (annularLastNonzeroIndex (mode p.1) (hmode p.1)) : ℝ) *
            gaussRoofMean -
          Real.log (N : ℝ) +
          3 * Delta * (annularDepthAmbientSize N : ℝ) ≤
        upperRetainedShallowUniformExponent rho Delta N := by
    unfold upperRetainedShallowUniformExponent
    nlinarith
  unfold shallowPrefixCylinderEnvelope
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponent) (by positivity)

end

end Erdos1002
