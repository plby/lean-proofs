import ErdosProblems.Erdos1002.GaussPrefixAnnularZeroMode
import ErdosProblems.Erdos1002.GaussUniformAggregateTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The literal uniform-Lebesgue annular zero mode

The Gauss-measure annular theorem is stationary and therefore does not see
the left time endpoint.  The original Erdős law is uniform Lebesgue measure.
For active time cells bounded away from zero, the first selected
continued-fraction depth is a positive multiple of `log N`; exponential
Gauss-transfer convergence then makes the complete tagged Lebesgue and
Gauss tuple sums asymptotically equal.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUniformZeroModePropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- Common lower depth supplied by the first positive annular time cell. -/
def annularPositiveTimeDepthFloor (N grid : ℕ) : ℕ :=
  gaussLogDepthEndpoint N (intervalGridPoint 0 1 grid 1)

theorem intervalGridPoint_zero_one_one_pos
    {grid : ℕ} (hgrid : 0 < grid) :
    0 < intervalGridPoint 0 1 grid 1 := by
  unfold intervalGridPoint
  norm_num
  positivity

theorem tendsto_annularPositiveTimeDepthFloor_div_log
    {grid : ℕ} (hgrid : 0 < grid) :
    Tendsto
      (fun N ↦ (annularPositiveTimeDepthFloor N grid : ℝ) /
        Real.log (N : ℝ))
      atTop
      (nhds (intervalGridPoint 0 1 grid 1 / gaussRoofMean)) := by
  simpa only [annularPositiveTimeDepthFloor, gaussLogDepthEndpoint] using!
    tendsto_natCeil_const_mul_scale_div
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (intervalGridPoint_zero_one_one_pos hgrid).le
      gaussRoofMean_pos

/-- Every tuple in a positive nonterminal time cell begins after the common
positive logarithmic depth floor. -/
theorem canonicalAnnularGridTupleFamily_first_ge_positiveTimeDepthFloor
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    {N : ℕ} (hN : 1 ≤ N)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e) :
    annularPositiveTimeDepthFloor N grid ≤ t ⟨0, hr⟩ := by
  let j : Fin (MixedOccurrenceCount k) := ⟨0, hr⟩
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have htimeIndex : 1 ≤ (e j).1.time.1 :=
    htimePositive (e j).1 hactive
  have htimePoint :
      intervalGridPoint 0 1 grid 1 ≤
        intervalGridPoint 0 1 grid (e j).1.time.1 := by
    unfold intervalGridPoint
    have hgridR : (0 : ℝ) < grid := by exact_mod_cast hgrid
    have htimeIndexR : (1 : ℝ) ≤ ((e j).1.time.1 : ℝ) := by
      exact_mod_cast htimeIndex
    norm_num
    simpa only [one_div] using!
      div_le_div_of_nonneg_right htimeIndexR hgridR.le
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hN)
  have hfloorLower :
      annularPositiveTimeDepthFloor N grid ≤
        annularTimeDepthLower N grid (e j).1 := by
    unfold annularPositiveTimeDepthFloor annularTimeDepthLower
      gaussLogDepthEndpoint
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right htimePoint hlog)
      gaussRoofMean_pos.le
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp ht with
    ⟨F, _horder, hbox, hFt⟩
  have hmem :
      t j ∈ annularOccurrenceParityDepthBox N k (e j) := by
    have hj := hbox j
    rw [← hFt]
    simpa only [annularOccurrenceParityDepthBox,
      annularTimeParityDepthBox, parityIco, Finset.mem_filter,
      annularOccurrenceDepthBoxes, annularOccurrenceParity] using! hj
  have hlower :
      annularTimeDepthLower N grid (e j).1 ≤ t j := by
    have hmem' :
        (annularTimeDepthLower N grid (e j).1 ≤ t j ∧
            t j < annularTimeDepthUpper N grid (e j).1) ∧
          t j % 2 = (annularGridDepthParity (e j).1).1 := by
      simpa only [annularOccurrenceParityDepthBox,
        annularTimeParityDepthBox, parityIco, Finset.mem_filter,
        Finset.mem_Ico, annularOccurrenceDepthBoxes,
        annularOccurrenceParity] using! hmem
    exact hmem'.1.1
  exact hfloorLower.trans hlower

/-- The actual annular zero mode under uniform Lebesgue measure.  The
additional positive-time hypothesis is essential for this transfer; the
deleted time-zero endpoint layer is restored separately in the final grid
assembly. -/
theorem tendsto_annularCanonicalUniformZeroMode
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e))
      atTop
      (nhds (annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k)) := by
  let tupleFamily :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ canonicalAnnularGridTupleFamily N k e
  have htotal : Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard (tupleFamily N) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [tupleFamily, aggregateTupleFamilyCard] using!
      tendsto_totalCanonicalAnnularGridTupleCard_density
        hgrid k hr htime
  have hdepthRatio :=
    tendsto_annularPositiveTimeDepthFloor_div_log hgrid
  have hdepthConstant :
      0 < intervalGridPoint 0 1 grid 1 / gaussRoofMean :=
    div_pos (intervalGridPoint_zero_one_one_pos hgrid)
      gaussRoofMean_pos
  have hdecay :=
    tendsto_aggregateTupleFamilyCard_mul_transferDecay_of_depth_ratio
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop tupleFamily htotal
      (fun N ↦ annularPositiveTimeDepthFloor N grid)
      hdepthConstant hdepthRatio
  refine
    tendsto_aggregateUniformMovingSignedApproximationTupleMassSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A)
      (density := annularOccurrenceTimeDensity k)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      ?_ ?_ ?_ ?_
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      ?_
      tupleFamily
      ?_ ?_ htotal ?_
      (fun N ↦ annularPositiveTimeDepthFloor N grid)
      ?_ hdecay
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_pos
        hε hεA hgrid hsigned e j
  · exact fun e j ↦
      flattenedAnnular_oriented_lower_lt_upper
        hεA hgrid e j
  · exact fun e j ↦
      flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned e j
  · exact flattenedAnnular_oriented_product_eq ε A
  · filter_upwards
      [tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0] with
      N hN
    exact hN
  · exact fun N e t ht ↦
      canonicalAnnularGridTupleFamily_chronological N k e t ht
  · exact fun N e t ht j ↦
      canonicalAnnularGridTupleFamily_parity N k e t ht j
  · simpa only [tupleFamily, aggregateShortTupleFamilyCard] using!
      tendsto_totalShortCanonicalAnnularGridTupleCard_sqrt_density_zero
        hgrid k hr htime
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact fun e t ht ↦
      canonicalAnnularGridTupleFamily_first_ge_positiveTimeDepthFloor
        hgrid k hr htimePositive hN e t ht

end

end Erdos1002
