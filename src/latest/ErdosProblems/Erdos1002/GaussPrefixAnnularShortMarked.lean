import ErdosProblems.Erdos1002.GaussPrefixAnnularUniformZeroMode
import ErdosProblems.Erdos1002.GaussMovingSignedMarkedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negligibility of short annular tuples, including marked modes

The canonical tuple family is split at the square-root separation gap.
This file proves that the complete short-gap subfamily has vanishing
uniform-Lebesgue mass.  Since every torus character has modulus one, the
same statement holds for arbitrary order-dependent Fourier modes.

This removes the short-gap block from the nonzero Fourier problem without
any cancellation assumption.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The short-gap part of one canonical annular occurrence order. -/
def shortCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  shortNatTupleFamily (annularSeparationGap N)
    (canonicalAnnularGridTupleFamily N k e)

/-- The complementary long-gap part of one canonical occurrence order. -/
def separatedCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  separatedNatTupleFamily (annularSeparationGap N)
    (canonicalAnnularGridTupleFamily N k e)

@[simp] theorem mem_shortCanonicalAnnularGridTupleFamily_iff
    {N grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    {e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k}
    {t : Fin (MixedOccurrenceCount k) → ℕ} :
    t ∈ shortCanonicalAnnularGridTupleFamily N k e ↔
      t ∈ canonicalAnnularGridTupleFamily N k e ∧
        ¬ IsSeparatedNatTuple (annularSeparationGap N) t := by
  exact mem_shortNatTupleFamily_iff

private theorem shortNatTupleFamily_idem_annular
    {r gap : ℕ} (tuples : Finset (Fin r → ℕ)) :
    shortNatTupleFamily gap (shortNatTupleFamily gap tuples) =
      shortNatTupleFamily gap tuples := by
  ext t
  simp

/-- The full short-gap aggregate has zero uniform-Lebesgue mass. -/
theorem tendsto_annularCanonicalUniformShortMass_zero
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
          (fun e ↦ shortCanonicalAnnularGridTupleFamily N k e))
      atTop (nhds 0) := by
  let tupleFamily :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ shortCanonicalAnnularGridTupleFamily N k e
  have htotal : Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard (tupleFamily N) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
    simpa only [tupleFamily, aggregateTupleFamilyCard,
      shortCanonicalAnnularGridTupleFamily,
      totalShortCanonicalAnnularGridTupleCard] using!
      tendsto_totalShortCanonicalAnnularGridTupleCard_sqrt_density_zero
        hgrid k hr htime
  have hshort : Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := annularSeparationGap N) (tupleFamily N) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
    apply htotal.congr'
    filter_upwards with N
    have hId :
        aggregateShortTupleFamilyCard
            (gap := annularSeparationGap N) (tupleFamily N) =
          aggregateTupleFamilyCard (tupleFamily N) := by
      unfold aggregateShortTupleFamilyCard aggregateTupleFamilyCard
      apply Finset.sum_congr rfl
      intro e _he
      congr 1
      exact shortNatTupleFamily_idem_annular
        (canonicalAnnularGridTupleFamily N k e)
    rw [hId]
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
  have hlimit :=
    tendsto_aggregateUniformMovingSignedApproximationTupleMassSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A) (density := 0)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      (fun e j ↦
        flattenedAnnular_oriented_lower_pos
          hε hεA hgrid hsigned e j)
      (fun e j ↦
        flattenedAnnular_oriented_lower_lt_upper
          hεA hgrid e j)
      (fun e j ↦
        flattenedAnnular_oriented_upper_le
          hεA hgrid hsigned e j)
      (flattenedAnnular_oriented_product_eq ε A)
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      (tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0)
      tupleFamily
      (fun N e t ht ↦
        canonicalAnnularGridTupleFamily_chronological N k e t
          (mem_shortCanonicalAnnularGridTupleFamily_iff.mp ht).1)
      (fun N e t ht j ↦
        canonicalAnnularGridTupleFamily_parity N k e t
          (mem_shortCanonicalAnnularGridTupleFamily_iff.mp ht).1 j)
      htotal hshort
      (fun N ↦ annularPositiveTimeDepthFloor N grid)
      (by
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact fun e t ht ↦
          canonicalAnnularGridTupleFamily_first_ge_positiveTimeDepthFloor
            hgrid k hr htimePositive hN e t
              (mem_shortCanonicalAnnularGridTupleFamily_iff.mp ht).1)
      hdecay
  simpa only [zero_mul] using! hlimit

/-- Arbitrary order-dependent torus modes on the short block tend to
zero.  The proof uses only the modulus-one bound, so no mode is required
to be nonzero. -/
theorem
    tendsto_annularCanonicalUniformShortMarkedFourier_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) :
    Tendsto
      (fun N : ℕ ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (shortCanonicalAnnularGridTupleFamily N k e))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦ by
      calc
        ‖∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (shortCanonicalAnnularGridTupleFamily N k e)‖ ≤
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ‖uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (shortCanonicalAnnularGridTupleFamily N k e)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            movingSignedApproximationTupleMassSum
              uniform01Measure (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (shortCanonicalAnnularGridTupleFamily N k e) := by
          apply Finset.sum_le_sum
          intro e _he
          exact norm_movingSignedMarkedFourierTupleSum_le_mass
            uniform01Measure N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (shortCanonicalAnnularGridTupleFamily N k e)
        _ = aggregateUniformMovingSignedApproximationTupleMassSum
              (β := Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k)
              (Real.log (N : ℝ))
              (fun e ↦ flattenedAnnularSignedLower ε A e)
              (fun e ↦ flattenedAnnularSignedUpper ε A e)
              (fun e ↦
                shortCanonicalAnnularGridTupleFamily N k e) := rfl
  · exact tendsto_annularCanonicalUniformShortMass_zero
      hε hεA hgrid k hr htimePositive htime hsigned

/-! ## Exact reduction to the separated block -/

/-- For one occurrence order, the complete Fourier coefficient is exactly
the sum of its short-gap and separated parts. -/
theorem uniformMovingSignedMarkedFourierTupleSum_canonical_eq_short_add_separated
    {ε A : ℝ} {grid N : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) :
    uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode
        (canonicalAnnularGridTupleFamily N k e) =
      uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (shortCanonicalAnnularGridTupleFamily N k e) +
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (separatedCanonicalAnnularGridTupleFamily N k e) := by
  classical
  let f : (Fin (MixedOccurrenceCount k) → ℕ) → ℂ :=
    fun times ↦
      ∫ x, gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode times x ∂uniform01Measure
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not
      (canonicalAnnularGridTupleFamily N k e)
      (IsSeparatedNatTuple (annularSeparationGap N)) f
  simpa only [uniformMovingSignedMarkedFourierTupleSum,
    movingSignedMarkedFourierTupleSum,
    shortCanonicalAnnularGridTupleFamily,
    separatedCanonicalAnnularGridTupleFamily,
    shortNatTupleFamily, separatedNatTupleFamily, f] using!
      hpartition.symm.trans (add_comm _ _)

/-- Consequently, unconditional short-gap deletion reduces the complete
tag-dependent Fourier problem exactly to the separated block. -/
theorem
    tendsto_annularCanonicalUniformMarkedFourier_zero_of_separated
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hseparated :
      Tendsto
        (fun N : ℕ ↦
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (separatedCanonicalAnnularGridTupleFamily N k e))
        atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (canonicalAnnularGridTupleFamily N k e))
      atTop (nhds 0) := by
  have hshort :=
    tendsto_annularCanonicalUniformShortMarkedFourier_zero
      hε hεA hgrid k hr htimePositive htime hsigned mode
  have hadd := hshort.add hseparated
  have haddZero :
      Tendsto
        (fun N : ℕ ↦
          (∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (shortCanonicalAnnularGridTupleFamily N k e)) +
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (separatedCanonicalAnnularGridTupleFamily N k e))
        atTop (nhds 0) := by
    simpa only [add_zero] using! hadd
  apply haddZero.congr'
  filter_upwards with N
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    (uniformMovingSignedMarkedFourierTupleSum_canonical_eq_short_add_separated
      (ε := ε) (A := A) k e (mode e)).symm

end

end Erdos1002
