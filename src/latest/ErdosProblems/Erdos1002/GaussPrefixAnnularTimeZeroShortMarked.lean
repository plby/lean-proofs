import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMode
import ErdosProblems.Erdos1002.GaussPrefixAnnularShortMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Short marked annular tuples including the first time cell

The old uniform short-block theorem used a positive first-depth floor.
For the first time cell that floor is unavailable.  Instead, the entire
short family already has zero normalized cardinal density under Gauss
measure, and absolute continuity transfers its zero mass to Lebesgue
measure.  The modulus-one character bound then deletes every marked mode.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

private theorem shortNatTupleFamily_idem_timeZero
    {r gap : ℕ} (tuples : Finset (Fin r → ℕ)) :
    shortNatTupleFamily gap (shortNatTupleFamily gap tuples) =
      shortNatTupleFamily gap tuples := by
  ext t
  simp

theorem tendsto_annularCanonicalGaussShortMass_zero_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateGaussMovingSignedApproximationTupleSum
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
      exact shortNatTupleFamily_idem_timeZero
        (canonicalAnnularGridTupleFamily N k e)
    rw [hId]
  have hlimit :=
    tendsto_aggregateGaussMovingSignedApproximationTupleSum
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
  simpa only [zero_mul, tupleFamily] using! hlimit

theorem tendsto_annularCanonicalUniformShortMass_zero_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
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
  let gaussMass : ℕ → ℝ := fun N ↦
    aggregateGaussMovingSignedApproximationTupleSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (Real.log (N : ℝ))
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ shortCanonicalAnnularGridTupleFamily N k e)
  apply squeeze_zero'
    (g := fun N ↦ (2 * Real.log 2) * gaussMass N)
  · exact Eventually.of_forall fun N ↦ by
      unfold aggregateUniformMovingSignedApproximationTupleMassSum
        aggregateMovingSignedApproximationTupleMassSum
        movingSignedApproximationTupleMassSum
      positivity
  · exact Eventually.of_forall fun N ↦
      aggregateUniformMovingSignedApproximationTupleMassSum_le_gauss
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ shortCanonicalAnnularGridTupleFamily N k e)
  · have hgauss :=
      tendsto_annularCanonicalGaussShortMass_zero_including_time_zero
        hε hεA hgrid k hr htime hsigned
    have h := hgauss.const_mul (2 * Real.log 2)
    simpa only [gaussMass, mul_zero] using! h

theorem
    tendsto_annularCanonicalUniformShortMarkedFourier_zero_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
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
    (g := fun N : ℕ ↦
      aggregateUniformMovingSignedApproximationTupleMassSum
        (β := Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ shortCanonicalAnnularGridTupleFamily N k e))
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
  · exact
      tendsto_annularCanonicalUniformShortMass_zero_including_time_zero
        hε hεA hgrid k hr htime hsigned

/-- Full marked cancellation follows from separated cancellation without
excluding the first time cell. -/
theorem
    tendsto_annularCanonicalUniformMarkedFourier_zero_of_separated_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
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
    tendsto_annularCanonicalUniformShortMarkedFourier_zero_including_time_zero
      hε hεA hgrid k hr htime hsigned mode
  have hadd := hshort.add hseparated
  have haddZero : Tendsto
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
