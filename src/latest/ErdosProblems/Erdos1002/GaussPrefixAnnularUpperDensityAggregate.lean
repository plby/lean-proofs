import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFrozenJoint
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDelayedFloor
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperCovarianceAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate freezing of the Lebesgue-to-Gauss density

After the prefix character has been frozen at the delayed depth, the only
remaining non-prefix-measurable factor in the prefix block is the exact
Lebesgue-to-Gauss density.  This file replaces that density by its value at
the canonical representative of the delayed cylinder.

The estimate is made with the complete affine-frozen prefix and future
digit block still attached.  Both factors have norm at most one.  The
delayed depth is uniformly at least the annular square-root separation gap,
so the pointwise density error is geometric in that gap.  This geometric
decay absorbs the polynomial number of contracted upper-retained tagged
tuples.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperDensityAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The density-only freezing error for one contracted upper-retained tag.
The affine-frozen prefix and the complete future digit block are retained
literally. -/
def annularContractedUpperRetainedDensityFreezingContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x,
    ((gaussPrefixFrozenLebesgueDensity
          (annularContractedUpperRetainedDelayedDepth p) x -
        gaussLebesguePrefixWeight x : ℝ) : ℂ) *
      gaussPrefixAffineFrozenCompactCharacter
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p) x *
      annularContractedUpperRetainedFutureDigitBlock ε A p x
    ∂gaussMeasure

/-- The complete future digit block has pointwise norm at most one. -/
theorem norm_annularContractedUpperRetainedFutureDigitBlock_le_one
    {ε A eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) :
    ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤ 1 := by
  unfold annularContractedUpperRetainedFutureDigitBlock
  rw [annularUpperRetainedFutureDigitBlock_eq_eventIndicator]
  by_cases hx :
      x ∈ annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- One density-freezing contribution is bounded by the uniform
representative error at its own delayed depth. -/
theorem
    norm_annularContractedUpperRetainedDensityFreezingContribution_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ‖annularContractedUpperRetainedDensityFreezingContribution
        ε A eta rho N k hr mode hmode p‖ ≤
      Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) := by
  unfold annularContractedUpperRetainedDensityFreezingContribution
  calc
    _ ≤ ∫ _x : ℝ,
        Real.log 2 * (1 / 4 : ℝ) ^
          (annularContractedUpperRetainedDelayedDepth p / 2)
        ∂gaussMeasure := by
      apply norm_integral_le_of_norm_le
        (integrable_const
          (Real.log 2 * (1 / 4 : ℝ) ^
            (annularContractedUpperRetainedDelayedDepth p / 2)))
      filter_upwards
        [ae_gauss_abs_gaussPrefixFrozenLebesgueDensity_sub_le
          (annularContractedUpperRetainedDelayedDepth p)] with x hx
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hprefix :
          ‖gaussPrefixAffineFrozenCompactCharacter
              N
              (activeAnnularOccurrenceSignedLower k ε A)
              (activeAnnularOccurrenceSignedUpper k ε A)
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ ≤ 1 :=
        norm_gaussPrefixAffineFrozenCompactCharacter_le_one
          N
          (activeAnnularOccurrenceSignedLower k ε A)
          (activeAnnularOccurrenceSignedUpper k ε A)
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p)
          (annularContractedUpperRetainedGoodWords eta rho N p) x
      calc
        |gaussPrefixFrozenLebesgueDensity
              (annularContractedUpperRetainedDelayedDepth p) x -
            gaussLebesguePrefixWeight x| *
            ‖gaussPrefixAffineFrozenCompactCharacter
              N
              (activeAnnularOccurrenceSignedLower k ε A)
              (activeAnnularOccurrenceSignedUpper k ε A)
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ *
            ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤
          (Real.log 2 * (1 / 4 : ℝ) ^
              (annularContractedUpperRetainedDelayedDepth p / 2)) *
            ‖gaussPrefixAffineFrozenCompactCharacter
              N
              (activeAnnularOccurrenceSignedLower k ε A)
              (activeAnnularOccurrenceSignedUpper k ε A)
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ *
            ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            (norm_nonneg _)
        _ ≤ (Real.log 2 * (1 / 4 : ℝ) ^
              (annularContractedUpperRetainedDelayedDepth p / 2)) *
            1 *
            ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprefix (by positivity))
            (norm_nonneg _)
        _ ≤ (Real.log 2 * (1 / 4 : ℝ) ^
              (annularContractedUpperRetainedDelayedDepth p / 2)) *
            1 * 1 := by
          exact mul_le_mul_of_nonneg_left
            (norm_annularContractedUpperRetainedFutureDigitBlock_le_one p x)
            (mul_nonneg (by positivity) zero_le_one)
        _ = Real.log 2 * (1 / 4 : ℝ) ^
            (annularContractedUpperRetainedDelayedDepth p / 2) := by ring
    _ = Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) := by simp

/-- Uniform one-tag bound at the common square-root separation scale. -/
theorem
    norm_annularContractedUpperRetainedDensityFreezingContribution_le_transferDecay
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N) :
    ‖annularContractedUpperRetainedDensityFreezingContribution
        ε A eta rho N k hr mode hmode p‖ ≤
      (540 / 527 : ℝ) *
        ((527 / 540 : ℝ) ^ annularSeparationGap N *
          Real.log 2) := by
  have hgapDepth :
      annularSeparationGap N ≤
        annularContractedUpperRetainedDelayedDepth p := by
    simpa only [annularContractedUpperRetainedDelayedDepth,
      annularContractedUpperRetainedUpperTag] using!
      annularSeparationGap_le_annularUpperRetainedDelayedSplitDepth
        hgrid htime (annularContractedUpperRetainedUpperTag p) hN
  calc
    ‖annularContractedUpperRetainedDensityFreezingContribution
        ε A eta rho N k hr mode hmode p‖ ≤
      Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) :=
      norm_annularContractedUpperRetainedDensityFreezingContribution_le
        ε A eta rho N k hr mode hmode p
    _ ≤ Real.log 2 *
        ((540 / 527 : ℝ) *
          (527 / 540 : ℝ) ^ annularSeparationGap N) := by
      exact mul_le_mul_of_nonneg_left
        (quarter_pow_half_le_transferDecay_of_le hgapDepth)
        (Real.log_pos one_lt_two).le
    _ = (540 / 527 : ℝ) *
        ((527 / 540 : ℝ) ^ annularSeparationGap N *
          Real.log 2) := by ring

/-! ## Aggregate absolute error -/

/-- Sum of the density-freezing norms over all contracted upper tags. -/
def annularContractedUpperRetainedDensityFreezingNormSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ‖annularContractedUpperRetainedDensityFreezingContribution
      ε A eta rho N k hr mode hmode p‖

/-- Finite-`N` domination by the tagged cardinality and the common
square-root transfer rate. -/
theorem annularContractedUpperRetainedDensityFreezingNormSum_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N) :
    annularContractedUpperRetainedDensityFreezingNormSum
        ε A eta rho N k hr mode hmode ≤
      (Fintype.card
        (AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode) : ℝ) *
        ((540 / 527 : ℝ) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2)) := by
  unfold annularContractedUpperRetainedDensityFreezingNormSum
  calc
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      ‖annularContractedUpperRetainedDensityFreezingContribution
        ε A eta rho N k hr mode hmode p‖) ≤
      ∑ _p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ((540 / 527 : ℝ) *
          ((527 / 540 : ℝ) ^ annularSeparationGap N *
            Real.log 2)) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        norm_annularContractedUpperRetainedDensityFreezingContribution_le_transferDecay
          ε A eta rho N hgrid k hr htime mode hmode p hN
    _ = _ := by simp

/-- Polynomially many contracted upper density-freezing errors have
vanishing total norm. -/
theorem
    tendsto_annularContractedUpperRetainedDensityFreezingNormSum_zero
    (ε A eta rho : ℝ)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        annularContractedUpperRetainedDensityFreezingNormSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let r : ℕ := MixedOccurrenceCount k + 1
  let upper : ℕ → ℝ := fun N ↦
    (annularDepthAmbientSize N : ℝ) ^ r *
      ((540 / 527 : ℝ) *
        ((527 / 540 : ℝ) ^ annularSeparationGap N *
          Real.log 2))
  have hzero : Tendsto upper atTop (nhds 0) := by
    have h :=
      (tendsto_annularAmbientPower_mul_transferDecay_zero r).const_mul
        (540 / 527 : ℝ)
    convert! h using 1
    · funext N
      dsimp only [upper]
      ring
    · ring
  have hcard :=
    eventually_nestedPairCount_contractedAnnularUpperRetained_le_ambient_pow
      eta rho hgrid k hr htime mode hmode
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold annularContractedUpperRetainedDensityFreezingNormSum
      exact Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop 2, hcard] with N hN hcardN
    have hcardTagged :
        Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) ≤
          annularDepthAmbientSize N ^ r := by
      rw [card_annularContractedUpperRetainedTaggedTuple_eq_nestedPairCount]
      simpa only [r] using! hcardN
    calc
      annularContractedUpperRetainedDensityFreezingNormSum
          ε A eta rho N k hr mode hmode ≤
        (Fintype.card
          (AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode) : ℝ) *
          ((540 / 527 : ℝ) *
            ((527 / 540 : ℝ) ^ annularSeparationGap N *
              Real.log 2)) :=
        annularContractedUpperRetainedDensityFreezingNormSum_le
          ε A eta rho N hgrid k hr htime mode hmode hN
      _ ≤ (annularDepthAmbientSize N : ℝ) ^ r *
          ((540 / 527 : ℝ) *
            ((527 / 540 : ℝ) ^ annularSeparationGap N *
              Real.log 2)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcardTagged
        · positivity
      _ = upper N := rfl
  · exact hzero

/-! ## Identification with the two canonical tagged joints -/

/-- For one contracted tag, the density-freezing contribution is exactly
the frozen-density joint minus the corresponding live-density affine
joint. -/
theorem
    annularContractedUpperRetainedFrozenDigitJoint_sub_affine_eq_densityFreezingContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedFrozenDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
          ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedDensityFreezingContribution
        ε A eta rho N k hr mode hmode p := by
  let carrier : ℝ → ℂ := fun x ↦
    gaussPrefixAffineFrozenCompactCharacter
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p) x *
      annularContractedUpperRetainedFutureDigitBlock ε A p x
  have hEvents :
      ∀ j : Fin (MixedOccurrenceCount k),
        MeasurableSet
          (annularContractedUpperRetainedFutureDigitEvent ε A p j) := by
    intro j
    unfold annularContractedUpperRetainedFutureDigitEvent
      annularContractedUpperRetainedUpperTag
    exact
      measurableSet_annularUpperRetainedFutureDigitEvent
        (annularContractedUpperRetainedToUpper p) j
  have hcarrierRaw :=
    (gaussPrefixAffineFrozen_futureDigitBlock_covariance_le
      N
      (activeAnnularOccurrenceSignedLower k ε A)
      (activeAnnularOccurrenceSignedUpper k ε A)
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
      (annularContractedUpperRetainedMixingGap rho N)
      (annularContractedUpperRetainedGoodWords eta rho N p)
      (annularContractedUpperRetainedFutureTime p)
      hEvents).1
  rw [annularContractedUpperRetained_delayedDepth_add_mixingGap p]
    at hcarrierRaw
  have hcarrier : Integrable carrier gaussMeasure := by
    simpa only [carrier,
      annularContractedUpperRetainedFutureDigitBlock,
      annularContractedUpperRetainedFutureTime,
      annularContractedUpperRetainedFutureDigitEvent,
      annularContractedUpperRetainedUpperTag,
      annularUpperRetainedFutureDigitBlock] using! hcarrierRaw
  have hfrozenMeasurable :
      AEStronglyMeasurable
        (fun x : ℝ ↦
          (gaussPrefixFrozenLebesgueDensity
            (annularContractedUpperRetainedDelayedDepth p) x : ℂ))
        gaussMeasure := by
    exact
      ((measurable_gaussPrefixFrozenLebesgueDensity_prefix
          (annularContractedUpperRetainedDelayedDepth p)).complex_ofReal.mono
        (gaussPrefixMeasurableSpace_le
          (annularContractedUpperRetainedDelayedDepth p))
        le_rfl).aestronglyMeasurable
  have hfrozenBound :
      ∀ᵐ x : ℝ ∂gaussMeasure,
        ‖(gaussPrefixFrozenLebesgueDensity
          (annularContractedUpperRetainedDelayedDepth p) x : ℂ)‖ ≤
            2 * Real.log 2 :=
    Eventually.of_forall fun x ↦
      norm_gaussPrefixFrozenLebesgueDensity_le_two_log
        (annularContractedUpperRetainedDelayedDepth p) x
  have hfrozen :
      Integrable
        (fun x ↦
          (gaussPrefixFrozenLebesgueDensity
              (annularContractedUpperRetainedDelayedDepth p) x : ℂ) *
            carrier x)
        gaussMeasure :=
    hcarrier.bdd_mul hfrozenMeasurable hfrozenBound
  have hliveMeasurable :
      AEStronglyMeasurable
        (fun x : ℝ ↦ (gaussLebesguePrefixWeight x : ℂ))
        gaussMeasure :=
    measurable_gaussLebesguePrefixWeight.complex_ofReal.aestronglyMeasurable
  have hliveBound :
      ∀ᵐ x : ℝ ∂gaussMeasure,
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ ≤
          2 * Real.log 2 := by
    filter_upwards [gaussMeasure_unit_ae] with x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hbounds := gaussLebesguePrefixWeight_bounds hxIcc
    have hnonneg : 0 ≤ gaussLebesguePrefixWeight x :=
      (Real.log_pos one_lt_two).le.trans hbounds.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hbounds.2
  have hlive :
      Integrable
        (fun x ↦ (gaussLebesguePrefixWeight x : ℂ) * carrier x)
        gaussMeasure :=
    hcarrier.bdd_mul hliveMeasurable hliveBound
  have hFrozenJoint :
      annularContractedUpperRetainedFrozenDigitJoint
          ε A eta rho N k hr mode hmode p =
        ∫ x,
          (gaussPrefixFrozenLebesgueDensity
              (annularContractedUpperRetainedDelayedDepth p) x : ℂ) *
            carrier x
          ∂gaussMeasure := by
    unfold annularContractedUpperRetainedFrozenDigitJoint
      gaussLateLebesgueWeightedFrozenJoint
      gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
    rw [annularContractedUpperRetained_delayedDepth_add_mixingGap p]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [carrier,
      annularContractedUpperRetainedFutureDigitBlock,
      annularContractedUpperRetainedFutureTime,
      annularContractedUpperRetainedFutureDigitEvent,
      annularContractedUpperRetainedUpperTag,
      annularUpperRetainedFutureDigitBlock]
    ring
  have hAffineJoint :
      annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
          ε A eta rho N k hr mode hmode p =
        ∫ x, (gaussLebesguePrefixWeight x : ℂ) * carrier x
          ∂gaussMeasure := by
    unfold
      annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [carrier]
    ring
  have hContribution :
      annularContractedUpperRetainedDensityFreezingContribution
          ε A eta rho N k hr mode hmode p =
        ∫ x,
          ((gaussPrefixFrozenLebesgueDensity
                (annularContractedUpperRetainedDelayedDepth p) x -
              gaussLebesguePrefixWeight x : ℝ) : ℂ) *
            carrier x
          ∂gaussMeasure := by
    unfold
      annularContractedUpperRetainedDensityFreezingContribution
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [carrier]
    ring
  rw [hFrozenJoint, hAffineJoint, hContribution,
    ← integral_sub hfrozen hlive]
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  ring

/-! ## Difference of the aggregate canonical joints -/

/-- Aggregate affine-frozen joint before freezing the
Lebesgue-to-Gauss density. -/
def annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
      ε A eta rho N k hr mode hmode p

/-- The norm of the aggregate frozen-minus-affine difference is bounded
by the sum of the individual density-freezing norms. -/
theorem
    norm_annularContractedUpperRetainedFrozenDigitJointSum_sub_affine_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularContractedUpperRetainedFrozenDigitJointSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
          ε A eta rho N k hr mode hmode‖ ≤
      annularContractedUpperRetainedDensityFreezingNormSum
        ε A eta rho N k hr mode hmode := by
  unfold annularContractedUpperRetainedFrozenDigitJointSum
    annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
    annularContractedUpperRetainedDensityFreezingNormSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      (annularContractedUpperRetainedFrozenDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJoint
          ε A eta rho N k hr mode hmode p)‖ =
      ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        annularContractedUpperRetainedDensityFreezingContribution
          ε A eta rho N k hr mode hmode p‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro p _hp
        exact
          annularContractedUpperRetainedFrozenDigitJoint_sub_affine_eq_densityFreezingContribution
            ε A eta rho N k hr mode hmode p
    _ ≤ ∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedDensityFreezingContribution
          ε A eta rho N k hr mode hmode p‖ :=
      norm_sum_le _ _

/-- Freezing the density changes the complete aggregate
affine-prefix/future-digit joint by a quantity tending to zero.  The
orientation here is the one used in the replacement chain. -/
theorem
    tendsto_annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum_sub_frozen_zero
    (ε A eta rho : ℝ)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        annularContractedUpperRetainedLebesgueWeightedAffineDigitJointSum
            ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedFrozenDigitJointSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hnorm :=
    tendsto_annularContractedUpperRetainedDensityFreezingNormSum_zero
      ε A eta rho hgrid k hr htime mode hmode
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦ by
      rw [norm_sub_rev]
      exact
        norm_annularContractedUpperRetainedFrozenDigitJointSum_sub_affine_le
          ε A eta rho N k hr mode hmode)
    hnorm

end

end Erdos1002
