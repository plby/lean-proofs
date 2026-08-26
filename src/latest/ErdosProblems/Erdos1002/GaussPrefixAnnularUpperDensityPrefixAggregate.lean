import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDensityAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Prefix-only density freezing for contracted upper tuples

The factorized late term contains the mean of the frozen prefix factor.
To compare that mean with the original uniform-Lebesgue prefix integral,
we also need density freezing without the future block.  This is safe:
the representative-density error is geometric in the delayed depth, so
its absolute sum over the whole polynomial tagged family tends to zero.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperDensityPrefixAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Mean of the affine-frozen prefix with the exact
Lebesgue-to-Gauss density still present. -/
def annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
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
    (gaussLebesguePrefixWeight x : ℂ) *
      gaussPrefixAffineFrozenCompactCharacter
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p) x
    ∂gaussMeasure

/-- Prefix-only density-freezing error for one contracted tag. -/
def annularContractedUpperRetainedDensityPrefixFreezingContribution
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
        (annularContractedUpperRetainedGoodWords eta rho N p) x
    ∂gaussMeasure

/-- The frozen and live-density prefix means differ by the preceding
literal contribution. -/
theorem
    annularContractedUpperRetainedFrozenPrefixMean_sub_affinePrefixMean_eq
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedFrozenPrefixMean
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
          ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedDensityPrefixFreezingContribution
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
      (annularContractedUpperRetainedGoodWords eta rho N p) x
  have hcarrierMeasurable : Measurable carrier := by
    exact
      (measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
        N
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedGoodWords eta rho N p)).mono
          (gaussPrefixMeasurableSpace_le
            (annularContractedUpperRetainedDelayedDepth p))
          le_rfl
  have hcarrier : Integrable carrier gaussMeasure := by
    have hraw :=
      (integrable_const (μ := gaussMeasure) (1 : ℂ)).bdd_mul
        hcarrierMeasurable.aestronglyMeasurable
        (Eventually.of_forall fun x ↦
          norm_gaussPrefixAffineFrozenCompactCharacter_le_one
            N
            (activeAnnularOccurrenceSignedLower k ε A)
            (activeAnnularOccurrenceSignedUpper k ε A)
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p)
            (annularContractedUpperRetainedGoodWords eta rho N p) x)
    simpa only [mul_one, carrier] using! hraw
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
  have hfrozen :
      Integrable
        (fun x ↦
          (gaussPrefixFrozenLebesgueDensity
              (annularContractedUpperRetainedDelayedDepth p) x : ℂ) *
            carrier x)
        gaussMeasure :=
    hcarrier.bdd_mul hfrozenMeasurable
      (Eventually.of_forall fun x ↦
        norm_gaussPrefixFrozenLebesgueDensity_le_two_log
          (annularContractedUpperRetainedDelayedDepth p) x)
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
  unfold annularContractedUpperRetainedFrozenPrefixMean
    gaussLateLebesgueWeightedFrozenPrefixMean
    gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
    annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
    annularContractedUpperRetainedDensityPrefixFreezingContribution
  change
    (∫ x,
        (gaussPrefixFrozenLebesgueDensity
            (annularContractedUpperRetainedDelayedDepth p) x : ℂ) *
          carrier x ∂gaussMeasure) -
      (∫ x,
        (gaussLebesguePrefixWeight x : ℂ) * carrier x ∂gaussMeasure) =
      ∫ x,
        ((gaussPrefixFrozenLebesgueDensity
              (annularContractedUpperRetainedDelayedDepth p) x -
            gaussLebesguePrefixWeight x : ℝ) : ℂ) *
          carrier x ∂gaussMeasure
  rw [← integral_sub hfrozen hlive]
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  ring

/-- One prefix-only density error has the same geometric bound as the
corresponding joint error. -/
theorem
    norm_annularContractedUpperRetainedDensityPrefixFreezingContribution_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
        ε A eta rho N k hr mode hmode p‖ ≤
      Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) := by
  unfold annularContractedUpperRetainedDensityPrefixFreezingContribution
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
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
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
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ ≤
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
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ ≤
          (Real.log 2 * (1 / 4 : ℝ) ^
              (annularContractedUpperRetainedDelayedDepth p / 2)) * 1 :=
          mul_le_mul_of_nonneg_left hprefix (by positivity)
        _ = Real.log 2 * (1 / 4 : ℝ) ^
            (annularContractedUpperRetainedDelayedDepth p / 2) := by ring
    _ = Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) := by simp

/-- Uniform transfer-rate version of the preceding one-tag bound. -/
theorem
    norm_annularContractedUpperRetainedDensityPrefixFreezingContribution_le_transferDecay
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
    ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
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
    ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
        ε A eta rho N k hr mode hmode p‖ ≤
      Real.log 2 * (1 / 4 : ℝ) ^
        (annularContractedUpperRetainedDelayedDepth p / 2) :=
      norm_annularContractedUpperRetainedDensityPrefixFreezingContribution_le
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

/-- Absolute sum of prefix-only density-freezing errors. -/
def annularContractedUpperRetainedDensityPrefixFreezingNormSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
      ε A eta rho N k hr mode hmode p‖

/-- The complete prefix-only density error tends to zero absolutely. -/
theorem
    tendsto_annularContractedUpperRetainedDensityPrefixFreezingNormSum_zero
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
        annularContractedUpperRetainedDensityPrefixFreezingNormSum
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
      unfold annularContractedUpperRetainedDensityPrefixFreezingNormSum
      exact Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop 2, hcard] with N hN hcardN
    have hcardTagged :
        Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) ≤
          annularDepthAmbientSize N ^ r := by
      rw [card_annularContractedUpperRetainedTaggedTuple_eq_nestedPairCount]
      simpa only [r] using! hcardN
    unfold annularContractedUpperRetainedDensityPrefixFreezingNormSum
    calc
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
          ε A eta rho N k hr mode hmode p‖) ≤
        ∑ _p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ((540 / 527 : ℝ) *
            ((527 / 540 : ℝ) ^ annularSeparationGap N *
              Real.log 2)) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          norm_annularContractedUpperRetainedDensityPrefixFreezingContribution_le_transferDecay
            ε A eta rho N hgrid k hr htime mode hmode p hN
      _ =
        (Fintype.card
          (AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode) : ℝ) *
          ((540 / 527 : ℝ) *
            ((527 / 540 : ℝ) ^ annularSeparationGap N *
              Real.log 2)) := by simp
      _ ≤
        (annularDepthAmbientSize N : ℝ) ^ r *
          ((540 / 527 : ℝ) *
            ((527 / 540 : ℝ) ^ annularSeparationGap N *
              Real.log 2)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcardTagged
        · positivity
      _ = upper N := rfl
  · exact hzero

end

end Erdos1002
