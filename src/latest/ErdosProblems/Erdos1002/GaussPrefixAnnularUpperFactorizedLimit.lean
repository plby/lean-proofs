import ErdosProblems.Erdos1002.GaussPrefixAnnularContractedShallowTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularFactorizedErrorTransfer
import ErdosProblems.Erdos1002.GaussPrefixGoodDepthMonotonicity
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperCovarianceAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDensityPrefixAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingAggregate
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingPhaseAsymptotic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing of the contracted upper factorized mean

The last upper-retained term is a product of a delayed-prefix mean and the
mean of the complete future digit block.  The comparison with shallow
oscillatory cancellation must be made before the future factor is discarded:
errors between the delayed and shallow prefix factors are kept multiplied by
the same complete future block and are transferred from joint estimates to
products of means by functional prefix--future mixing.

This file first records the terminal shallow factorized sum and proves its
vanishing directly from the already audited contracted shallow cancellation.
The delayed-to-shallow comparison is developed below this terminal step.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 3000000

local instance gaussPrefixAnnularUpperFactorizedLimitPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Prefix-only live and freezing envelopes -/

/-- The delayed-prefix live mean under Gauss measure, with the exact
Lebesgue density.  This is exactly the corresponding uniform-Lebesgue
mean by change of measure, but this form can be compared pointwise with
the affine-frozen prefix mean. -/
def annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
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
      (gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)).indicator
        (gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p)) x
    ∂gaussMeasure

/-- Prefix-only deterministic freezing envelope, restricted to the same
delayed denominator-good event. -/
def annularContractedUpperRetainedPrefixFreezingEnvelope
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) : ℝ :=
  (gaussDenominatorPrefixGoodEvent
    (annularContractedUpperRetainedDelayedDepth p)
    (annularDepthAmbientSize N)
    (upperGoodTransferDenominatorTolerance eta rho)).indicator
    (annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
      ε A eta rho N k hr mode hmode p) x

private theorem
    prefixOnlyOscillatoryFreezingEnvelope_le_of_phaseCoefficient_le
    {r : ℕ} (a b coordinate : Fin r → ℝ)
    (K phaseRadius valueRadius phaseCoefficient : ℝ)
    (hphase :
      2 * Real.pi * |K| * phaseRadius ≤ phaseCoefficient) :
    oscillatoryPrefixFreezingEnvelope
        a b coordinate K phaseRadius valueRadius ≤
      phaseCoefficient *
          closedIntervalIndicatorProduct
            (fun i ↦ a i - valueRadius)
            (fun i ↦ b i + valueRadius) coordinate +
        ∑ i,
          closedIntervalBoundaryIndicator
              (a i) (b i) valueRadius (coordinate i) *
            ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
              closedIntervalIndicator
                (a j - valueRadius) (b j + valueRadius)
                (coordinate j) := by
  unfold oscillatoryPrefixFreezingEnvelope
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right hphase
    unfold closedIntervalIndicatorProduct
    exact Finset.prod_nonneg fun i _hi ↦ by
      unfold closedIntervalIndicator
      split <;> positivity
  · exact le_rfl

/-- Prefix-only version of the pointwise freezing estimate.  The proof
uses the actual selected delayed word, proves that it is denominator
bounded by `N`, and then applies the audited common-good-cylinder
freezing estimate. -/
theorem
    norm_weightedLivePrefix_sub_weightedAffinePrefix_le_freezingEnvelope
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ))
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0) :
    ‖(gaussLebesguePrefixWeight x : ℂ) *
          (gaussDenominatorPrefixGoodEvent
            (annularContractedUpperRetainedDelayedDepth p)
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho)).indicator
            (gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)) x -
        (gaussLebesguePrefixWeight x : ℂ) *
          gaussPrefixAffineFrozenCompactCharacter
            N
            (activeAnnularOccurrenceSignedLower k ε A)
            (activeAnnularOccurrenceSignedUpper k ε A)
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p)
            (annularContractedUpperRetainedGoodWords eta rho N p) x‖ ≤
      (2 * Real.log 2) *
        annularContractedUpperRetainedPrefixFreezingEnvelope
          ε A eta rho N k hr mode hmode p x := by
  classical
  let G :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  by_cases hxGood : x ∈ G
  · let b := annularContractedUpperRetainedDelayedDepth p
    let d := annularContractedUpperRetainedShallowDepth p
    let selected : PositiveDigitWord b := selectedGaussPrefixWord b x
    have hden :
        cfTerminalDenominator selected.1 ≤ N := by
      exact
        selectedDelayedTerminalDenominator_le_of_prefixGood
          hgrid htime p hN hW hmargin (by
            simpa only [G] using! hxGood)
    have hbpos : 0 < b := by
      have hsepPos : 0 < annularSeparationGap N :=
        Nat.sqrt_pos.mpr (by
          unfold annularDepthAmbientSize
          omega)
      have hfloor :=
        annularSeparationGap_le_annularUpperRetainedDelayedSplitDepth
          hgrid htime (annularContractedUpperRetainedUpperTag p)
          (by omega)
      exact hsepPos.trans_le (by
        simpa only [b, annularContractedUpperRetainedDelayedDepth,
          annularContractedUpperRetainedUpperTag] using! hfloor)
    have hnonempty : selected.1 ≠ [] := by
      intro hempty
      have hlen : selected.1.length = 0 := by simp [hempty]
      rw [selected.2.1] at hlen
      omega
    let bounded : BoundedPositiveTerminalWord N :=
      ⟨selected.1, hnonempty, selected.2.2, hden⟩
    let w : ExactDepthBoundedPositiveWord N b :=
      ⟨bounded, selected.2.1⟩
    have hwToPositive : w.toPositive = selected := by
      rfl
    have hxDomain : x ∈ positivePrefixDomain b :=
      mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
    have hxCylinder :
        x ∈ exactDepthBoundedCylinder w := by
      change x ∈ positivePrefixCylinder b w.toPositive
      rw [hwToPositive]
      exact selectedGaussPrefixWord_mem hxDomain
    have hwGood :
        w.toPositive ∈
          annularContractedUpperRetainedGoodWords eta rho N p := by
      simpa only [annularContractedUpperRetainedGoodWords,
        G, gaussDenominatorPrefixGoodEvent, Set.mem_preimage,
        b, hwToPositive] using! hxGood
    let e := annularContractedUpperRetainedPrefixOccurrenceEquiv p
    let s := annularContractedUpperRetainedCenterDepth p
    have hpoint :=
      norm_mixedPrefixCharacter_sub_affineFrozen_le_commonGoodEnvelope
        N hN
        (activeAnnularOccurrenceSignedLower k ε A)
        (activeAnnularOccurrenceSignedUpper k ε A)
        (abs_activeAnnularOccurrenceSignedLower_le
          hε hεA hgrid hsigned)
        (abs_activeAnnularOccurrenceSignedUpper_le
          hε hεA hgrid hsigned)
        hsmall k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedShallowDepth_le_delayed p)
        (annularContractedUpperRetainedPrefixOccurrence_depth_le_shallow
          hgrid htime p hN hW)
        w hwGood e
        (annularContractedUpperRetainedGoodWords eta rho N p)
        hwGood hxUnit hxNonterm hxCylinder
    have hsle :
        s ≤ b := by
      exact
        (annularContractedUpperRetainedCenterDepth_le_shallow
          hgrid htime p hN hW).trans
          (annularContractedUpperRetainedShallowDepth_le_delayed p)
    have hphaseMajorant :
        2 * Real.pi *
              |(N : ℝ) *
                gaussPrefixWordMixedPrefixCarrier N k
                  (unflattenedAnnularFourierMode p.1 (mode p.1))
                  (annularContractedUpperRetainedRealization p).1
                  b selected| *
              gaussPrefixGoodCylinderPhaseRadius b
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho) ≤
            annularContractedUpperRetainedPhaseFreezingMajorant
              eta rho N k hr mode hmode p := by
      simpa only [
        annularContractedUpperRetainedPhaseFreezingMajorant,
        b, s, selected] using!
        (goodEnvelope_phaseCoefficient_le
          N k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          hsle
          selected hwGood
          (fun z hz ↦ by
            simpa only using!
              annularContractedUpperRetained_nonzero_depth_le_center
                p z.1 hz))
    have hrawLe :
        annularContractedUpperRetainedCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x ≤
          annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x := by
      unfold annularContractedUpperRetainedCharacterFreezingEnvelope
        annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
      apply prefixOnlyOscillatoryFreezingEnvelope_le_of_phaseCoefficient_le
      simpa only [b, d, selected] using! hphaseMajorant
    rw [Set.indicator_of_mem (by simpa only [G] using! hxGood)]
    have hweight :
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ ≤
          2 * Real.log 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hxIcc : x ∈ Icc (0 : ℝ) 1 :=
        ⟨hxUnit.1.le, hxUnit.2.le⟩
      have hbounds := gaussLebesguePrefixWeight_bounds hxIcc
      have hnonneg :
          0 ≤ gaussLebesguePrefixWeight x :=
        (Real.log_pos one_lt_two).le.trans hbounds.1
      simpa only [abs_of_nonneg hnonneg] using! hbounds.2
    rw [← mul_sub, norm_mul]
    calc
      ‖(gaussLebesguePrefixWeight x : ℂ)‖ *
          ‖gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) x -
            gaussPrefixAffineFrozenCompactCharacter
              N
              (activeAnnularOccurrenceSignedLower k ε A)
              (activeAnnularOccurrenceSignedUpper k ε A)
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p)
              (annularContractedUpperRetainedGoodWords eta rho N p) x‖ ≤
        (2 * Real.log 2) *
          annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
            ε A eta rho N k hr mode hmode p x := by
        apply mul_le_mul hweight
        · apply le_trans ?_ hrawLe
          simpa only [
            annularContractedUpperRetainedCharacterFreezingEnvelope,
            e, b, d, selected, hwToPositive] using! hpoint
        · exact norm_nonneg _
        · exact (mul_nonneg (by positivity) (by positivity))
      _ =
        (2 * Real.log 2) *
          annularContractedUpperRetainedPrefixFreezingEnvelope
            ε A eta rho N k hr mode hmode p x := by
        unfold annularContractedUpperRetainedPrefixFreezingEnvelope
        rw [Set.indicator_of_mem (by simpa only [G] using! hxGood)]
  · have hxNotWords :
        selectedGaussPrefixWord
            (annularContractedUpperRetainedDelayedDepth p) x ∉
          annularContractedUpperRetainedGoodWords eta rho N p := by
      simpa only [G, annularContractedUpperRetainedGoodWords,
        gaussDenominatorPrefixGoodEvent, Set.mem_preimage] using! hxGood
    rw [Set.indicator_of_notMem (by simpa only [G] using! hxGood)]
    unfold gaussPrefixAffineFrozenCompactCharacter
    dsimp only
    rw [if_neg hxNotWords]
    simp only [mul_zero, sub_zero, norm_zero]
    unfold annularContractedUpperRetainedPrefixFreezingEnvelope
    rw [Set.indicator_of_notMem (by simpa only [G] using! hxGood)]
    positivity

/-- Denominator-good enlarged phase event on the delayed prefix alone. -/
def annularContractedUpperRetainedGoodPrefixPhaseEvent
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho) ∩
    annularContractedUpperRetainedPrefixPhaseEvent
      ε A eta rho N p

/-- Denominator-good endpoint-strip event on the delayed prefix alone. -/
def annularContractedUpperRetainedGoodPrefixBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) : Set ℝ :=
  gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho) ∩
    annularContractedUpperRetainedPrefixBoundaryEvent
      ε A eta rho N p j

theorem
    measurableSet_annularContractedUpperRetainedGoodPrefixPhaseEvent
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    MeasurableSet
      (annularContractedUpperRetainedGoodPrefixPhaseEvent
        ε A eta rho N p) := by
  exact
    (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).inter
      (measurableSet_annularContractedUpperRetainedPrefixPhaseEvent
        ε A eta rho N p)

theorem
    measurableSet_annularContractedUpperRetainedGoodPrefixBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    MeasurableSet
      (annularContractedUpperRetainedGoodPrefixBoundaryEvent
        ε A eta rho N p j) := by
  exact
    (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).inter
      (measurableSet_annularContractedUpperRetainedPrefixBoundaryEvent
        ε A eta rho N p j)

/-- Exact event decomposition of the prefix-only freezing envelope. -/
theorem annularContractedUpperRetainedPrefixFreezingEnvelope_eq_events
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) :
    annularContractedUpperRetainedPrefixFreezingEnvelope
        ε A eta rho N k hr mode hmode p x =
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        (annularContractedUpperRetainedGoodPrefixPhaseEvent
          ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x +
      ∑ j,
        (annularContractedUpperRetainedGoodPrefixBoundaryEvent
          ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x := by
  unfold annularContractedUpperRetainedPrefixFreezingEnvelope
  by_cases hx :
      x ∈ gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)
  · rw [Set.indicator_of_mem hx,
      annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope_eq]
    have hphase :
        (annularContractedUpperRetainedGoodPrefixPhaseEvent
            ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x =
          (annularContractedUpperRetainedPrefixPhaseEvent
            ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x := by
      by_cases hp :
          x ∈ annularContractedUpperRetainedPrefixPhaseEvent
            ε A eta rho N p
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (by exact ⟨hx, hp⟩)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (by
            intro h
            exact hp h.2)]
    have hboundary :
        ∀ j,
          (annularContractedUpperRetainedGoodPrefixBoundaryEvent
              ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x =
            (annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x := by
      intro j
      by_cases hb :
          x ∈ annularContractedUpperRetainedPrefixBoundaryEvent
            ε A eta rho N p j
      · rw [Set.indicator_of_mem hb,
          Set.indicator_of_mem (by exact ⟨hx, hb⟩)]
      · rw [Set.indicator_of_notMem hb,
          Set.indicator_of_notMem (by
            intro h
            exact hb h.2)]
    rw [hphase]
    simp_rw [hboundary]
  · rw [Set.indicator_of_notMem hx]
    have hphase :
        x ∉ annularContractedUpperRetainedGoodPrefixPhaseEvent
          ε A eta rho N p := by
      intro h
      exact hx h.1
    have hboundary :
        ∀ j,
          x ∉ annularContractedUpperRetainedGoodPrefixBoundaryEvent
            ε A eta rho N p j := by
      intro j h
      exact hx h.1
    rw [Set.indicator_of_notMem hphase]
    simp_rw [Set.indicator_of_notMem (hboundary _)]
    simp

/-- Integrated prefix envelope is exactly a phase mass plus the sum of
the delayed-prefix endpoint-strip masses. -/
theorem integral_annularContractedUpperRetainedPrefixFreezingEnvelope_eq
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    (∫ x,
      annularContractedUpperRetainedPrefixFreezingEnvelope
        ε A eta rho N k hr mode hmode p x ∂gaussMeasure) =
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        gaussMeasure.real
          (annularContractedUpperRetainedGoodPrefixPhaseEvent
            ε A eta rho N p) +
      ∑ j,
        gaussMeasure.real
          (annularContractedUpperRetainedGoodPrefixBoundaryEvent
            ε A eta rho N p j) := by
  have hphase :=
    measurableSet_annularContractedUpperRetainedGoodPrefixPhaseEvent
      ε A eta rho N p
  have hboundary :
      ∀ j, MeasurableSet
        (annularContractedUpperRetainedGoodPrefixBoundaryEvent
          ε A eta rho N p j) :=
    measurableSet_annularContractedUpperRetainedGoodPrefixBoundaryEvent
      ε A eta rho N p
  rw [integral_congr_ae
    (ae_of_all gaussMeasure fun x ↦
      annularContractedUpperRetainedPrefixFreezingEnvelope_eq_events
        ε A eta rho N k hr mode hmode p x)]
  rw [integral_add
    (((integrable_const (1 : ℝ)).indicator hphase).const_mul _)
    (integrable_finset_sum _ fun j _hj ↦
      (integrable_const (1 : ℝ)).indicator (hboundary j))]
  rw [integral_const_mul,
    integral_finset_sum _ (fun j _hj ↦
      (integrable_const (1 : ℝ)).indicator (hboundary j))]
  congr 1
  · exact congrArg
      (fun t : ℝ ↦
        annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p * t)
      (integral_indicator_one hphase)
  · apply Finset.sum_congr rfl
    intro j _hj
    exact integral_indicator_one (hboundary j)

/-- Integrated one-tag prefix-freezing error, still expressed through
prefix event masses.  No future factor has been discarded: this estimate
will only be multiplied by the same complete future mean downstream. -/
theorem
    norm_livePrefixMean_sub_affinePrefixMean_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
          ε A eta rho N k hr mode hmode p‖ ≤
      (2 * Real.log 2) *
        (annularContractedUpperRetainedPhaseFreezingMajorant
              eta rho N k hr mode hmode p *
            gaussMeasure.real
              (annularContractedUpperRetainedGoodPrefixPhaseEvent
                ε A eta rho N p) +
          ∑ j,
            gaussMeasure.real
              (annularContractedUpperRetainedGoodPrefixBoundaryEvent
                ε A eta rho N p j)) := by
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let G :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let pref : ℝ → ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
  let affine : ℝ → ℂ :=
    gaussPrefixAffineFrozenCompactCharacter
      N
      (activeAnnularOccurrenceSignedLower k ε A)
      (activeAnnularOccurrenceSignedUpper k ε A)
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
      (annularContractedUpperRetainedGoodWords eta rho N p)
  let f : ℝ → ℂ := fun x ↦
    (gaussLebesguePrefixWeight x : ℂ) * G.indicator pref x
  let g : ℝ → ℂ := fun x ↦
    (gaussLebesguePrefixWeight x : ℂ) * affine x
  have hprefixMeas : Measurable pref := by
    dsimp only [pref]
    unfold gaussPrefixMarkedMixedPrefixCharacter
    apply Finset.measurable_fun_prod
    intro z _hz
    exact measurable_gaussPrefixMarkedDepthCharacter N
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2)
      (measurableSet_compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A z.1)
        (activeAnnularOccurrenceSignedUpper k ε A z.1))
      (unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2)
  have haffineMeas : Measurable affine := by
    dsimp only [affine]
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
            (annularContractedUpperRetainedDelayedDepth p)) le_rfl
  have hfMeas : Measurable f :=
    measurable_gaussLebesguePrefixWeight.complex_ofReal.mul
      (hprefixMeas.indicator
        (measurableSet_gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)))
  have hgMeas : Measurable g :=
    measurable_gaussLebesguePrefixWeight.complex_ofReal.mul haffineMeas
  have hweight :
      ∀ᵐ x ∂gaussMeasure,
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ ≤
          2 * Real.log 2 := by
    filter_upwards [gaussMeasure_unit_ae] with x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hb := gaussLebesguePrefixWeight_bounds hxIcc
    have hnonneg :
        0 ≤ gaussLebesguePrefixWeight x :=
      (Real.log_pos one_lt_two).le.trans hb.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hb.2
  have hfInt : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable (2 * Real.log 2)
    filter_upwards [hweight] with x hweightx
    dsimp only [f]
    by_cases hxG : x ∈ G
    · rw [Set.indicator_of_mem hxG, norm_mul]
      have hpref :
          ‖pref x‖ ≤ 1 := by
        simpa only [pref, B] using!
          norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
            N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p) x
      calc
        ‖(gaussLebesguePrefixWeight x : ℂ)‖ * ‖pref x‖ ≤
            (2 * Real.log 2) * ‖pref x‖ :=
          mul_le_mul_of_nonneg_right hweightx (norm_nonneg _)
        _ ≤ (2 * Real.log 2) * 1 := by
          exact mul_le_mul_of_nonneg_left hpref
            (mul_nonneg (by norm_num)
              (Real.log_pos one_lt_two).le)
        _ = 2 * Real.log 2 := mul_one _
    · rw [Set.indicator_of_notMem hxG, norm_mul, norm_zero, mul_zero]
      exact mul_nonneg (by norm_num) (Real.log_pos one_lt_two).le
  have hgInt : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgMeas.aestronglyMeasurable (2 * Real.log 2)
    filter_upwards [hweight] with x hweightx
    dsimp only [g]
    rw [norm_mul]
    have haffine :
        ‖affine x‖ ≤ 1 := by
      simpa only [affine] using!
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
      ‖(gaussLebesguePrefixWeight x : ℂ)‖ * ‖affine x‖ ≤
          (2 * Real.log 2) * ‖affine x‖ :=
        mul_le_mul_of_nonneg_right hweightx (norm_nonneg _)
      _ ≤ (2 * Real.log 2) * 1 := by
        exact mul_le_mul_of_nonneg_left haffine
          (mul_nonneg (by norm_num) (Real.log_pos one_lt_two).le)
      _ = 2 * Real.log 2 := mul_one _
  have henvelopeInt :
      Integrable
        (fun x ↦
          (2 * Real.log 2) *
            annularContractedUpperRetainedPrefixFreezingEnvelope
              ε A eta rho N k hr mode hmode p x)
        gaussMeasure := by
    have hphase :=
      measurableSet_annularContractedUpperRetainedGoodPrefixPhaseEvent
        ε A eta rho N p
    have hboundary :
        ∀ j, MeasurableSet
          (annularContractedUpperRetainedGoodPrefixBoundaryEvent
            ε A eta rho N p j) :=
      measurableSet_annularContractedUpperRetainedGoodPrefixBoundaryEvent
        ε A eta rho N p
    rw [show
      (fun x ↦
        (2 * Real.log 2) *
          annularContractedUpperRetainedPrefixFreezingEnvelope
            ε A eta rho N k hr mode hmode p x) =
        (fun x ↦
          (2 * Real.log 2) *
            (annularContractedUpperRetainedPhaseFreezingMajorant
                eta rho N k hr mode hmode p *
              (annularContractedUpperRetainedGoodPrefixPhaseEvent
                ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x +
            ∑ j,
              (annularContractedUpperRetainedGoodPrefixBoundaryEvent
                ε A eta rho N p j).indicator
                  (fun _ ↦ (1 : ℝ)) x)) by
      funext x
      rw [
        annularContractedUpperRetainedPrefixFreezingEnvelope_eq_events]]
    exact
      ((((integrable_const (1 : ℝ)).indicator hphase).const_mul
          (annularContractedUpperRetainedPhaseFreezingMajorant
            eta rho N k hr mode hmode p)).add
        (integrable_finset_sum _ fun j _hj ↦
          (integrable_const (1 : ℝ)).indicator (hboundary j))).const_mul
        (2 * Real.log 2)
  unfold
    annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
    annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
  change ‖(∫ x, f x ∂gaussMeasure) - ∫ x, g x ∂gaussMeasure‖ ≤ _
  rw [← integral_sub hfInt hgInt]
  calc
    ‖∫ x, f x - g x ∂gaussMeasure‖ ≤
        ∫ x,
          (2 * Real.log 2) *
            annularContractedUpperRetainedPrefixFreezingEnvelope
              ε A eta rho N k hr mode hmode p x ∂gaussMeasure := by
      apply norm_integral_le_of_norm_le henvelopeInt
      filter_upwards [ae_nonterminating_gaussMeasure] with x hx
      have hpoint :=
        norm_weightedLivePrefix_sub_weightedAffinePrefix_le_freezingEnvelope
          hε hεA hgrid k htime hsigned hr mode hmode p
          hN hW hsmall hmargin hx.1 hx.2
      by_cases hxG : x ∈ G
      · simpa only [f, g, pref, affine, G, B,
          Set.indicator_of_mem hxG, gaussOrbit, mul_assoc] using! hpoint
      · simpa only [f, g, pref, affine, G, B,
          Set.indicator_of_notMem hxG, gaussOrbit, mul_assoc,
          mul_zero] using! hpoint
    _ =
        (2 * Real.log 2) *
          (∫ x,
            annularContractedUpperRetainedPrefixFreezingEnvelope
              ε A eta rho N k hr mode hmode p x ∂gaussMeasure) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [
        integral_annularContractedUpperRetainedPrefixFreezingEnvelope_eq]

/-! ## Removing the frozen-density prefix error -/

/-- Factorized mean after only the frozen Lebesgue density has been
restored to the exact density.  The affine-frozen character and the
complete future mean are unchanged. -/
def annularContractedUpperRetainedAffineFactorizedMeanSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
        ε A eta rho N k hr mode hmode p *
      annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p

/-- The factorized frozen-density error is bounded by the already
summable prefix-only density error.  The future factor is retained until
the final use of its unit norm bound. -/
theorem
    norm_annularContractedUpperRetainedFactorizedMeanSum_sub_affine_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularContractedUpperRetainedFactorizedMeanSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedAffineFactorizedMeanSum
          ε A eta rho N k hr mode hmode‖ ≤
      annularContractedUpperRetainedDensityPrefixFreezingNormSum
        ε A eta rho N k hr mode hmode := by
  unfold annularContractedUpperRetainedFactorizedMeanSum
    annularContractedUpperRetainedAffineFactorizedMeanSum
    annularContractedUpperRetainedDensityPrefixFreezingNormSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        (annularContractedUpperRetainedFrozenPrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p -
          annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p)‖ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedFrozenPrefixMean
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p -
            annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
            ε A eta rho N k hr mode hmode p‖ := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [← sub_mul,
        annularContractedUpperRetainedFrozenPrefixMean_sub_affinePrefixMean_eq,
        norm_mul]
      calc
        ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
              ε A eta rho N k hr mode hmode p‖ *
            ‖annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ ≤
          ‖annularContractedUpperRetainedDensityPrefixFreezingContribution
              ε A eta rho N k hr mode hmode p‖ * 1 := by
            exact mul_le_mul_of_nonneg_left
              (norm_annularContractedUpperRetainedFutureMean_le_one
                ε A eta rho N k hr mode hmode p)
              (norm_nonneg _)
        _ = _ := mul_one _

/-- Restoring the exact density in the factorized prefix mean has
vanishing total cost. -/
theorem
    tendsto_annularContractedUpperRetainedFactorizedMeanSum_sub_affine_zero
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
      (fun N : ℕ ↦
        annularContractedUpperRetainedFactorizedMeanSum
              ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedAffineFactorizedMeanSum
              ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hdensity :=
    tendsto_annularContractedUpperRetainedDensityPrefixFreezingNormSum_zero
      ε A eta rho hgrid k hr htime mode hmode
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦
      norm_annularContractedUpperRetainedFactorizedMeanSum_sub_affine_le
        ε A eta rho N k hr mode hmode)
    hdensity

/-! ## Prefix freezing inside the factorized expression -/

/-- Factorized sum formed from the live delayed-prefix mean and the same
complete future mean. -/
def annularContractedUpperRetainedLivePrefixFactorizedMeanSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
        ε A eta rho N k hr mode hmode p *
      annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p

/-- Uniform-law version of the delayed live prefix mean. -/
def annularContractedUpperRetainedUniformLivePrefixMean
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x in
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho),
    gaussPrefixMarkedMixedPrefixCharacter N
      (fun i ↦ compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A i)
        (activeAnnularOccurrenceSignedUpper k ε A i))
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p) x
    ∂uniform01Measure

theorem
    annularContractedUpperRetainedUniformLivePrefixMean_eq_weighted
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedUniformLivePrefixMean
        ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
        ε A eta rho N k hr mode hmode p := by
  unfold annularContractedUpperRetainedUniformLivePrefixMean
    annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
  rw [← integral_indicator
    (measurableSet_gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho))]
  exact integral_uniform01_eq_integral_gaussLebesguePrefixWeight_mul _

/-- Live shallow-prefix mean on the shallow denominator-good event. -/
def annularContractedUpperRetainedShallowGoodSetIntegral
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x in
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedShallowDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho),
    gaussPrefixMarkedMixedPrefixCharacter N
      (fun i ↦ compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A i)
        (activeAnnularOccurrenceSignedUpper k ε A i))
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedShallowDepth p) x
    ∂uniform01Measure

/-- The part present at the shallow good cutoff but absent at the delayed
good cutoff. -/
def annularContractedUpperRetainedGoodDepthSliceIntegral
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x in
    gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedShallowDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) \
      gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho),
    gaussPrefixMarkedMixedPrefixCharacter N
      (fun i ↦ compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A i)
        (activeAnnularOccurrenceSignedUpper k ε A i))
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedShallowDepth p) x
    ∂uniform01Measure

/-- The shallow cutoff, together with the full retained midpoint width,
still lies below the ambient depth horizon.  This is the deterministic
room which ensures that a shallow denominator-good word has terminal
denominator at most `N` once the uniform shallow exponent is negative. -/
theorem
    annularContractedUpperRetainedShallowDepth_add_bandWidth_le_ambient
    {eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N) :
    annularContractedUpperRetainedShallowDepth p +
        annularMidpointBandWidth rho N ≤
      annularDepthAmbientSize N := by
  let q := annularContractedUpperRetainedUpperTag p
  let s := annularLastNonzeroIndex (mode q.1) (hmode q.1)
  have hupper :=
    mem_laterUpperMidpointNatTupleFamily_iff.mp q.2.2
  have hcanonical :
      annularUpperRetainedTimes q ∈
        canonicalAnnularGridTupleFamily N k q.1 := by
    exact annularUpperRetainedTimes_mem_canonical q
  have hbound :
      ∀ j, annularUpperRetainedTimes q j <
        annularDepthAmbientSize N := by
    intro j
    exact canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime (by omega) q.1
      (annularUpperRetainedTimes q) hcanonical j
  have hcenter :
      annularUpperRetainedTimes q s +
          annularMidpointBandWidth rho N <
        annularDepthAmbientSize N := by
    exact center_add_width_lt_horizon_of_upper_witness
      hbound hupper.2.2
  have hcenter' :
      annularUpperRetainedTimes
            (annularContractedUpperRetainedToUpper p)
            (annularLastNonzeroIndex
              (mode (annularContractedUpperRetainedToUpper p).1)
              (hmode (annularContractedUpperRetainedToUpper p).1)) +
          annularMidpointBandWidth rho N <
        annularDepthAmbientSize N := by
    simpa only [q, s, annularContractedUpperRetainedUpperTag] using! hcenter
  unfold annularContractedUpperRetainedShallowDepth
    annularContractedUpperRetainedUpperTag
    annularUpperRetainedShallowSplitDepth
    annularUpperRetainedSplitDepth
    midpointPrefixSplitDepth
    annularUpperRetainedGap
    midpointPrefixFutureGap
  omega

/-- Prefix-only analogue of the exact good-cylinder decomposition.  The
extra terminal inequality is essential: it proves that every
nonterminating point in the word-defined good event belongs to the finite
family of depth-`m`, denominator-`N` cylinders. -/
theorem
    setIntegral_gaussPrefixMarkedMixedPrefixCharacter_prefixGoodEvent_eq_sum
    {ι : Type*} [Fintype ι]
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i))
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {m L : ℕ} {Delta : ℝ}
    (hm : 0 < m)
    (hterminal :
      Real.exp
          ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ)) ≤
        (N : ℝ)) :
    (∫ x in gaussDenominatorPrefixGoodEvent m L Delta,
        gaussPrefixMarkedMixedPrefixCharacter N B k h F m x
          ∂uniform01Measure) =
      ∑ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        ∫ x in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N B k h F m x
            ∂uniform01Measure := by
  let f : ℝ → ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k h F m
  let G : Set ℝ := gaussDenominatorPrefixGoodEvent m L Delta
  let S : Set ℝ := exactDepthBoundedCylinderUnion N m
  have hG : MeasurableSet G :=
    measurableSet_gaussDenominatorPrefixGoodEvent m L Delta
  have hS : MeasurableSet S :=
    measurableSet_exactDepthBoundedCylinderUnion N m
  have hfMeas : Measurable f := by
    dsimp only [f]
    unfold gaussPrefixMarkedMixedPrefixCharacter
    apply Finset.measurable_fun_prod
    intro z _hz
    exact measurable_gaussPrefixMarkedDepthCharacter N
      (F z.1 z.2) (hB z.1) (h z.1 z.2)
  have hf : Integrable f uniform01Measure := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      simpa only [f] using!
        norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
          N B k h F m x
  have hsupport :
      G.indicator f =ᵐ[uniform01Measure]
        S.indicator (G.indicator f) := by
    filter_upwards [ae_nonterminating_uniform01] with x hx
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
    · rw [Set.indicator_of_notMem hxS]
      by_cases hxG : x ∈ G
      · have hdomain :
            x ∈ positivePrefixDomain m :=
          mem_positivePrefixDomain_of_nonterminating hx.1 hx.2
        let selected : PositiveDigitWord m :=
          selectedGaussPrefixWord m x
        have hxCell :
            x ∈ positivePrefixCylinder m selected := by
          exact selectedGaussPrefixWord_mem hdomain
        have hgood :
            selected ∈ gaussDenominatorPrefixGoodWords m L Delta := by
          simpa only [G, gaussDenominatorPrefixGoodEvent,
            Set.mem_preimage, selected] using! hxG
        have hupper :=
          (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
            selected hgood (le_refl m)).2
        have htake : selected.1.take m = selected.1 := by
          exact List.take_of_length_le selected.2.1.le
        have hdenReal :
            (cfTerminalDenominator selected.1 : ℝ) ≤ (N : ℝ) := by
          calc
            (cfTerminalDenominator selected.1 : ℝ) ≤
                Real.exp
                  ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ)) := by
              simpa only [positiveDigitWordTake_val, htake] using! hupper
            _ ≤ (N : ℝ) := hterminal
        have hden :
            cfTerminalDenominator selected.1 ≤ N := by
          exact_mod_cast hdenReal
        have hnonempty : selected.1 ≠ [] := by
          intro hempty
          have hlength : selected.1.length = 0 := by
            simp [hempty]
          rw [selected.2.1] at hlength
          omega
        let bounded : BoundedPositiveTerminalWord N :=
          ⟨selected.1, hnonempty, selected.2.2, hden⟩
        let exact : ExactDepthBoundedPositiveWord N m :=
          ⟨bounded, selected.2.1⟩
        have hxExact :
            x ∈ exactDepthBoundedCylinder exact := by
          exact hxCell
        have : x ∈ S :=
          Set.mem_iUnion.mpr ⟨exact, hxExact⟩
        exact (hxS this).elim
      · simp [Set.indicator_of_notMem hxG]
  have hpartition :
      (∫ x in G, f x ∂uniform01Measure) =
        ∑ w : ExactDepthBoundedPositiveWord N m,
          ∫ x in exactDepthBoundedCylinder w,
            G.indicator f x ∂uniform01Measure := by
    calc
      (∫ x in G, f x ∂uniform01Measure) =
          ∫ x, G.indicator f x ∂uniform01Measure := by
        rw [integral_indicator hG]
      _ = ∫ x, S.indicator (G.indicator f) x
            ∂uniform01Measure := by
        exact integral_congr_ae hsupport
      _ = ∫ x in S, G.indicator f x ∂uniform01Measure := by
        rw [integral_indicator hS]
      _ = ∑ w : ExactDepthBoundedPositiveWord N m,
          ∫ x in exactDepthBoundedCylinder w,
            G.indicator f x ∂uniform01Measure := by
        exact integral_iUnion_fintype
          (fun w ↦ measurableSet_exactDepthBoundedCylinder w)
          (pairwise_disjoint_exactDepthBoundedCylinder N m)
          (fun _w ↦ (hf.indicator hG).integrableOn)
  rw [hpartition]
  calc
    (∑ w : ExactDepthBoundedPositiveWord N m,
        ∫ x in exactDepthBoundedCylinder w,
          G.indicator f x ∂uniform01Measure) =
      ∑ w : ExactDepthBoundedPositiveWord N m,
        if w.toPositive ∈
            gaussDenominatorPrefixGoodWords m L Delta then
          ∫ x in exactDepthBoundedCylinder w,
            f x ∂uniform01Measure
        else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hwGood :
          w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta
      · rw [if_pos hwGood]
        rw [← integral_indicator
          (measurableSet_exactDepthBoundedCylinder w),
          ← integral_indicator
            (measurableSet_exactDepthBoundedCylinder w)]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hxCell : x ∈ exactDepthBoundedCylinder w
        · have hselected :
              selectedGaussPrefixWord m x = w.toPositive :=
            selectedGaussPrefixWord_eq_of_mem w.toPositive hxCell
          have hxG : x ∈ G := by
            simpa only [G, gaussDenominatorPrefixGoodEvent,
              Set.mem_preimage, hselected] using! hwGood
          simp [Set.indicator_of_mem hxCell,
            Set.indicator_of_mem hxG]
        · simp [Set.indicator_of_notMem hxCell]
      · rw [if_neg hwGood]
        calc
          (∫ x in exactDepthBoundedCylinder w,
              G.indicator f x ∂uniform01Measure) =
              ∫ _x : ℝ, (0 : ℂ) ∂uniform01Measure := by
            rw [← integral_indicator
              (measurableSet_exactDepthBoundedCylinder w)]
            apply integral_congr_ae
            filter_upwards with x
            by_cases hxCell : x ∈ exactDepthBoundedCylinder w
            · have hselected :
                  selectedGaussPrefixWord m x = w.toPositive :=
                selectedGaussPrefixWord_eq_of_mem w.toPositive hxCell
              have hxNotG : x ∉ G := by
                simpa only [G, gaussDenominatorPrefixGoodEvent,
                  Set.mem_preimage, hselected] using! hwGood
              simp [Set.indicator_of_mem hxCell,
                Set.indicator_of_notMem hxNotG]
            · simp [Set.indicator_of_notMem hxCell]
          _ = 0 := by simp
    _ = ∑ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        ∫ x in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N B k h F m x
            ∂uniform01Measure := by
      simp only [shallowExactDepthPrefixGoodCells,
        Finset.sum_filter, f]

/-- Negativity of the uniform shallow exponent implies that every
shallow good word is already inside the process denominator cutoff. -/
theorem
    annularContractedUpperRetainedShallowTerminalExponential_le
    {eta rho : ℝ} {N grid : ℕ}
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hexponent :
      upperRetainedShallowUniformExponent rho
          (upperGoodTransferDenominatorTolerance eta rho) N ≤ 0) :
    Real.exp
        ((annularContractedUpperRetainedShallowDepth p : ℝ) *
            gaussRoofMean +
          upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ)) ≤
      (N : ℝ) := by
  have hdepth :=
    annularContractedUpperRetainedShallowDepth_add_bandWidth_le_ambient
      hgrid k htime p hN
  have hdepthReal :
      (annularContractedUpperRetainedShallowDepth p : ℝ) +
          (annularMidpointBandWidth rho N : ℝ) ≤
        (annularDepthAmbientSize N : ℝ) := by
    exact_mod_cast hdepth
  have hmu :=
    mul_le_mul_of_nonneg_right hdepthReal gaussRoofMean_pos.le
  have hDelta :
      0 ≤ upperGoodTransferDenominatorTolerance eta rho :=
    (upperGoodTransferDenominatorTolerance_pos heta hrho).le
  have hH :
      0 ≤ (annularDepthAmbientSize N : ℝ) :=
    Nat.cast_nonneg _
  have hlogBound :
      (annularContractedUpperRetainedShallowDepth p : ℝ) *
            gaussRoofMean +
          upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ) ≤
        Real.log (N : ℝ) := by
    unfold upperRetainedShallowUniformExponent at hexponent
    nlinarith [gaussRoofMean_pos]
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  calc
    Real.exp
        ((annularContractedUpperRetainedShallowDepth p : ℝ) *
            gaussRoofMean +
          upperGoodTransferDenominatorTolerance eta rho *
            (annularDepthAmbientSize N : ℝ)) ≤
        Real.exp (Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr hlogBound
    _ = (N : ℝ) := Real.exp_log hNpos

/-- The set-integral form used by delayed-good monotonicity is exactly the
audited finite shallow-cylinder sum, once the uniform exponent has entered
its negative regime. -/
theorem
    annularContractedUpperRetainedShallowGoodSetIntegral_eq_cylinderSum
    {ε A eta rho : ℝ} {N grid : ℕ}
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hexponent :
      upperRetainedShallowUniformExponent rho
          (upperGoodTransferDenominatorTolerance eta rho) N ≤ 0) :
    annularContractedUpperRetainedShallowGoodSetIntegral
        ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
        ε A eta rho
        (upperGoodTransferDenominatorTolerance eta rho)
        N k hr mode hmode p := by
  let q := annularContractedUpperRetainedUpperTag p
  have hupper :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp q.2.2).1
  have hfirst :
      annularSeparationGap N ≤
        annularUpperRetainedTimes q ⟨0, hr⟩ :=
    (mem_lateFirstNatTupleFamily_iff.mp hupper).2
  have hfirstCenter :
      annularUpperRetainedTimes q ⟨0, hr⟩ ≤
        annularUpperRetainedTimes q
          (annularLastNonzeroIndex (mode q.1) (hmode q.1)) :=
    annularUpperRetained_firstDepth_le_centerDepth q
  have hsepPos : 0 < annularSeparationGap N :=
    Nat.sqrt_pos.mpr (by
      unfold annularDepthAmbientSize
      omega)
  have hcenterPos :
      0 <
        annularContractedUpperRetainedCenterDepth p := by
    have hraw :
        0 <
          annularUpperRetainedTimes q
            (annularLastNonzeroIndex (mode q.1) (hmode q.1)) :=
      hsepPos.trans_le (hfirst.trans hfirstCenter)
    simpa only [q, annularContractedUpperRetainedCenterDepth,
      annularContractedUpperRetainedTimes,
      annularContractedUpperRetainedUpperTag,
      ← annularContractedUpperRetainedTimes_embedding] using! hraw
  have hm :
      0 < annularContractedUpperRetainedShallowDepth p :=
    hcenterPos.trans_le
      (annularContractedUpperRetainedCenterDepth_le_shallow
        hgrid htime p hN hW)
  have hterminal :=
    annularContractedUpperRetainedShallowTerminalExponential_le
      heta hrho hgrid k htime p hN hexponent
  have hdecomp :=
    setIntegral_gaussPrefixMarkedMixedPrefixCharacter_prefixGoodEvent_eq_sum
      N
      (B := fun i ↦ compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A i)
        (activeAnnularOccurrenceSignedUpper k ε A i))
      (fun i ↦ measurableSet_compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A i)
        (activeAnnularOccurrenceSignedUpper k ε A i))
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      hm hterminal
  unfold annularContractedUpperRetainedShallowGoodSetIntegral
    annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
    annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro w _hw
  apply integral_congr_ae
  filter_upwards with x
  simpa only [activeAnnularOccurrenceSignedLower,
    activeAnnularOccurrenceSignedUpper,
    annularActiveSignedLower, annularActiveSignedUpper,
    annularContractedUpperRetainedShallowDepth,
    annularContractedUpperRetainedUpperTag,
    annularContractedUpperRetainedRealization] using!
    gaussPrefixMarkedMixedPrefixCharacter_activeEndpoints_eq
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularUpperRetainedRealization
        (annularContractedUpperRetainedToUpper p)).1
      (annularUpperRetainedShallowSplitDepth
        (annularContractedUpperRetainedToUpper p)) x

/-- Exact delayed-to-shallow decomposition.  Deeper denominator-good
implies shallower denominator-good only almost everywhere, and that is
the only exceptional-set input in this identity. -/
theorem
    annularContractedUpperRetainedUniformLivePrefixMean_eq_shallow_sub_slice
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularContractedUpperRetainedUniformLivePrefixMean
        ε A eta rho N k hr mode hmode p =
      annularContractedUpperRetainedShallowGoodSetIntegral
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedGoodDepthSliceIntegral
          ε A eta rho N k hr mode hmode p := by
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let b := annularContractedUpperRetainedDelayedDepth p
  let d := annularContractedUpperRetainedShallowDepth p
  let G_b :=
    gaussDenominatorPrefixGoodEvent b
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let G_d :=
    gaussDenominatorPrefixGoodEvent d
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let f : ℝ → ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1 d
  have hchar :
      (gaussPrefixMarkedMixedPrefixCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1 b) = f := by
    funext x
    simpa only [B, b, d,
      annularContractedUpperRetainedDelayedDepth,
      annularContractedUpperRetainedShallowDepth,
      annularContractedUpperRetainedUpperTag,
      annularContractedUpperRetainedRealization] using!
      annularUpperRetained_delayedPrefixCharacter_eq_shallow
        hgrid htime (annularContractedUpperRetainedToUpper p)
        (by omega) hW B x
  have hfMeas : Measurable f := by
    dsimp only [f]
    unfold gaussPrefixMarkedMixedPrefixCharacter
    apply Finset.measurable_fun_prod
    intro z _hz
    exact measurable_gaussPrefixMarkedDepthCharacter N
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2)
      (measurableSet_compactValueMarkedRegion
        (activeAnnularOccurrenceSignedLower k ε A z.1)
        (activeAnnularOccurrenceSignedUpper k ε A z.1))
      (unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2)
  have hfInt : Integrable f uniform01Measure := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      simpa only [f, B] using!
        norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
          N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1 d x
  have hGbMeas : MeasurableSet G_b := by
    exact measurableSet_gaussDenominatorPrefixGoodEvent _ _ _
  have hGdMeas : MeasurableSet G_d := by
    exact measurableSet_gaussDenominatorPrefixGoodEvent _ _ _
  have hdiffMeas : MeasurableSet (G_d \ G_b) :=
    hGdMeas.diff hGbMeas
  have hGbInt : Integrable (G_b.indicator f) uniform01Measure :=
    hfInt.indicator hGbMeas
  have hGdInt : Integrable (G_d.indicator f) uniform01Measure :=
    hfInt.indicator hGdMeas
  have hdiffInt : Integrable ((G_d \ G_b).indicator f) uniform01Measure :=
    hfInt.indicator hdiffMeas
  have hmono :
      G_b ≤ᵐ[uniform01Measure] G_d := by
    simpa only [G_b, G_d] using!
      gaussDenominatorPrefixGoodEvent_ae_mono_uniform
        (annularContractedUpperRetainedShallowDepth_le_delayed p)
  unfold annularContractedUpperRetainedUniformLivePrefixMean
    annularContractedUpperRetainedShallowGoodSetIntegral
    annularContractedUpperRetainedGoodDepthSliceIntegral
  change (∫ x in G_b, _ ∂uniform01Measure) =
    (∫ x in G_d, f x ∂uniform01Measure) -
      ∫ x in G_d \ G_b, f x ∂uniform01Measure
  rw [hchar]
  rw [← integral_indicator hGbMeas,
    ← integral_indicator hGdMeas,
    ← integral_indicator hdiffMeas,
    ← integral_sub hGdInt hdiffInt]
  apply integral_congr_ae
  filter_upwards [hmono] with x hx
  by_cases hxb : x ∈ G_b
  · have hxd : x ∈ G_d := hx hxb
    have hnotDiff : x ∉ G_d \ G_b := by
      intro hdiff
      exact hdiff.2 hxb
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hxd,
      Set.indicator_of_notMem hnotDiff]
    simp
  · by_cases hxd : x ∈ G_d
    · have hdiff : x ∈ G_d \ G_b := ⟨hxd, hxb⟩
      rw [Set.indicator_of_notMem hxb, Set.indicator_of_mem hxd,
        Set.indicator_of_mem hdiff]
      simp
    · have hnotDiff : x ∉ G_d \ G_b := by
        intro hdiff
        exact hxd hdiff.1
      rw [Set.indicator_of_notMem hxb, Set.indicator_of_notMem hxd,
        Set.indicator_of_notMem hnotDiff]
      simp

/-- Sum of products of delayed-prefix boundary masses and the complete
future means.  This is the quantity to which full-event mass plus
functional mixing will be applied. -/
def annularContractedUpperRetainedGoodPrefixBoundaryProductSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ∑ j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))),
      gaussMeasure.real
          (annularContractedUpperRetainedGoodPrefixBoundaryEvent
            ε A eta rho N p j) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖

/-- Finite-scale prefix-freezing comparison after factorization.  The
phase term is removed only through its exponentially small scalar.  Every
boundary probability remains multiplied by the same future mean. -/
theorem
    norm_affineFactorizedMeanSum_sub_livePrefix_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedAffineFactorizedMeanSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedLivePrefixFactorizedMeanSum
          ε A eta rho N k hr mode hmode‖ ≤
      (2 * Real.log 2) *
        ((∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPhaseFreezingMajorant
            eta rho N k hr mode hmode p) +
          annularContractedUpperRetainedGoodPrefixBoundaryProductSum
            ε A eta rho N k hr mode hmode) := by
  unfold annularContractedUpperRetainedAffineFactorizedMeanSum
    annularContractedUpperRetainedLivePrefixFactorizedMeanSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        (annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p -
          annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p)‖ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p -
            annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          (2 * Real.log 2) *
            (annularContractedUpperRetainedPhaseFreezingMajorant
                eta rho N k hr mode hmode p +
              ∑ j : Fin (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k
                  (annularContractedUpperRetainedRealization p).1
                  (annularContractedUpperRetainedDelayedDepth p))),
                gaussMeasure.real
                    (annularContractedUpperRetainedGoodPrefixBoundaryEvent
                      ε A eta rho N p j) *
                  ‖annularContractedUpperRetainedFutureMean
                    ε A eta rho N k hr mode hmode p‖) := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [← sub_mul, norm_mul, norm_sub_rev]
      have hprefix :=
        norm_livePrefixMean_sub_affinePrefixMean_le
          hε hεA hgrid k htime hsigned hr mode hmode p
          hN hW hsmall hmargin
      have hfuture :=
        norm_annularContractedUpperRetainedFutureMean_le_one
          ε A eta rho N k hr mode hmode p
      have hphaseMass :
          gaussMeasure.real
              (annularContractedUpperRetainedGoodPrefixPhaseEvent
                ε A eta rho N p) ≤ 1 := by
        exact measureReal_le_one
      calc
        ‖annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
              ε A eta rho N k hr mode hmode p -
            annularContractedUpperRetainedLebesgueWeightedAffinePrefixMean
              ε A eta rho N k hr mode hmode p‖ *
            ‖annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ ≤
          ((2 * Real.log 2) *
            (annularContractedUpperRetainedPhaseFreezingMajorant
                  eta rho N k hr mode hmode p *
                gaussMeasure.real
                  (annularContractedUpperRetainedGoodPrefixPhaseEvent
                    ε A eta rho N p) +
              ∑ j,
                gaussMeasure.real
                    (annularContractedUpperRetainedGoodPrefixBoundaryEvent
                      ε A eta rho N p j))) *
            ‖annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ := by
          exact mul_le_mul_of_nonneg_right hprefix (norm_nonneg _)
        _ ≤
          (2 * Real.log 2) *
            (annularContractedUpperRetainedPhaseFreezingMajorant
                eta rho N k hr mode hmode p +
              ∑ j,
                gaussMeasure.real
                    (annularContractedUpperRetainedGoodPrefixBoundaryEvent
                      ε A eta rho N p j) *
                  ‖annularContractedUpperRetainedFutureMean
                    ε A eta rho N k hr mode hmode p‖) := by
          have hphaseNonneg :
              0 ≤ annularContractedUpperRetainedPhaseFreezingMajorant
                eta rho N k hr mode hmode p := by
            unfold annularContractedUpperRetainedPhaseFreezingMajorant
            positivity
          have hlogNonneg : 0 ≤ 2 * Real.log 2 :=
            mul_nonneg (by norm_num) (Real.log_pos one_lt_two).le
          rw [mul_assoc, add_mul, Finset.sum_mul]
          apply mul_le_mul_of_nonneg_left _ hlogNonneg
          apply add_le_add
          · calc
              annularContractedUpperRetainedPhaseFreezingMajorant
                    eta rho N k hr mode hmode p *
                  gaussMeasure.real
                    (annularContractedUpperRetainedGoodPrefixPhaseEvent
                      ε A eta rho N p) *
                  ‖annularContractedUpperRetainedFutureMean
                    ε A eta rho N k hr mode hmode p‖ ≤
                annularContractedUpperRetainedPhaseFreezingMajorant
                    eta rho N k hr mode hmode p * 1 * 1 := by
                  gcongr
              _ =
                annularContractedUpperRetainedPhaseFreezingMajorant
                  eta rho N k hr mode hmode p := by ring
          · exact le_rfl
    _ = _ := by
      unfold
        annularContractedUpperRetainedGoodPrefixBoundaryProductSum
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Terminal shallow factorized sum -/

/-- The factorized expression after the delayed prefix has been replaced by
the shallow prefix-good oscillatory integral.  The complete future mean is
still the one attached to the original contracted tag. -/
def annularContractedUpperRetainedShallowFactorizedMeanSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
        ε A eta rho
        (upperGoodTransferDenominatorTolerance eta rho)
        N k hr mode hmode p *
      annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p

/-- Once the shallow finite-cylinder identity is available, the complete
live-factorized minus shallow-factorized error is bounded by the sum of
the depth-slice products.  In particular, the future mean is retained in
every summand. -/
theorem
    norm_annularContractedUpperRetainedLivePrefixFactorizedMeanSum_sub_shallow_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hexponent :
      upperRetainedShallowUniformExponent rho
          (upperGoodTransferDenominatorTolerance eta rho) N ≤ 0) :
    ‖annularContractedUpperRetainedLivePrefixFactorizedMeanSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedShallowFactorizedMeanSum
          ε A eta rho N k hr mode hmode‖ ≤
      ∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedGoodDepthSliceIntegral
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ := by
  unfold annularContractedUpperRetainedLivePrefixFactorizedMeanSum
    annularContractedUpperRetainedShallowFactorizedMeanSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        (annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p -
          annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
              ε A eta rho
              (upperGoodTransferDenominatorTolerance eta rho)
              N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p)‖ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedLebesgueWeightedLivePrefixMean
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p -
            annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
                ε A eta rho
                (upperGoodTransferDenominatorTolerance eta rho)
                N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [←
        annularContractedUpperRetainedUniformLivePrefixMean_eq_weighted
          ε A eta rho N k hr mode hmode p]
      rw [
        annularContractedUpperRetainedUniformLivePrefixMean_eq_shallow_sub_slice
          hgrid k htime hr mode hmode p hN hW,
        annularContractedUpperRetainedShallowGoodSetIntegral_eq_cylinderSum
          heta hrho hgrid k htime hr mode hmode p hN hW hexponent]
      ring_nf
      exact norm_neg _

/-- At each finite scale the shallow factorized sum is bounded by the
absolute shallow prefix sum.  The future factor is removed only here, after
factorization, via its probability bound `‖E 1_U‖ ≤ 1`; no error integrand
has lost its future event. -/
theorem norm_annularContractedUpperRetainedShallowFactorizedMeanSum_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularContractedUpperRetainedShallowFactorizedMeanSum
        ε A eta rho N k hr mode hmode‖ ≤
      ∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A eta rho
          (upperGoodTransferDenominatorTolerance eta rho)
          N k hr mode hmode p‖ := by
  unfold annularContractedUpperRetainedShallowFactorizedMeanSum
  calc
    ‖∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A eta rho
          (upperGoodTransferDenominatorTolerance eta rho)
          N k hr mode hmode p *
        annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
              ε A eta rho
              (upperGoodTransferDenominatorTolerance eta rho)
              N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
            ε A eta rho
            (upperGoodTransferDenominatorTolerance eta rho)
            N k hr mode hmode p‖ := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [norm_mul]
      calc
        ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
              ε A eta rho
              (upperGoodTransferDenominatorTolerance eta rho)
              N k hr mode hmode p‖ *
            ‖annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖ ≤
          ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
            ε A eta rho
            (upperGoodTransferDenominatorTolerance eta rho)
            N k hr mode hmode p‖ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (norm_annularContractedUpperRetainedFutureMean_le_one
              ε A eta rho N k hr mode hmode p)
            (norm_nonneg _)
        _ = _ := by ring

/-- The terminal shallow factorized contribution vanishes absolutely. -/
theorem
    tendsto_annularContractedUpperRetainedShallowFactorizedMeanSum_zero
    {ε A eta rho : ℝ}
    (hε : 0 < ε) (hεA : ε < A)
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
        annularContractedUpperRetainedShallowFactorizedMeanSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hDelta :
      0 ≤ upperGoodTransferDenominatorTolerance eta rho :=
    (upperGoodTransferDenominatorTolerance_pos heta hrho).le
  have hDeltaUpper :
      upperGoodTransferDenominatorTolerance eta rho ≤
        upperRetainedShallowDenominatorTolerance rho :=
    upperGoodTransferDenominatorTolerance_le_rhoSixth hrho.le
  have hshallow :=
    tendsto_sum_norm_annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance_zero
      (eta := eta)
      (Delta := upperGoodTransferDenominatorTolerance eta rho)
      hε hεA hrho hDelta hDeltaUpper hgrid k hr htime hsigned mode hmode
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦
      norm_annularContractedUpperRetainedShallowFactorizedMeanSum_le
        ε A eta rho N k hr mode hmode)
    hshallow

end

end Erdos1002
