import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFactorizedLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperDigitTransfer
import ErdosProblems.Erdos1002.GaussPrefixDigitMeasurability
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperBoundaryProductAsymptotic
import ErdosProblems.Erdos1002.GaussUniformAggregateTransfer
import ErdosProblems.Erdos1002.GaussMeasureUniformBound
import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralTransferLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The delayed-good depth slice with its future block retained

The difference between shallow and delayed denominator-good cutoffs is
estimated only after multiplication by the complete future digit mean.
The exact prefix windows are first dominated, off the terminating null set,
by one fixed homogeneous enlarged one-digit window.  This gives a genuine
finite-prefix event.  Prefix--future relative mixing then turns the product
of its prefix and future masses into a joint mass.  The prefix-bad factor
places this joint mass inside the global denominator-bad event; the latter
is deleted by the audited high-moment estimate after an all-coordinate
exact-to-digit replacement.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 3000000

local instance gaussPrefixAnnularUpperGoodDepthSlicePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-! ## A genuinely prefix-measurable homogeneous digit mask -/

/-- Chronological coordinates which belong to the exact midpoint prefix. -/
def annularContractedUpperRetainedPrefixIndexSet
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Finset (Fin (MixedOccurrenceCount k)) :=
  Finset.univ.filter fun j ↦
    annularContractedUpperRetainedTimes p j ≤
      annularUpperRetainedSplitDepth
        (annularContractedUpperRetainedUpperTag p)

/-- A single homogeneous enlarged one-digit window containing every
oriented prefix window in the fixed compact annulus. -/
def annularContractedUpperRetainedHomogeneousEnlargedDigitEvent
    (ε A : ℝ) (N : ℕ) : Set ℝ :=
  gaussEnlargedDigitWindow (Real.log (N : ℝ)) ε A

/-- Selected-word realization of the homogeneous digit mask on all prefix
coordinates.  The positive-offset hypothesis is automatic at all
sufficiently large scales and puts every active coordinate strictly before
the delayed depth. -/
def annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N) : Set ℝ :=
  gaussPrefixSelectedMaskedOneDigitTupleEvent
    (annularContractedUpperRetainedPrefixIndexSet p)
    (annularContractedUpperRetainedDelayedDepth p)
    (annularContractedUpperRetainedTimes p)
    (fun j hj ↦ by
      have hsplit :
          annularContractedUpperRetainedTimes p j ≤
            annularUpperRetainedSplitDepth
              (annularContractedUpperRetainedUpperTag p) := by
        exact (Finset.mem_filter.mp hj).2
      simp only [annularContractedUpperRetainedUpperTag] at hsplit
      unfold annularContractedUpperRetainedDelayedDepth
        annularUpperRetainedDelayedSplitDepth
        annularUpperRetainedFreezingOffset
      change 0 < annularUpperRetainedGap rho N / 2 at hoff
      omega)
    (fun _j ↦
      annularContractedUpperRetainedHomogeneousEnlargedDigitEvent ε A N)
    (fun _j _hj ↦
      isGaussOneDigitEvent_gaussEnlargedDigitWindow _ _ _)

theorem
    measurableSet_annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N) :
    @MeasurableSet ℝ
      (gaussPrefixMeasurableSpace
        (annularContractedUpperRetainedDelayedDepth p))
      (annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
        ε A eta rho N p hoff) := by
  unfold
    annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
  exact
    measurableSet_gaussPrefixSelectedMaskedOneDigitTupleEvent
      (annularContractedUpperRetainedPrefixIndexSet p)
      (annularContractedUpperRetainedDelayedDepth p)
      (annularContractedUpperRetainedTimes p)
      (fun j hj ↦ by
        have hsplit :
            annularContractedUpperRetainedTimes p j ≤
              annularUpperRetainedSplitDepth
                (annularContractedUpperRetainedUpperTag p) := by
          exact (Finset.mem_filter.mp hj).2
        simp only [annularContractedUpperRetainedUpperTag] at hsplit
        unfold annularContractedUpperRetainedDelayedDepth
          annularUpperRetainedDelayedSplitDepth
          annularUpperRetainedFreezingOffset
        change 0 < annularUpperRetainedGap rho N / 2 at hoff
        omega)
      (fun _j ↦
        annularContractedUpperRetainedHomogeneousEnlargedDigitEvent ε A N)
      (fun _j _hj ↦
        isGaussOneDigitEvent_gaussEnlargedDigitWindow _ _ _)

/-- The raw orbit form of the same prefix mask agrees almost everywhere
with its selected-word realization. -/
theorem
    ae_rawHomogeneousPrefixDigitEvent_eq_selected
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N) :
    (⋂ j, if j ∈ annularContractedUpperRetainedPrefixIndexSet p then
        (gaussOrbit (annularContractedUpperRetainedTimes p j)) ⁻¹'
          annularContractedUpperRetainedHomogeneousEnlargedDigitEvent
            ε A N
      else Set.univ) =ᵐ[gaussMeasure]
      annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
        ε A eta rho N p hoff := by
  simpa only [
      annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent]
    using!
      iInter_masked_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
        (annularContractedUpperRetainedPrefixIndexSet p)
        (annularContractedUpperRetainedTimes p)
        (fun j hj ↦ by
          have hsplit :
              annularContractedUpperRetainedTimes p j ≤
                annularUpperRetainedSplitDepth
                  (annularContractedUpperRetainedUpperTag p) := by
            exact (Finset.mem_filter.mp hj).2
          simp only [annularContractedUpperRetainedUpperTag] at hsplit
          unfold annularContractedUpperRetainedDelayedDepth
            annularUpperRetainedDelayedSplitDepth
            annularUpperRetainedFreezingOffset
          change 0 < annularUpperRetainedGap rho N / 2 at hoff
          omega)
        (fun _j ↦
          annularContractedUpperRetainedHomogeneousEnlargedDigitEvent
            ε A N)
        (fun _j _hj ↦
          isGaussOneDigitEvent_gaussEnlargedDigitWindow _ _ _)

/-- Every exact oriented prefix event is contained almost everywhere in
the homogeneous selected digit mask. -/
theorem
    ae_prefixApproximationEvent_subset_selectedHomogeneousPrefixDigitEvent
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N)
    (hlog : 0 < Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    annularUpperRetainedPrefixApproximationEvent ε A
        (annularContractedUpperRetainedUpperTag p)
      ≤ᵐ[gaussMeasure]
      annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
        ε A eta rho N p hoff := by
  have hraw :=
    ae_rawHomogeneousPrefixDigitEvent_eq_selected
      (ε := ε) (A := A) p hoff
  filter_upwards [ae_nonterminating_gaussMeasure, hraw] with x hx hrawx
  intro hxPrefix
  apply hrawx.mp
  refine Set.mem_iInter.mpr ?_
  intro j
  by_cases hj :
      j ∈ annularContractedUpperRetainedPrefixIndexSet p
  · rw [if_pos hj]
    have hsplit :
        annularContractedUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth
            (annularContractedUpperRetainedUpperTag p) :=
      (Finset.mem_filter.mp hj).2
    have hjExact :=
      (mem_annularUpperRetainedPrefixApproximationEvent_iff
        (annularContractedUpperRetainedUpperTag p) x).mp
          hxPrefix j hsplit
    have hlower :
        ε ≤ annularUpperRetainedOrientedLower ε A
          (annularContractedUpperRetainedUpperTag p) j := by
      simpa only [annularUpperRetainedOrientedLower,
        annularContractedUpperRetainedUpperTag] using!
        flattenedAnnular_oriented_lower_ge_epsilon
          hεA hgrid hsigned p.1 j
    have hupper :
        annularUpperRetainedOrientedUpper ε A
            (annularContractedUpperRetainedUpperTag p) j ≤ A := by
      simpa only [annularUpperRetainedOrientedUpper,
        annularContractedUpperRetainedUpperTag] using!
        flattenedAnnular_oriented_upper_le
          hεA hgrid hsigned p.1 j
    have hxHomogeneous :
        x ∈ gaussApproximationWindow
          (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j) ε A := by
      rw [mem_gaussApproximationWindow_iff] at hjExact ⊢
      exact ⟨hjExact.1,
        hlower.trans hjExact.2.1,
        hjExact.2.2.trans hupper⟩
    have hcover :=
      union_gaussApproximationWindow_gaussDigitWindowAt_subset
        hlog hε hεA hlarge
        (Or.inl hxHomogeneous)
    rcases hcover with hex | hdigit
    · exact
        (not_mem_gaussPrefixExceptional_of_nonterminating
          hx.1 hx.2
          (annularContractedUpperRetainedTimes p j + 1) hex).elim
    · simpa only [
        annularContractedUpperRetainedHomogeneousEnlargedDigitEvent,
        Set.mem_preimage] using! hdigit
  · rw [if_neg hj]
    trivial

/-! ## Prefix-bad mass and the complete future block -/

/-- Prefix event used for relative mixing.  The shallow-minus-delayed slice
is contained in this event because it is disjoint from delayed goodness. -/
def annularContractedUpperRetainedBadSelectedPrefixDigitEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N) : Set ℝ :=
  (gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho))ᶜ ∩
    annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
      ε A eta rho N p hoff

theorem
    measurableSet_annularContractedUpperRetainedBadSelectedPrefixDigitEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N) :
    @MeasurableSet ℝ
      (gaussPrefixMeasurableSpace
        (annularContractedUpperRetainedDelayedDepth p))
      (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
        ε A eta rho N p hoff) := by
  unfold annularContractedUpperRetainedBadSelectedPrefixDigitEvent
  apply MeasurableSet.inter
  · exact
      (measurableSet_gaussDenominatorPrefixGoodEvent_prefix
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)).compl
  · exact
      measurableSet_annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
        (ε := ε) (A := A) p hoff

/-! ## The shallow-minus-delayed integral is supported on the exact prefix
windows -/

/-- The depth-slice integral has norm at most the uniform mass of the same
slice intersected with the exact prefix-window event.  This is the literal
support statement needed below; in particular no cancellation is used. -/
theorem
    norm_annularContractedUpperRetainedGoodDepthSliceIntegral_le_prefixEvent
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ‖annularContractedUpperRetainedGoodDepthSliceIntegral
        ε A eta rho N k hr mode hmode p‖ ≤
      uniform01Measure.real
        ((gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedShallowDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho) \
            gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedDelayedDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho)) ∩
          annularUpperRetainedPrefixApproximationEvent ε A
            (annularContractedUpperRetainedUpperTag p)) := by
  let S : Set ℝ :=
    gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedShallowDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) \
      gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)
  let E : Set ℝ :=
    annularUpperRetainedPrefixApproximationEvent ε A
      (annularContractedUpperRetainedUpperTag p)
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let f : ℝ → ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedShallowDepth p)
  have hSMeas : MeasurableSet S := by
    exact
      (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).diff
        (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _)
  have hEMeas : MeasurableSet E := by
    exact
      measurableSet_annularUpperRetainedPrefixApproximationEvent
        (ε := ε) (A := A)
        (annularContractedUpperRetainedUpperTag p)
  have hchar :
      (gaussPrefixMarkedMixedPrefixCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)) = f := by
    funext x
    simpa only [B, f,
      annularContractedUpperRetainedDelayedDepth,
      annularContractedUpperRetainedShallowDepth,
      annularContractedUpperRetainedUpperTag,
      annularContractedUpperRetainedRealization] using!
      annularUpperRetained_delayedPrefixCharacter_eq_shallow
        hgrid htime (annularContractedUpperRetainedToUpper p)
        (by omega) hW B x
  have hsupport :
      (∫ x in S, f x ∂uniform01Measure) =
        ∫ x in S ∩ E, f x ∂uniform01Measure := by
    rw [← integral_indicator hSMeas,
      ← integral_indicator (hSMeas.inter hEMeas)]
    apply integral_congr_ae
    filter_upwards [ae_nonterminating_uniform01] with x hx
    by_cases hxS : x ∈ S
    · by_cases hxE : x ∈ E
      · rw [Set.indicator_of_mem hxS,
          Set.indicator_of_mem
            (show x ∈ S ∩ E from ⟨hxS, hxE⟩)]
      · have hfzero : f x = 0 := by
          by_contra hfne
          apply hxE
          apply
            annularContractedUpperRetained_prefixCharacter_ne_zero_implies_prefixEvent
              (p := p) hx.1
          rw [hchar]
          exact hfne
        rw [Set.indicator_of_mem hxS,
          Set.indicator_of_notMem (by
            intro hxSE
            exact hxE hxSE.2),
          hfzero]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (by
          intro hxSE
          exact hxS hxSE.1)]
  unfold annularContractedUpperRetainedGoodDepthSliceIntegral
  change ‖∫ x in S, f x ∂uniform01Measure‖ ≤
    uniform01Measure.real (S ∩ E)
  rw [hsupport]
  have hbound :=
    norm_setIntegral_le_of_norm_le_const
      (C := (1 : ℝ))
      (measure_lt_top uniform01Measure (S ∩ E))
      (fun x _hx ↦ by
        simpa only [f, B] using!
          norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
            N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedShallowDepth p) x)
  simpa only [one_mul] using! hbound

/-- After the exact prefix windows have been replaced by the selected
finite-word mask, the depth-slice integral is bounded by the corresponding
Gauss prefix-bad mass. -/
theorem
    norm_annularContractedUpperRetainedGoodDepthSliceIntegral_le_badSelected
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N)
    (hlog : 0 < Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedGoodDepthSliceIntegral
        ε A eta rho N k hr mode hmode p‖ ≤
      (2 * Real.log 2) *
        gaussMeasure.real
          (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
            ε A eta rho N p hoff) := by
  let Gd : Set ℝ :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedShallowDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let Gb : Set ℝ :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let E : Set ℝ :=
    annularUpperRetainedPrefixApproximationEvent ε A
      (annularContractedUpperRetainedUpperTag p)
  let P : Set ℝ :=
    annularContractedUpperRetainedSelectedHomogeneousPrefixDigitEvent
      ε A eta rho N p hoff
  have hfirst :=
    norm_annularContractedUpperRetainedGoodDepthSliceIntegral_le_prefixEvent
      (ε := ε) (A := A) hgrid htime p hN hW
  have hmonoUniform :
      uniform01Measure.real ((Gd \ Gb) ∩ E) ≤
        uniform01Measure.real (Gbᶜ ∩ E) := by
    apply measureReal_mono
    · intro x hx
      exact ⟨hx.1.2, hx.2⟩
    · exact measure_ne_top uniform01Measure _
  have hbadExactMeas : MeasurableSet (Gbᶜ ∩ E) := by
    exact
      (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).compl.inter
        (measurableSet_annularUpperRetainedPrefixApproximationEvent
          (ε := ε) (A := A)
          (annularContractedUpperRetainedUpperTag p))
  have huniformGauss :
      uniform01Measure.real (Gbᶜ ∩ E) ≤
        (2 * Real.log 2) * gaussMeasure.real (Gbᶜ ∩ E) :=
    uniform01MeasureReal_le_gaussMeasureReal hbadExactMeas
  have hprefixAE : E ≤ᵐ[gaussMeasure] P := by
    simpa only [E, P] using!
      ae_prefixApproximationEvent_subset_selectedHomogeneousPrefixDigitEvent
        hε hεA hgrid hsigned p hoff hlog hlarge
  have hbadAE :
      (Gbᶜ ∩ E : Set ℝ) ≤ᵐ[gaussMeasure]
        (Gbᶜ ∩ P : Set ℝ) := by
    filter_upwards [hprefixAE] with x hx
    intro hxb
    exact ⟨hxb.1, hx hxb.2⟩
  have hmonoGauss :
      gaussMeasure.real (Gbᶜ ∩ E) ≤ gaussMeasure.real (Gbᶜ ∩ P) :=
    measureReal_mono_ae_of_finite gaussMeasure hbadAE
  calc
    ‖annularContractedUpperRetainedGoodDepthSliceIntegral
        ε A eta rho N k hr mode hmode p‖ ≤
        uniform01Measure.real ((Gd \ Gb) ∩ E) := by
      simpa only [Gd, Gb, E] using! hfirst
    _ ≤ uniform01Measure.real (Gbᶜ ∩ E) := hmonoUniform
    _ ≤ (2 * Real.log 2) * gaussMeasure.real (Gbᶜ ∩ E) :=
      huniformGauss
    _ ≤ (2 * Real.log 2) * gaussMeasure.real (Gbᶜ ∩ P) := by
      exact mul_le_mul_of_nonneg_left hmonoGauss (by positivity)
    _ = (2 * Real.log 2) *
        gaussMeasure.real
          (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
            ε A eta rho N p hoff) := by
      rfl

/-! ## Relative mixing with the complete future tuple -/

theorem
    measurableSet_annularContractedUpperRetainedFutureDigitTupleEvent_future
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    @MeasurableSet ℝ
      (gaussFutureMeasurableSpace
        (annularContractedUpperRetainedDelayedDepth p +
          annularContractedUpperRetainedMixingGap rho N))
      (annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p)) := by
  rw [annularContractedUpperRetained_delayedDepth_add_mixingGap p]
  unfold gaussFutureMeasurableSpace
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨
    shiftedGaussTailEvent
      (annularUpperRetainedFutureBase
        (annularContractedUpperRetainedUpperTag p))
      (annularUpperRetainedFutureTime
        (annularContractedUpperRetainedUpperTag p))
      (annularUpperRetainedFutureDigitEvent ε A
        (annularContractedUpperRetainedUpperTag p)),
    ?_, ?_⟩
  · exact measurableSet_shiftedGaussTailEvent fun j ↦
      measurableSet_annularUpperRetainedFutureDigitEvent
        (ε := ε) (A := A)
        (annularContractedUpperRetainedUpperTag p) j
  · exact
      annularUpperRetainedFutureDigitBlock_preimage_eq
        (ε := ε) (A := A)
        (annularContractedUpperRetainedUpperTag p)

/-- If the relative-mixing error is at most one half, the product of the
two Gauss-event masses is at most twice their joint mass. -/
theorem measureReal_mul_le_two_mul_inter_of_eventRelativeMixing_half
    (m₁ m₂ : MeasurableSpace ℝ)
    {rate : ℝ} (hrate : rate ≤ 1 / 2)
    {S U : Set ℝ}
    (hS : @MeasurableSet ℝ m₁ S)
    (hU : @MeasurableSet ℝ m₂ U)
    (hmix :
      @EventRelativeMixing ℝ m₁ m₂ (borel ℝ)
        gaussMeasure rate) :
    gaussMeasure.real S * gaussMeasure.real U ≤
      2 * gaussMeasure.real (S ∩ U) := by
  have h :=
    hmix S U hS hU
  let P : ℝ := gaussMeasure.real S * gaussMeasure.real U
  let J : ℝ := gaussMeasure.real (S ∩ U)
  have hPJ : P - J ≤ |J - P| := by
    rw [show P - J = -(J - P) by ring]
    exact neg_le_abs _
  have hrateP : rate * P ≤ (1 / 2) * P := by
    exact mul_le_mul_of_nonneg_right hrate
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
  have h' : |J - P| ≤ rate * P := by
    simpa only [J, P, mul_assoc] using! h
  change P ≤ 2 * J
  nlinarith

theorem
    badSelectedPrefixMass_mul_futureMass_le_twice_joint
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N)
    (hrate :
      48 * (527 / 540 : ℝ) ^
          annularContractedUpperRetainedMixingGap rho N ≤ 1 / 2) :
    gaussMeasure.real
          (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
            ε A eta rho N p hoff) *
        gaussMeasure.real
          (annularUpperRetainedFutureDigitTupleEvent ε A
            (annularContractedUpperRetainedUpperTag p)) ≤
      2 * gaussMeasure.real
        (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
              ε A eta rho N p hoff ∩
          annularUpperRetainedFutureDigitTupleEvent ε A
            (annularContractedUpperRetainedUpperTag p)) := by
  exact
    measureReal_mul_le_two_mul_inter_of_eventRelativeMixing_half
      (m₁ := gaussPrefixMeasurableSpace
        (annularContractedUpperRetainedDelayedDepth p))
      (m₂ := gaussFutureMeasurableSpace
        (annularContractedUpperRetainedDelayedDepth p +
          annularContractedUpperRetainedMixingGap rho N))
      hrate
      (measurableSet_annularContractedUpperRetainedBadSelectedPrefixDigitEvent
        (ε := ε) (A := A) p hoff)
      (measurableSet_annularContractedUpperRetainedFutureDigitTupleEvent_future
        (ε := ε) (A := A) p)
      (gaussPrefixFuture_eventRelativeMixing
        (annularContractedUpperRetainedDelayedDepth p)
        (annularContractedUpperRetainedMixingGap rho N))

theorem
    eventually_annularContractedUpperRetainedMixingRate_le_half
    (hrho : 0 < rho) :
    ∀ᶠ N : ℕ in atTop,
      48 * (527 / 540 : ℝ) ^
          annularContractedUpperRetainedMixingGap rho N ≤ 1 / 2 := by
  have hpow :
      Tendsto (fun m : ℕ ↦ (527 / 540 : ℝ) ^ m)
        atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgap :
      Tendsto
        (fun N : ℕ ↦
          annularContractedUpperRetainedMixingGap rho N)
        atTop atTop := by
    simpa only [annularContractedUpperRetainedMixingGap] using!
      tendsto_annularUpperRetainedDelayedMixingGap_atTop hrho
  have hrate :
      Tendsto
        (fun N : ℕ ↦
          48 * (527 / 540 : ℝ) ^
            annularContractedUpperRetainedMixingGap rho N)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul (hpow.comp hgap)
  exact (hrate.eventually_lt_const (by norm_num)).mono fun _N hN ↦ hN.le

/-! ## The mixed joint event lies in one global bad homogeneous tuple -/

theorem
    gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent_gauss
    {C L m : ℕ} {Delta : ℝ} (hm : m ≤ C * L) :
    gaussDenominatorLinearGoodEvent C L Delta
      ≤ᵐ[gaussMeasure]
    gaussDenominatorPrefixGoodEvent m L Delta := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro hxGood
  apply (mem_gaussDenominatorPrefixGoodEvent_iff hx.1 hx.2).2
  intro n hn
  exact hxGood n (hn.trans hm)

/-- The homogeneous full digit tuple used to delete the global bad event. -/
def annularContractedUpperRetainedHomogeneousDigitTupleEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  gaussHeterogeneousDigitWindowTupleEvent
    (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A)
    (annularContractedUpperRetainedTimes p)

theorem
    measurableSet_annularContractedUpperRetainedHomogeneousDigitTupleEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    MeasurableSet
      (annularContractedUpperRetainedHomogeneousDigitTupleEvent
        ε A eta rho N p) := by
  exact
    measurableSet_gaussHeterogeneousDigitWindowTupleEvent
      (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A)
      (annularContractedUpperRetainedTimes p)

/-- After adjoining the complete future tuple, prefix badness becomes
global badness and every chronological coordinate lies in the same
homogeneous digit window. -/
theorem
    ae_badSelectedPrefix_inter_future_subset_globalBad_inter_homogeneousDigit
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (henlarge : A + 8 * A ^ 2 / Real.log (N : ℝ) ≤ 2 * A) :
    (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
          ε A eta rho N p hoff ∩
        annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedUpperTag p) : Set ℝ)
      ≤ᵐ[gaussMeasure]
    (gaussDenominatorLinearBadEvent 1
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) ∩
        annularContractedUpperRetainedHomogeneousDigitTupleEvent
          ε A eta rho N p : Set ℝ) := by
  have hglobalPrefix :
      gaussDenominatorLinearGoodEvent 1
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)
        ≤ᵐ[gaussMeasure]
      gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) := by
    apply
      gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent_gauss
    simpa only [one_mul] using!
      (annularContractedUpperRetainedDelayedDepth_lt_ambient
        hgrid htime p (by omega) hW).le
  have hraw :=
    ae_rawHomogeneousPrefixDigitEvent_eq_selected
      (ε := ε) (A := A) p hoff
  filter_upwards
      [ae_nonterminating_gaussMeasure, gaussMeasure_unit_ae,
        hglobalPrefix, hraw] with x hx hunit hgood hrawx
  intro hxJoint
  have hxBadPrefix :
      x ∉ gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho) :=
    hxJoint.1.1
  have hxGlobalBad :
      x ∈ gaussDenominatorLinearBadEvent 1
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho) := by
    rw [gaussDenominatorLinearBadEvent_eq_compl]
    intro hxGlobalGood
    exact hxBadPrefix (hgood hxGlobalGood)
  have hxRaw :
      x ∈
        ⋂ j,
          if j ∈ annularContractedUpperRetainedPrefixIndexSet p then
            (gaussOrbit (annularContractedUpperRetainedTimes p j)) ⁻¹'
              annularContractedUpperRetainedHomogeneousEnlargedDigitEvent
                ε A N
          else Set.univ := by
    exact hrawx.mpr hxJoint.1.2
  have hxFuture :
      ∀ j : Fin (MixedOccurrenceCount k),
        annularUpperRetainedSplitDepth
              (annularContractedUpperRetainedUpperTag p) <
            annularUpperRetainedTimes
              (annularContractedUpperRetainedUpperTag p) j →
          gaussOrbit
              (annularUpperRetainedTimes
                (annularContractedUpperRetainedUpperTag p) j) x ∈
            scaledGaussFirstDigitWindow
              (Real.log (N : ℝ))
              (annularUpperRetainedOrientedLower ε A
                (annularContractedUpperRetainedUpperTag p) j)
              (annularUpperRetainedOrientedUpper ε A
                (annularContractedUpperRetainedUpperTag p) j) :=
    (mem_annularUpperRetainedFutureDigitTupleEvent_iff
      hgrid htime
      (annularContractedUpperRetainedUpperTag p)
      (by omega) hW x).mp hxJoint.2
  refine ⟨hxGlobalBad, ?_⟩
  unfold
    annularContractedUpperRetainedHomogeneousDigitTupleEvent
    gaussHeterogeneousDigitWindowTupleEvent
  rw [mem_orderedEventIntersection_ofFn_iff]
  intro j
  simp only [gaussDigitWindowAt, Set.mem_inter_iff, Set.mem_preimage]
  refine ⟨hunit, ?_⟩
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularUpperRetainedSplitDepth
          (annularContractedUpperRetainedUpperTag p)
  · have hjIndex :
        j ∈ annularContractedUpperRetainedPrefixIndexSet p := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hjRaw := Set.mem_iInter.mp hxRaw j
    rw [if_pos hjIndex] at hjRaw
    change
      gaussOrbit (annularContractedUpperRetainedTimes p j) x ∈
        scaledGaussFirstDigitWindow
          (Real.log (N : ℝ)) ε (2 * A)
    change
      gaussOrbit (annularContractedUpperRetainedTimes p j) x ∈
        gaussEnlargedDigitWindow (Real.log (N : ℝ)) ε A at hjRaw
    exact ⟨hjRaw.1, hjRaw.2.1, hjRaw.2.2.trans henlarge⟩
  · have hjFuture :
      annularUpperRetainedSplitDepth
            (annularContractedUpperRetainedUpperTag p) <
          annularUpperRetainedTimes
            (annularContractedUpperRetainedUpperTag p) j := by
      simpa only [annularContractedUpperRetainedTimes_embedding] using!
        Nat.lt_of_not_ge hj
    have hjMem := hxFuture j hjFuture
    have hlower :
        ε ≤ annularUpperRetainedOrientedLower ε A
          (annularContractedUpperRetainedUpperTag p) j := by
      simpa only [annularUpperRetainedOrientedLower,
        annularContractedUpperRetainedUpperTag] using!
        flattenedAnnular_oriented_lower_ge_epsilon
          hεA hgrid hsigned p.1 j
    have hupper :
        annularUpperRetainedOrientedUpper ε A
            (annularContractedUpperRetainedUpperTag p) j ≤ A := by
      simpa only [annularUpperRetainedOrientedUpper,
        annularContractedUpperRetainedUpperTag] using!
        flattenedAnnular_oriented_upper_le
          hεA hgrid hsigned p.1 j
    change
      gaussOrbit (annularContractedUpperRetainedTimes p j) x ∈
        scaledGaussFirstDigitWindow
          (Real.log (N : ℝ)) ε (2 * A)
    simpa only [annularContractedUpperRetainedTimes_embedding] using!
      ⟨hjMem.1, hlower.trans hjMem.2.1,
        hjMem.2.2.trans (hupper.trans (by linarith [hε, hεA]))⟩

/-! ## Absolute deletion of the homogeneous tuple family -/

/-- Exact homogeneous approximation tuple paired with the digit tuple
above. -/
def annularContractedUpperRetainedHomogeneousApproximationTupleEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  gaussHeterogeneousApproximationTupleEvent
    (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A)
    (annularContractedUpperRetainedTimes p)

theorem
    measurableSet_annularContractedUpperRetainedHomogeneousApproximationTupleEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    MeasurableSet
      (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
        ε A eta rho N p) := by
  exact
    measurableSet_gaussHeterogeneousApproximationTupleEvent
      (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A)
      (annularContractedUpperRetainedTimes p)

/-- Complete-canonical-family majorant for the homogeneous replacement
errors. -/
def annularCanonicalGaussHomogeneousReplacementError
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ∑ t ∈ canonicalAnnularGridTupleFamily N k e,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A) t ∆
          gaussHeterogeneousDigitWindowTupleEvent
              (Real.log (N : ℝ)) (fun _j ↦ ε) (fun _j ↦ 2 * A) t)

theorem tendsto_annularCanonicalGaussHomogeneousReplacementError_zero
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        annularCanonicalGaussHomogeneousReplacementError ε A N k)
      atTop (nhds 0) := by
  let lower :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun _e _j ↦ ε
  let upper :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun _e _j ↦ 2 * A
  have htotal :
      Tendsto
        (fun N : ℕ ↦
          (aggregateTupleFamilyCard
              (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
        atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [aggregateTupleFamilyCard,
      totalCanonicalAnnularGridTupleCard] using!
      tendsto_totalCanonicalAnnularGridTupleCard_density
        hgrid k hr htime
  have hreplacement :=
    tendsto_aggregateGaussHeterogeneousApproximationDigitSymmDiff_zero
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := 2 * A) (density := annularOccurrenceTimeDensity k)
      hr (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop lower upper
      (by linarith [hε, hεA])
      (fun _e _j ↦ hε)
      (fun _e _j ↦ by linarith [hεA])
      (fun _e _j ↦ le_rfl)
      (fun N e ↦ canonicalAnnularGridTupleFamily N k e)
      (fun N e t ht ↦
        canonicalAnnularGridTupleFamily_chronological N k e t ht)
      htotal
  simpa only [
    annularCanonicalGaussHomogeneousReplacementError,
    lower, upper] using! hreplacement

/-- Reindex the tagged homogeneous replacement sum as a nested sum over
orders and contracted time tuples. -/
theorem
    sum_annularContractedUpperRetained_taggedHomogeneousReplacement_eq_nested
    (eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      gaussMeasure.real
        (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
              ε A eta rho N p ∆
          annularContractedUpperRetainedHomogeneousDigitTupleEvent
              ε A eta rho N p)) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ t ∈
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
          gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
                  (Real.log (N : ℝ))
                  (fun _j ↦ ε) (fun _j ↦ 2 * A) t ∆
              gaussHeterogeneousDigitWindowTupleEvent
                  (Real.log (N : ℝ))
                  (fun _j ↦ ε) (fun _j ↦ 2 * A) t) := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    gaussMeasure.real
      (gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ))
            (fun _j ↦ ε) (fun _j ↦ 2 * A) p.1 ∆
        gaussHeterogeneousDigitWindowTupleEvent
            (Real.log (N : ℝ))
            (fun _j ↦ ε) (fun _j ↦ 2 * A) p.1)
  change
    (∑ p : Σ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)),
      f p.1 p.2) = _
  rw [Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro e _he
  rw [← Finset.attach_eq_univ
    (s := contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))]
  simp only [f]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (fun _j ↦ ε) (fun _j ↦ 2 * A) t ∆
          gaussHeterogeneousDigitWindowTupleEvent
              (Real.log (N : ℝ))
              (fun _j ↦ ε) (fun _j ↦ 2 * A) t))

theorem
    tendsto_sum_annularContractedUpperRetained_taggedHomogeneousReplacement_zero
    (hε : 0 < ε) (hεA : ε < A)
    (eta rho : ℝ)
    (hgrid : 0 < grid)
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
          gaussMeasure.real
            (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
                  ε A eta rho N p ∆
              annularContractedUpperRetainedHomogeneousDigitTupleEvent
                  ε A eta rho N p))
      atTop (nhds 0) := by
  have hcanonical :=
    tendsto_annularCanonicalGaussHomogeneousReplacementError_zero
      hε hεA hgrid k hr htime
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ measureReal_nonneg
  · exact Eventually.of_forall fun N ↦ by
      calc
        (∑ p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            gaussMeasure.real
              (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
                    ε A eta rho N p ∆
                annularContractedUpperRetainedHomogeneousDigitTupleEvent
                    ε A eta rho N p)) =
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ∑ t ∈
                contractedAnnularCanonicalLaterUpperMidpointTupleFamily
                  eta rho N k hr e (mode e) (hmode e),
                gaussMeasure.real
                  (gaussHeterogeneousApproximationTupleEvent
                        (Real.log (N : ℝ))
                        (fun _j ↦ ε) (fun _j ↦ 2 * A) t ∆
                    gaussHeterogeneousDigitWindowTupleEvent
                        (Real.log (N : ℝ))
                        (fun _j ↦ ε) (fun _j ↦ 2 * A) t) :=
          sum_annularContractedUpperRetained_taggedHomogeneousReplacement_eq_nested
            (ε := ε) (A := A) eta rho N k hr mode hmode
        _ ≤ annularCanonicalGaussHomogeneousReplacementError ε A N k := by
          unfold annularCanonicalGaussHomogeneousReplacementError
          apply Finset.sum_le_sum
          intro e _he
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
              k hr e (mode e) (hmode e))
            (fun _t _ht _hnot ↦ measureReal_nonneg)
  · exact hcanonical

/-- Gauss mass of the homogeneous exact tuple restricted to the one global
denominator-bad event, summed over the contracted tagged family. -/
def annularContractedUpperRetainedHomogeneousExactGlobalBadMass
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    gaussMeasure.real
      (gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho) ∩
        annularContractedUpperRetainedHomogeneousApproximationTupleEvent
          ε A eta rho N p)

/-- Finite-scale comparison with the audited uniform approximation-window
bad moment. -/
theorem
    annularContractedUpperRetainedHomogeneousExactGlobalBadMass_le_moment
    (hgrid : 0 < grid)
    (hN : 2 ≤ N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedUpperRetainedHomogeneousExactGlobalBadMass
        ε A eta rho N k hr mode hmode ≤
      (1 / Real.log 2) *
        ∫ x in gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho),
          (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N)
              ε (2 * A) x : ℝ) ^ MixedOccurrenceCount k
          ∂uniform01Measure := by
  let T :=
    AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode
  let bad : Set ℝ :=
    gaussDenominatorLinearBadEvent 1
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let E : T → Set ℝ := fun p ↦
    annularContractedUpperRetainedHomogeneousApproximationTupleEvent
      ε A eta rho N p
  let C : ℝ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
  let countPow : ℝ → ℝ := fun x ↦
    (gaussApproximationWindowCount
      (Real.log (N : ℝ)) (annularDepthAmbientSize N)
      ε (2 * A) x : ℝ) ^ MixedOccurrenceCount k
  have hE : ∀ p ∈ (Finset.univ : Finset T), MeasurableSet (E p) := by
    intro p _hp
    exact
      measurableSet_annularContractedUpperRetainedHomogeneousApproximationTupleEvent
        (ε := ε) (A := A) p
  have hpoint : ∀ x,
      (∑ p ∈ (Finset.univ : Finset T),
        (E p).indicator (fun _ ↦ (1 : ℝ)) x) ≤ C * countPow x := by
    intro x
    dsimp only [E, C, countPow,
      annularContractedUpperRetainedHomogeneousApproximationTupleEvent,
      gaussHeterogeneousApproximationTupleEvent]
    rw [
      sum_annularContractedUpperRetained_taggedWindowIndicators_eq_nested
        k hr mode hmode x]
    exact
      sum_annularContractedUpperRetained_windowIndicators_le
        (ε := ε) (A := 2 * A) (eta := eta) (rho := rho) (N := N)
        hgrid k hr htime mode hmode (by omega) x
  have hcountInt : Integrable countPow uniform01Measure := by
    exact
      integrable_gaussApproximationWindowCount_pow
        (Real.log (N : ℝ)) (annularDepthAmbientSize N)
        (MixedOccurrenceCount k) ε (2 * A)
  have huniform :
      (∑ p : T, uniform01Measure.real (E p ∩ bad)) ≤
        ∫ x in bad, C * countPow x ∂uniform01Measure := by
    simpa only [Finset.mem_univ, sum_const_zero, true_and] using!
      sum_measureReal_inter_le_setIntegral
        uniform01Measure (Finset.univ : Finset T) E bad
        (fun x ↦ C * countPow x) hE
        (hcountInt.const_mul C) hpoint
  calc
    annularContractedUpperRetainedHomogeneousExactGlobalBadMass
        ε A eta rho N k hr mode hmode =
        ∑ p : T, gaussMeasure.real (bad ∩ E p) := by rfl
    _ ≤ ∑ p : T,
        (1 / Real.log 2) * uniform01Measure.real (E p ∩ bad) := by
      apply Finset.sum_le_sum
      intro p _hp
      calc
        gaussMeasure.real (bad ∩ E p) =
            gaussMeasure.real (E p ∩ bad) := by
          rw [Set.inter_comm]
        _ ≤ (1 / Real.log 2) *
            uniform01Measure.real (E p ∩ bad) :=
          gaussMeasureReal_le_inv_log_two_mul_uniform01MeasureReal
            ((hE p (by simp)).inter
              (measurableSet_gaussDenominatorLinearBadEvent
                1 (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho)))
    _ = (1 / Real.log 2) *
        ∑ p : T, uniform01Measure.real (E p ∩ bad) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / Real.log 2) *
        ∫ x in bad, C * countPow x ∂uniform01Measure := by
      exact mul_le_mul_of_nonneg_left huniform (by positivity)
    _ = (1 / Real.log 2) *
        ∫ x in gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho),
          (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N)
              ε (2 * A) x : ℝ) ^ MixedOccurrenceCount k
          ∂uniform01Measure := by
      rfl

theorem
    tendsto_annularContractedUpperRetainedHomogeneousExactGlobalBadMass_zero
    (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedHomogeneousExactGlobalBadMass
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let C : ℝ :=
    (1 / Real.log 2) *
      Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)
  let moment : ℕ → ℝ := fun N ↦
    ∫ x in gaussDenominatorLinearBadEvent 1
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho),
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N)
        ε (2 * A) x : ℝ) ^ MixedOccurrenceCount k
      ∂uniform01Measure
  have hmoment : Tendsto moment atTop (nhds 0) := by
    simpa only [moment] using!
      tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
        annularDepthAmbientSize annularDepthAmbientSize
        (MixedOccurrenceCount k) 1
        hr hε (by linarith [hεA])
        exists_eventually_annularDepthAmbientSize_le_mul_log
        (by norm_num)
        (upperGoodTransferDenominatorTolerance_pos heta hrho)
        tendsto_annularDepthAmbientSize_atTop
  have hmajor :
      Tendsto (fun N : ℕ ↦ C * moment N) atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hmoment
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have h :=
      annularContractedUpperRetainedHomogeneousExactGlobalBadMass_le_moment
        (ε := ε) (A := A) (eta := eta) (rho := rho)
        hgrid hN k hr htime mode hmode
    simpa only [C, moment, integral_const_mul, mul_assoc] using! h
  · simpa only [C, moment, mul_assoc] using! hmajor

/-- Gauss mass of the homogeneous digit tuple on the global denominator
bad event. -/
def annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    gaussMeasure.real
      (gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho) ∩
        annularContractedUpperRetainedHomogeneousDigitTupleEvent
          ε A eta rho N p)

theorem
    annularContractedUpperRetainedHomogeneousDigitGlobalBadMass_le
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
        ε A eta rho N k hr mode hmode ≤
      annularContractedUpperRetainedHomogeneousExactGlobalBadMass
          ε A eta rho N k hr mode hmode +
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          gaussMeasure.real
            (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
                  ε A eta rho N p ∆
              annularContractedUpperRetainedHomogeneousDigitTupleEvent
                  ε A eta rho N p) := by
  let bad : Set ℝ :=
    gaussDenominatorLinearBadEvent 1
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let E := fun p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode ↦
    annularContractedUpperRetainedHomogeneousApproximationTupleEvent
      ε A eta rho N p
  let D := fun p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode ↦
    annularContractedUpperRetainedHomogeneousDigitTupleEvent
      ε A eta rho N p
  unfold
    annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
    annularContractedUpperRetainedHomogeneousExactGlobalBadMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _hp
  have hsubset :
      bad ∩ D p ⊆ (bad ∩ E p) ∪ (E p ∆ D p) := by
    intro x hx
    by_cases hxE : x ∈ E p
    · exact Or.inl ⟨hx.1, hxE⟩
    · exact Or.inr (Or.inr ⟨hx.2, hxE⟩)
  calc
    gaussMeasure.real (bad ∩ D p) ≤
        gaussMeasure.real ((bad ∩ E p) ∪ (E p ∆ D p)) :=
      measureReal_mono hsubset
    _ ≤ gaussMeasure.real (bad ∩ E p) +
        gaussMeasure.real (E p ∆ D p) :=
      measureReal_union_le _ _
    _ = gaussMeasure.real
          (gaussDenominatorLinearBadEvent 1
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedHomogeneousApproximationTupleEvent
              ε A eta rho N p) +
        gaussMeasure.real
          (annularContractedUpperRetainedHomogeneousApproximationTupleEvent
                ε A eta rho N p ∆
            annularContractedUpperRetainedHomogeneousDigitTupleEvent
              ε A eta rho N p) := by
      rfl

theorem
    tendsto_annularContractedUpperRetainedHomogeneousDigitGlobalBadMass_zero
    (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hexact :=
    tendsto_annularContractedUpperRetainedHomogeneousExactGlobalBadMass_zero
      hε hεA heta hrho hgrid k hr htime mode hmode
  have hreplacement :=
    tendsto_sum_annularContractedUpperRetained_taggedHomogeneousReplacement_zero
      hε hεA eta rho hgrid k hr htime mode hmode
  have hsum := hexact.add hreplacement
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ measureReal_nonneg
  · exact Eventually.of_forall fun N ↦
      annularContractedUpperRetainedHomogeneousDigitGlobalBadMass_le
        ε A eta rho N k hr mode hmode
  · simpa only [zero_add] using! hsum

/-! ## Final retained-future depth-slice estimate -/

theorem
    norm_GoodDepthSliceIntegral_mul_futureMean_le_globalBadDigitMass
    (hε : 0 < ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hoff : 0 < annularUpperRetainedFreezingOffset rho N)
    (hlog : 0 < Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ))
    (henlarge : A + 8 * A ^ 2 / Real.log (N : ℝ) ≤ 2 * A)
    (hrate :
      48 * (527 / 540 : ℝ) ^
          annularContractedUpperRetainedMixingGap rho N ≤ 1 / 2) :
    ‖annularContractedUpperRetainedGoodDepthSliceIntegral
          ε A eta rho N k hr mode hmode p *
        annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
      (4 * Real.log 2) *
        gaussMeasure.real
          (gaussDenominatorLinearBadEvent 1
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedHomogeneousDigitTupleEvent
              ε A eta rho N p) := by
  let P : ℝ :=
    gaussMeasure.real
      (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
        ε A eta rho N p hoff)
  let U : ℝ :=
    gaussMeasure.real
      (annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p))
  let J : ℝ :=
    gaussMeasure.real
      (annularContractedUpperRetainedBadSelectedPrefixDigitEvent
            ε A eta rho N p hoff ∩
        annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedUpperTag p))
  let D : ℝ :=
    gaussMeasure.real
      (gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho) ∩
        annularContractedUpperRetainedHomogeneousDigitTupleEvent
          ε A eta rho N p)
  have hslice :
      ‖annularContractedUpperRetainedGoodDepthSliceIntegral
          ε A eta rho N k hr mode hmode p‖ ≤
        (2 * Real.log 2) * P := by
    simpa only [P] using!
      norm_annularContractedUpperRetainedGoodDepthSliceIntegral_le_badSelected
        hε hεA hgrid htime hsigned p hN hW hoff hlog hlarge
  have hfuture :
      ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ = U := by
    simpa only [U] using!
      norm_annularContractedUpperRetainedFutureMean_eq_measureReal
        ε A eta rho N k hr mode hmode p
  have hmix : P * U ≤ 2 * J := by
    simpa only [P, U, J] using!
      badSelectedPrefixMass_mul_futureMass_le_twice_joint
        (ε := ε) (A := A) p hoff hrate
  have hjoint : J ≤ D := by
    apply measureReal_mono_ae_of_finite gaussMeasure
    simpa only [J, D] using!
      ae_badSelectedPrefix_inter_future_subset_globalBad_inter_homogeneousDigit
        hε hεA hgrid htime hsigned p hoff hN hW henlarge
  rw [norm_mul, hfuture]
  calc
    ‖annularContractedUpperRetainedGoodDepthSliceIntegral
          ε A eta rho N k hr mode hmode p‖ * U ≤
        ((2 * Real.log 2) * P) * U :=
      mul_le_mul_of_nonneg_right hslice measureReal_nonneg
    _ = (2 * Real.log 2) * (P * U) := by ring
    _ ≤ (2 * Real.log 2) * (2 * J) := by
      exact mul_le_mul_of_nonneg_left hmix (by positivity)
    _ ≤ (2 * Real.log 2) * (2 * D) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjoint (by norm_num)) (by positivity)
    _ = (4 * Real.log 2) * D := by ring

/-- The complete future factor makes the shallow-minus-delayed
denominator-good slice absolutely summable and vanishing. -/
theorem
    tendsto_sum_norm_annularContractedUpperRetainedGoodDepthSliceIntegral_mul_futureMean_zero
    (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    (hgrid : 0 < grid)
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
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedGoodDepthSliceIntegral
                ε A eta rho N k hr mode hmode p *
              annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖)
      atTop (nhds 0) := by
  have hbad :=
    tendsto_annularContractedUpperRetainedHomogeneousDigitGlobalBadMass_zero
      hε hεA heta hrho hgrid k hr htime mode hmode
  have hmajor :
      Tendsto
        (fun N : ℕ ↦
          (4 * Real.log 2) *
            annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
              ε A eta rho N k hr mode hmode)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hbad
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N :=
    eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hoff :
      ∀ᶠ N : ℕ in atTop,
        0 < annularUpperRetainedFreezingOffset rho N :=
    (tendsto_annularUpperRetainedFreezingOffset_atTop hrho).eventually_gt_atTop 0
  have hrate :=
    eventually_annularContractedUpperRetainedMixingRate_le_half
      (rho := rho) hrho
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        16 * A ^ 2 ≤ ε * Real.log (N : ℝ) := by
    have hlogLarge :=
      tendsto_log_natCast_atTop.eventually_gt_atTop
        (16 * A ^ 2 / ε)
    filter_upwards [hlogLarge] with N hN
    have hmul := (div_lt_iff₀ hε).mp hN
    nlinarith
  have henlarge :
      ∀ᶠ N : ℕ in atTop,
        A + 8 * A ^ 2 / Real.log (N : ℝ) ≤ 2 * A := by
    have hA : 0 < A := hε.trans hεA
    have hlogLarge :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (8 * A)
    have hlogPos :=
      tendsto_log_natCast_atTop.eventually_gt_atTop 0
    filter_upwards [hlogLarge, hlogPos] with N hlargeN hlogN
    have hdiv : 8 * A ^ 2 / Real.log (N : ℝ) ≤ A := by
      apply (div_le_iff₀ hlogN).2
      nlinarith
    linarith
  refine squeeze_zero'
    (Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _)
    ?_ hmajor
  filter_upwards
      [hN, hW, hoff, hrate, hlarge, henlarge] with
      N hNN hWN hoffN hrateN hlargeN henlargeN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hNN)
  unfold annularContractedUpperRetainedHomogeneousDigitGlobalBadMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _hp
  exact
    norm_GoodDepthSliceIntegral_mul_futureMean_le_globalBadDigitMass
      hε hεA hgrid htime hsigned p hNN hWN hoffN hlogN
      hlargeN henlargeN hrateN

end

end Erdos1002
