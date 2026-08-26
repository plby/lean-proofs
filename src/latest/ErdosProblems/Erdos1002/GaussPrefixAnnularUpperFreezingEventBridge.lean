import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Full-event bridge for upper character freezing

The enlarged delayed-prefix event and the complete future digit block are
associated here with one full chronological masked tuple.  Boundary strips
are kept full-dimensional: their distinguished coordinate has width twice
the freezing radius, while every other delayed-prefix coordinate remains in
its enlarged rare window and every future rare digit remains attached.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 2000000

local instance gaussPrefixAnnularUpperFreezingEventBridgePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

theorem ae_annularContractedUpperRetainedCompletePhaseEvent_subset_masked
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ∀ᵐ x ∂gaussMeasure,
      x ∈ annularContractedUpperRetainedCompletePhaseEvent
          ε A eta rho N p →
        x ∈ annularContractedUpperRetainedPhaseMaskedEvent
          ε A eta rho N p := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro hxComplete
  unfold annularContractedUpperRetainedPhaseMaskedEvent
  rw [mem_maskedOrderedEventIntersection_iff]
  intro j
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · let z : GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p) :=
      ⟨p.1 j, by
        have hjtime :=
          congrFun (annularContractedUpperRetainedRealization_times p) j
        change
          ((annularContractedUpperRetainedRealization p).1
              (p.1 j).1 (p.1 j).2 : ℕ) =
            annularContractedUpperRetainedTimes p j at hjtime
        rw [hjtime]
        exact hj⟩
    let i :=
      (annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm z
    have hi :=
      Set.mem_iInter.mp hxComplete.2.1 i
    have hactive : 0 < k (p.1 j).1 := by
      have hjlt := (p.1 j).2.isLt
      omega
    have hsigned :
        x ∈ gaussSignedApproximationWindow
          (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j)
          (annularContractedUpperRetainedPhaseSignedLower
            ε A eta rho N p j)
          (annularContractedUpperRetainedPhaseSignedUpper
            ε A eta rho N p j) := by
      refine ⟨⟨hx.1.1, hx.1.2.le⟩, ?_⟩
      have heq :
          (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 =
            p.1 j := by
        change
          (annularContractedUpperRetainedPrefixOccurrenceEquiv p
              ((annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm
                z)).1 =
            p.1 j
        rw [Equiv.apply_symm_apply]
      have htime :
          ((annularContractedUpperRetainedRealization p).1
              (p.1 j).1 (p.1 j).2 : ℕ) =
            annularContractedUpperRetainedTimes p j := by
        have hjtime :=
          congrFun (annularContractedUpperRetainedRealization_times p) j
        simpa only [fixedOrderMixedTimes] using! hjtime
      have htimeI :
          ((annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.2 :
                ℕ) =
            annularContractedUpperRetainedTimes p j := by
        rw [heq]
        exact htime
      change
        annularContractedUpperRetainedPrefixCoordinate p x i ∈
          Icc
            (annularContractedUpperRetainedPrefixLower ε A p i -
              annularContractedUpperRetainedPrefixValueRadius eta rho N p)
            (annularContractedUpperRetainedPrefixUpper ε A p i +
              annularContractedUpperRetainedPrefixValueRadius eta rho N p)
        at hi
      change
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ))
            (annularContractedUpperRetainedTimes p j) x ∈
          Icc
            (annularContractedUpperRetainedPhaseSignedLower
              ε A eta rho N p j)
            (annularContractedUpperRetainedPhaseSignedUpper
              ε A eta rho N p j)
      simpa only [
        annularContractedUpperRetainedPrefixCoordinate,
        annularContractedUpperRetainedPrefixLower,
        annularContractedUpperRetainedPrefixUpper,
        heq,
        activeAnnularOccurrenceSignedLower_of_pos hactive,
        activeAnnularOccurrenceSignedUpper_of_pos hactive,
        annularOccurrenceSignedLower_flattened,
        annularOccurrenceSignedUpper_flattened,
        gaussPrefixMarkedPoint_value_eq_signedScaledApproximation,
        htimeI,
        annularContractedUpperRetainedPhaseSignedLower,
        annularContractedUpperRetainedPhaseSignedUpper,
        if_pos hj] using! hi
    rw [gaussSignedApproximationWindow_eq_oriented] at hsigned
    simpa only [
      maskedCoordinateEvent,
      annularContractedUpperRetainedDelayedFutureMask,
      Nat.not_lt.mpr hj,
      Bool.false_eq_true,
      ↓reduceIte,
      annularContractedUpperRetainedPhaseMaskedEvent] using! hsigned
  · have hjFuture :
        annularContractedUpperRetainedDelayedDepth p <
          annularContractedUpperRetainedTimes p j :=
      Nat.lt_of_not_ge hj
    let q := annularContractedUpperRetainedUpperTag p
    have hjSplit :
        annularUpperRetainedSplitDepth q <
          annularUpperRetainedTimes q j := by
      exact
        (annularUpperRetained_after_delayed_iff_after_split
          hgrid htime q hN hW j).mp (by
            simpa only [q,
              annularContractedUpperRetainedUpperTag,
              annularContractedUpperRetainedDelayedDepth,
              annularContractedUpperRetainedTimes_embedding] using!
              hjFuture)
    have hjDigit :=
      (mem_annularUpperRetainedFutureDigitTupleEvent_iff
        hgrid htime q hN hW x).mp hxComplete.2.2 j hjSplit
    have hlower :=
      annularUpperRetained_actual_orientedLower_eq
        (ε := ε) (A := A) q j
    have hupper :=
      annularUpperRetained_actual_orientedUpper_eq
        (ε := ε) (A := A) q j
    have hlower' :
        gaussParityOrientedLower
            (annularContractedUpperRetainedTimes p j)
            (flattenedAnnularSignedLower ε A p.1 j)
            (flattenedAnnularSignedUpper ε A p.1 j) =
          annularUpperRetainedOrientedLower ε A q j := by
      simpa only [q,
        annularContractedUpperRetainedTimes_embedding] using! hlower
    have hupper' :
        gaussParityOrientedUpper
            (annularContractedUpperRetainedTimes p j)
            (flattenedAnnularSignedLower ε A p.1 j)
            (flattenedAnnularSignedUpper ε A p.1 j) =
          annularUpperRetainedOrientedUpper ε A q j := by
      simpa only [q,
        annularContractedUpperRetainedTimes_embedding] using! hupper
    have hxIoc : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1.1, hx.1.2.le⟩
    simp only [
      maskedCoordinateEvent,
      annularContractedUpperRetainedDelayedFutureMask,
      hjFuture,
      ↓reduceIte,
      gaussDigitWindowAt,
      Set.mem_inter_iff,
      Set.mem_preimage,
      annularContractedUpperRetainedPhaseSignedLower,
      annularContractedUpperRetainedPhaseSignedUpper,
      if_neg hj,
      annularContractedUpperRetainedPhaseOrientedLower,
      annularContractedUpperRetainedPhaseOrientedUpper]
    refine ⟨hxIoc, ?_⟩
    simpa only [q,
      annularContractedUpperRetainedTimes_embedding,
      hlower', hupper'] using! hjDigit

/-! ## Full-dimensional endpoint-strip events -/

/-- One of the two endpoint-strip prefix events.  `upperEndpoint = false`
selects the strip about the signed lower endpoint, while `true` selects the
strip about the signed upper endpoint. -/
def annularContractedUpperRetainedPrefixEndpointEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  closedEndpointStripWindowTupleEvent
    (annularContractedUpperRetainedPrefixLower ε A p)
    (annularContractedUpperRetainedPrefixUpper ε A p)
    (annularContractedUpperRetainedPrefixCoordinate p)
    (annularContractedUpperRetainedPrefixValueRadius eta rho N p)
    i₀
    (if upperEndpoint then
      annularContractedUpperRetainedPrefixUpper ε A p i₀
    else
      annularContractedUpperRetainedPrefixLower ε A p i₀)

/-- The complete endpoint-strip event, with both the denominator-good
restriction and the full future digit tuple retained. -/
def annularContractedUpperRetainedCompleteEndpointEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho) ∩
    (annularContractedUpperRetainedPrefixEndpointEvent
        ε A eta rho N p i₀ upperEndpoint ∩
      annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p))

/-- Signed center of the distinguished chronological endpoint strip. -/
def annularContractedUpperRetainedBoundarySignedCenter
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : ℝ :=
  if upperEndpoint then
    flattenedAnnularSignedUpper ε A p.1
      (annularContractedUpperRetainedPrefixChronologicalIndex p i₀)
  else
    flattenedAnnularSignedLower ε A p.1
      (annularContractedUpperRetainedPrefixChronologicalIndex p i₀)

/-- Signed lower endpoints of one full chronological endpoint-strip tuple. -/
def annularContractedUpperRetainedBoundarySignedLower
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  if annularContractedUpperRetainedTimes p j ≤
      annularContractedUpperRetainedDelayedDepth p then
    if j =
        annularContractedUpperRetainedPrefixChronologicalIndex p i₀ then
      annularContractedUpperRetainedBoundarySignedCenter
          ε A p i₀ upperEndpoint -
        annularContractedUpperRetainedPrefixValueRadius eta rho N p
    else
      flattenedAnnularSignedLower ε A p.1 j -
        annularContractedUpperRetainedPrefixValueRadius eta rho N p
  else
    flattenedAnnularSignedLower ε A p.1 j

/-- Signed upper endpoints of one full chronological endpoint-strip tuple. -/
def annularContractedUpperRetainedBoundarySignedUpper
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  if annularContractedUpperRetainedTimes p j ≤
      annularContractedUpperRetainedDelayedDepth p then
    if j =
        annularContractedUpperRetainedPrefixChronologicalIndex p i₀ then
      annularContractedUpperRetainedBoundarySignedCenter
          ε A p i₀ upperEndpoint +
        annularContractedUpperRetainedPrefixValueRadius eta rho N p
    else
      flattenedAnnularSignedUpper ε A p.1 j +
        annularContractedUpperRetainedPrefixValueRadius eta rho N p
  else
    flattenedAnnularSignedUpper ε A p.1 j

def annularContractedUpperRetainedBoundaryOrientedLower
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussParityOrientedLower
    (annularContractedUpperRetainedTimes p j)
    (annularContractedUpperRetainedBoundarySignedLower
      ε A eta rho N p i₀ upperEndpoint j)
    (annularContractedUpperRetainedBoundarySignedUpper
      ε A eta rho N p i₀ upperEndpoint j)

def annularContractedUpperRetainedBoundaryOrientedUpper
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussParityOrientedUpper
    (annularContractedUpperRetainedTimes p j)
    (annularContractedUpperRetainedBoundarySignedLower
      ε A eta rho N p i₀ upperEndpoint j)
    (annularContractedUpperRetainedBoundarySignedUpper
      ε A eta rho N p i₀ upperEndpoint j)

/-- Positive center obtained by applying the actual depth parity to the
selected signed endpoint. -/
def annularContractedUpperRetainedBoundaryOrientedCenter
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : ℝ :=
  if Even
      (annularContractedUpperRetainedTimes p
        (annularContractedUpperRetainedPrefixChronologicalIndex p i₀)) then
    annularContractedUpperRetainedBoundarySignedCenter
      ε A p i₀ upperEndpoint
  else
    -annularContractedUpperRetainedBoundarySignedCenter
      ε A p i₀ upperEndpoint

private theorem gaussParityOrientedLower_sub_add
    (n : ℕ) (lower upper v : ℝ) :
    gaussParityOrientedLower n (lower - v) (upper + v) =
      gaussParityOrientedLower n lower upper - v := by
  by_cases hn : Even n
  · simp only [gaussParityOrientedLower, if_pos hn]
  · simp only [gaussParityOrientedLower, if_neg hn]
    ring

private theorem gaussParityOrientedUpper_sub_add
    (n : ℕ) (lower upper v : ℝ) :
    gaussParityOrientedUpper n (lower - v) (upper + v) =
      gaussParityOrientedUpper n lower upper + v := by
  by_cases hn : Even n
  · simp only [gaussParityOrientedUpper, if_pos hn]
  · simp only [gaussParityOrientedUpper, if_neg hn]
    ring

private theorem gaussParityOrientedLower_center
    (n : ℕ) (center v : ℝ) :
    gaussParityOrientedLower n (center - v) (center + v) =
      (if Even n then center else -center) - v := by
  by_cases hn : Even n
  · simp only [gaussParityOrientedLower, if_pos hn]
  · simp only [gaussParityOrientedLower, if_neg hn]
    ring

private theorem gaussParityOrientedUpper_center
    (n : ℕ) (center v : ℝ) :
    gaussParityOrientedUpper n (center - v) (center + v) =
      (if Even n then center else -center) + v := by
  by_cases hn : Even n
  · simp only [gaussParityOrientedUpper, if_pos hn]
  · simp only [gaussParityOrientedUpper, if_neg hn]
    ring

theorem annularContractedUpperRetainedBaseOrientedLower_eq
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedLower
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) =
      gaussPrescribedParityOrientedLower
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1) j := by
  simpa only [annularContractedUpperRetainedTimes_embedding,
    annularContractedUpperRetainedUpperTag,
    annularUpperRetainedOrientedLower] using!
    annularUpperRetained_actual_orientedLower_eq
      (ε := ε) (A := A)
      (annularContractedUpperRetainedUpperTag p) j

theorem annularContractedUpperRetainedBaseOrientedUpper_eq
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedUpper
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) =
      gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1) j := by
  simpa only [annularContractedUpperRetainedTimes_embedding,
    annularContractedUpperRetainedUpperTag,
    annularUpperRetainedOrientedUpper] using!
    annularUpperRetained_actual_orientedUpper_eq
      (ε := ε) (A := A)
      (annularContractedUpperRetainedUpperTag p) j

theorem annularContractedUpperRetainedBaseOrientedLower_ge
    (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    ε ≤
      gaussParityOrientedLower
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) := by
  rw [annularContractedUpperRetainedBaseOrientedLower_eq]
  exact flattenedAnnular_oriented_lower_ge_epsilon
    hεA hgrid hsigned p.1 j

theorem annularContractedUpperRetainedBaseOrientedLower_lt_upper
    (hεA : ε < A) (hgrid : 0 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedLower
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) <
      gaussParityOrientedUpper
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) := by
  rw [annularContractedUpperRetainedBaseOrientedLower_eq,
    annularContractedUpperRetainedBaseOrientedUpper_eq]
  exact flattenedAnnular_oriented_lower_lt_upper hεA hgrid p.1 j

theorem annularContractedUpperRetainedBaseOrientedUpper_le
    (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedUpper
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) ≤ A := by
  rw [annularContractedUpperRetainedBaseOrientedUpper_eq]
  exact flattenedAnnular_oriented_upper_le hεA hgrid hsigned p.1 j

theorem annularContractedUpperRetainedBoundaryOrientedLower_of_distinguished
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) :
    annularContractedUpperRetainedBoundaryOrientedLower
        ε A eta rho N p i₀ upperEndpoint
        (annularContractedUpperRetainedPrefixChronologicalIndex p i₀) =
      annularContractedUpperRetainedBoundaryOrientedCenter
          ε A p i₀ upperEndpoint -
        annularContractedUpperRetainedPrefixValueRadius eta rho N p := by
  rw [annularContractedUpperRetainedBoundaryOrientedLower,
    annularContractedUpperRetainedBoundarySignedLower,
    annularContractedUpperRetainedBoundarySignedUpper,
    if_pos
      (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
        p i₀),
    if_pos rfl,
    if_pos
      (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
        p i₀),
    if_pos rfl,
    gaussParityOrientedLower_center]
  rfl

theorem annularContractedUpperRetainedBoundaryOrientedUpper_of_distinguished
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) :
    annularContractedUpperRetainedBoundaryOrientedUpper
        ε A eta rho N p i₀ upperEndpoint
        (annularContractedUpperRetainedPrefixChronologicalIndex p i₀) =
      annularContractedUpperRetainedBoundaryOrientedCenter
          ε A p i₀ upperEndpoint +
        annularContractedUpperRetainedPrefixValueRadius eta rho N p := by
  rw [annularContractedUpperRetainedBoundaryOrientedUpper,
    annularContractedUpperRetainedBoundarySignedLower,
    annularContractedUpperRetainedBoundarySignedUpper,
    if_pos
      (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
        p i₀),
    if_pos rfl,
    if_pos
      (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
        p i₀),
    if_pos rfl,
    gaussParityOrientedUpper_center]
  rfl

theorem annularContractedUpperRetainedBoundaryOrientedLower_eq
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedUpperRetainedBoundaryOrientedLower
        ε A eta rho N p i₀ upperEndpoint j =
      if annularContractedUpperRetainedTimes p j ≤
          annularContractedUpperRetainedDelayedDepth p then
        if j =
            annularContractedUpperRetainedPrefixChronologicalIndex p i₀ then
          annularContractedUpperRetainedBoundaryOrientedCenter
              ε A p i₀ upperEndpoint -
            annularContractedUpperRetainedPrefixValueRadius eta rho N p
        else
          gaussParityOrientedLower
              (annularContractedUpperRetainedTimes p j)
              (flattenedAnnularSignedLower ε A p.1 j)
              (flattenedAnnularSignedUpper ε A p.1 j) -
            annularContractedUpperRetainedPrefixValueRadius eta rho N p
      else
        gaussParityOrientedLower
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) := by
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · by_cases hj₀ :
        j = annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    · subst j
      rw [if_pos
        (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
          p i₀), if_pos rfl]
      exact
        annularContractedUpperRetainedBoundaryOrientedLower_of_distinguished
          p i₀ upperEndpoint
    · rw [if_pos hj, if_neg hj₀]
      unfold annularContractedUpperRetainedBoundaryOrientedLower
        annularContractedUpperRetainedBoundarySignedLower
        annularContractedUpperRetainedBoundarySignedUpper
      rw [if_pos hj, if_neg hj₀, if_pos hj, if_neg hj₀,
        gaussParityOrientedLower_sub_add]
  · rw [if_neg hj]
    unfold annularContractedUpperRetainedBoundaryOrientedLower
      annularContractedUpperRetainedBoundarySignedLower
      annularContractedUpperRetainedBoundarySignedUpper
    rw [if_neg hj, if_neg hj]

theorem annularContractedUpperRetainedBoundaryOrientedUpper_eq
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedUpperRetainedBoundaryOrientedUpper
        ε A eta rho N p i₀ upperEndpoint j =
      if annularContractedUpperRetainedTimes p j ≤
          annularContractedUpperRetainedDelayedDepth p then
        if j =
            annularContractedUpperRetainedPrefixChronologicalIndex p i₀ then
          annularContractedUpperRetainedBoundaryOrientedCenter
              ε A p i₀ upperEndpoint +
            annularContractedUpperRetainedPrefixValueRadius eta rho N p
        else
          gaussParityOrientedUpper
              (annularContractedUpperRetainedTimes p j)
              (flattenedAnnularSignedLower ε A p.1 j)
              (flattenedAnnularSignedUpper ε A p.1 j) +
            annularContractedUpperRetainedPrefixValueRadius eta rho N p
      else
        gaussParityOrientedUpper
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) := by
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · by_cases hj₀ :
        j = annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    · subst j
      rw [if_pos
        (annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
          p i₀), if_pos rfl]
      exact
        annularContractedUpperRetainedBoundaryOrientedUpper_of_distinguished
          p i₀ upperEndpoint
    · rw [if_pos hj, if_neg hj₀]
      unfold annularContractedUpperRetainedBoundaryOrientedUpper
        annularContractedUpperRetainedBoundarySignedLower
        annularContractedUpperRetainedBoundarySignedUpper
      rw [if_pos hj, if_neg hj₀, if_pos hj, if_neg hj₀,
        gaussParityOrientedUpper_sub_add]
  · rw [if_neg hj]
    unfold annularContractedUpperRetainedBoundaryOrientedUpper
      annularContractedUpperRetainedBoundarySignedLower
      annularContractedUpperRetainedBoundarySignedUpper
    rw [if_neg hj, if_neg hj]

/-- Full chronological mixed exact/digit tuple for a single endpoint strip. -/
def annularContractedUpperRetainedBoundaryMaskedEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  maskedOrderedEventIntersection
    (fun j ↦
      gaussApproximationWindow
        (Real.log (N : ℝ))
        (annularContractedUpperRetainedTimes p j)
        (annularContractedUpperRetainedBoundaryOrientedLower
          ε A eta rho N p i₀ upperEndpoint j)
        (annularContractedUpperRetainedBoundaryOrientedUpper
          ε A eta rho N p i₀ upperEndpoint j))
    (fun j ↦
      gaussDigitWindowAt
        (Real.log (N : ℝ))
        (annularContractedUpperRetainedTimes p j)
        (annularContractedUpperRetainedBoundaryOrientedLower
          ε A eta rho N p i₀ upperEndpoint j)
        (annularContractedUpperRetainedBoundaryOrientedUpper
          ε A eta rho N p i₀ upperEndpoint j))
    (annularContractedUpperRetainedDelayedFutureMask p)

/-- The boundary event is exactly the union of its lower- and upper-endpoint
complete events. -/
theorem annularContractedUpperRetainedCompleteBoundaryEvent_eq_union
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    annularContractedUpperRetainedCompleteBoundaryEvent
        ε A eta rho N p i₀ =
      annularContractedUpperRetainedCompleteEndpointEvent
          ε A eta rho N p i₀ false ∪
        annularContractedUpperRetainedCompleteEndpointEvent
          ε A eta rho N p i₀ true := by
  rw [annularContractedUpperRetainedCompleteBoundaryEvent,
    annularContractedUpperRetainedPrefixBoundaryEvent,
    closedBoundaryWindowTupleEvent_eq_union_endpointStrips]
  ext x
  simp only [annularContractedUpperRetainedCompleteEndpointEvent,
    annularContractedUpperRetainedPrefixEndpointEvent,
    Bool.false_eq_true, ↓reduceIte, Set.mem_inter_iff,
    Set.mem_union]
  tauto

/-- A complete endpoint-strip event is contained almost everywhere in its
full chronological masked event.  Both branches of the proof retain every
future digit condition. -/
theorem
    ae_annularContractedUpperRetainedCompleteEndpointEvent_subset_masked
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ∀ᵐ x ∂gaussMeasure,
      x ∈ annularContractedUpperRetainedCompleteEndpointEvent
          ε A eta rho N p i₀ upperEndpoint →
        x ∈ annularContractedUpperRetainedBoundaryMaskedEvent
          ε A eta rho N p i₀ upperEndpoint := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro hxComplete
  unfold annularContractedUpperRetainedBoundaryMaskedEvent
  rw [mem_maskedOrderedEventIntersection_iff]
  intro j
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · let z : GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p) :=
      ⟨p.1 j, by
        have hjtime :=
          congrFun (annularContractedUpperRetainedRealization_times p) j
        change
          ((annularContractedUpperRetainedRealization p).1
              (p.1 j).1 (p.1 j).2 : ℕ) =
            annularContractedUpperRetainedTimes p j at hjtime
        rw [hjtime]
        exact hj⟩
    let i :=
      (annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm z
    let j₀ :=
      annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    have heq :
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 =
          p.1 j := by
      change
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p
            ((annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm
              z)).1 =
          p.1 j
      rw [Equiv.apply_symm_apply]
    have hindex : i = i₀ ↔ j = j₀ := by
      constructor
      · intro hii
        apply p.1.injective
        calc
          p.1 j =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 :=
            heq.symm
          _ =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1 := by
            rw [hii]
          _ = p.1 j₀ := by
            simpa only [j₀] using!
              (annularContractedUpperRetainedPrefixChronologicalIndex_label
                p i₀).symm
      · intro hjj
        apply (annularContractedUpperRetainedPrefixOccurrenceEquiv p).injective
        apply Subtype.ext
        calc
          (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 =
              p.1 j := heq
          _ = p.1 j₀ := congrArg p.1 hjj
          _ =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1 := by
            simpa only [j₀] using!
              annularContractedUpperRetainedPrefixChronologicalIndex_label
                p i₀
    have hactive : 0 < k (p.1 j).1 := by
      have hjlt := (p.1 j).2.isLt
      omega
    have hactive₀ :
        0 <
          k
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1.1 := by
      have hi₀lt :=
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1.2.isLt
      omega
    have htimeI :
        ((annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.2 :
              ℕ) =
          annularContractedUpperRetainedTimes p j := by
      rw [heq]
      have hjtime :=
        congrFun (annularContractedUpperRetainedRealization_times p) j
      simpa only [fixedOrderMixedTimes] using! hjtime
    have hcenterLower :
        annularContractedUpperRetainedPrefixLower ε A p i₀ =
          flattenedAnnularSignedLower ε A p.1 j₀ := by
      simp only [annularContractedUpperRetainedPrefixLower,
        activeAnnularOccurrenceSignedLower_of_pos hactive₀]
      rw [←
        annularContractedUpperRetainedPrefixChronologicalIndex_label p i₀]
      rfl
    have hcenterUpper :
        annularContractedUpperRetainedPrefixUpper ε A p i₀ =
          flattenedAnnularSignedUpper ε A p.1 j₀ := by
      simp only [annularContractedUpperRetainedPrefixUpper,
        activeAnnularOccurrenceSignedUpper_of_pos hactive₀]
      rw [←
        annularContractedUpperRetainedPrefixChronologicalIndex_label p i₀]
      rfl
    have hlowerI :
        annularContractedUpperRetainedPrefixLower ε A p i =
          flattenedAnnularSignedLower ε A p.1 j := by
      simp only [annularContractedUpperRetainedPrefixLower,
        heq, activeAnnularOccurrenceSignedLower_of_pos hactive]
      rfl
    have hupperI :
        annularContractedUpperRetainedPrefixUpper ε A p i =
          flattenedAnnularSignedUpper ε A p.1 j := by
      simp only [annularContractedUpperRetainedPrefixUpper,
        heq, activeAnnularOccurrenceSignedUpper_of_pos hactive]
      rfl
    have hxPrefix := hxComplete.2.1
    rw [annularContractedUpperRetainedPrefixEndpointEvent,
      closedEndpointStripWindowTupleEvent, closedWindowTupleEvent] at hxPrefix
    have hi := Set.mem_iInter.mp hxPrefix i
    have hsigned :
        x ∈ gaussSignedApproximationWindow
          (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j)
          (annularContractedUpperRetainedBoundarySignedLower
            ε A eta rho N p i₀ upperEndpoint j)
          (annularContractedUpperRetainedBoundarySignedUpper
            ε A eta rho N p i₀ upperEndpoint j) := by
      refine ⟨⟨hx.1.1, hx.1.2.le⟩, ?_⟩
      change
        annularContractedUpperRetainedPrefixCoordinate p x i ∈
          Icc
            (if i = i₀ then
              (if upperEndpoint then
                  annularContractedUpperRetainedPrefixUpper ε A p i₀
                else
                  annularContractedUpperRetainedPrefixLower ε A p i₀) -
                annularContractedUpperRetainedPrefixValueRadius eta rho N p
            else
              annularContractedUpperRetainedPrefixLower ε A p i -
                annularContractedUpperRetainedPrefixValueRadius eta rho N p)
            (if i = i₀ then
              (if upperEndpoint then
                  annularContractedUpperRetainedPrefixUpper ε A p i₀
                else
                  annularContractedUpperRetainedPrefixLower ε A p i₀) +
                annularContractedUpperRetainedPrefixValueRadius eta rho N p
            else
              annularContractedUpperRetainedPrefixUpper ε A p i +
                annularContractedUpperRetainedPrefixValueRadius eta rho N p)
        at hi
      change
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ))
            (annularContractedUpperRetainedTimes p j) x ∈
          Icc
            (annularContractedUpperRetainedBoundarySignedLower
              ε A eta rho N p i₀ upperEndpoint j)
            (annularContractedUpperRetainedBoundarySignedUpper
              ε A eta rho N p i₀ upperEndpoint j)
      simpa only [
        annularContractedUpperRetainedPrefixCoordinate,
        heq,
        hlowerI, hupperI,
        gaussPrefixMarkedPoint_value_eq_signedScaledApproximation,
        htimeI,
        annularContractedUpperRetainedBoundarySignedLower,
        annularContractedUpperRetainedBoundarySignedUpper,
        if_pos hj,
        hindex,
        j₀,
        annularContractedUpperRetainedBoundarySignedCenter,
        hcenterLower, hcenterUpper] using! hi
    rw [gaussSignedApproximationWindow_eq_oriented] at hsigned
    simpa only [
      maskedCoordinateEvent,
      annularContractedUpperRetainedDelayedFutureMask,
      Nat.not_lt.mpr hj,
      Bool.false_eq_true,
      ↓reduceIte] using! hsigned
  · have hjFuture :
        annularContractedUpperRetainedDelayedDepth p <
          annularContractedUpperRetainedTimes p j :=
      Nat.lt_of_not_ge hj
    let q := annularContractedUpperRetainedUpperTag p
    have hjSplit :
        annularUpperRetainedSplitDepth q <
          annularUpperRetainedTimes q j := by
      exact
        (annularUpperRetained_after_delayed_iff_after_split
          hgrid htime q hN hW j).mp (by
            simpa only [q,
              annularContractedUpperRetainedUpperTag,
              annularContractedUpperRetainedDelayedDepth,
              annularContractedUpperRetainedTimes_embedding] using!
              hjFuture)
    have hjDigit :=
      (mem_annularUpperRetainedFutureDigitTupleEvent_iff
        hgrid htime q hN hW x).mp hxComplete.2.2 j hjSplit
    have hlower :=
      annularUpperRetained_actual_orientedLower_eq
        (ε := ε) (A := A) q j
    have hupper :=
      annularUpperRetained_actual_orientedUpper_eq
        (ε := ε) (A := A) q j
    have hlower' :
        gaussParityOrientedLower
            (annularContractedUpperRetainedTimes p j)
            (flattenedAnnularSignedLower ε A p.1 j)
            (flattenedAnnularSignedUpper ε A p.1 j) =
          annularUpperRetainedOrientedLower ε A q j := by
      simpa only [q,
        annularContractedUpperRetainedTimes_embedding] using! hlower
    have hupper' :
        gaussParityOrientedUpper
            (annularContractedUpperRetainedTimes p j)
            (flattenedAnnularSignedLower ε A p.1 j)
            (flattenedAnnularSignedUpper ε A p.1 j) =
          annularUpperRetainedOrientedUpper ε A q j := by
      simpa only [q,
        annularContractedUpperRetainedTimes_embedding] using! hupper
    have hxIoc : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1.1, hx.1.2.le⟩
    simp only [
      maskedCoordinateEvent,
      annularContractedUpperRetainedDelayedFutureMask,
      hjFuture,
      ↓reduceIte,
      gaussDigitWindowAt,
      Set.mem_inter_iff,
      Set.mem_preimage,
      annularContractedUpperRetainedBoundarySignedLower,
      annularContractedUpperRetainedBoundarySignedUpper,
      if_neg hj,
      annularContractedUpperRetainedBoundaryOrientedLower,
      annularContractedUpperRetainedBoundaryOrientedUpper]
    refine ⟨hxIoc, ?_⟩
    simpa only [q,
      annularContractedUpperRetainedTimes_embedding,
      hlower', hupper'] using! hjDigit

/-- Consequently each complete boundary event is contained in the union of
the two full-dimensional endpoint-strip masked events. -/
theorem ae_annularContractedUpperRetainedCompleteBoundaryEvent_subset_union
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ∀ᵐ x ∂gaussMeasure,
      x ∈ annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p i₀ →
        x ∈
          annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ false ∪
            annularContractedUpperRetainedBoundaryMaskedEvent
              ε A eta rho N p i₀ true := by
  filter_upwards [
    ae_annularContractedUpperRetainedCompleteEndpointEvent_subset_masked
      (ε := ε) (A := A) hgrid htime p i₀ false hN hW,
    ae_annularContractedUpperRetainedCompleteEndpointEvent_subset_masked
      (ε := ε) (A := A) hgrid htime p i₀ true hN hW] with x hlower hupper
  intro hx
  rw [annularContractedUpperRetainedCompleteBoundaryEvent_eq_union p i₀]
    at hx
  rcases hx with hx | hx
  · exact Or.inl (hlower hx)
  · exact Or.inr (hupper hx)

end

end Erdos1002
