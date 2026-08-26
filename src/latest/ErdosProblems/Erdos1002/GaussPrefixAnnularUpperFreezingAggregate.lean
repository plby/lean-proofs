import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFreezingPointwise
import ErdosProblems.Erdos1002.GaussHeterogeneousMaskedTupleReplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate character freezing for contracted upper annular tuples

Every event below retains both the delayed denominator-good restriction
and the complete future digit block.  In particular, the future block is
never replaced by the pointwise bound `1` before the full tagged event
mass has been formed.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperFreezingAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- Signed lower endpoints of the delayed prefix coordinates. -/
def annularContractedUpperRetainedPrefixLower
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))) → ℝ :=
  fun i ↦
    activeAnnularOccurrenceSignedLower k ε A
      ((annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1)

/-- Signed upper endpoints of the delayed prefix coordinates. -/
def annularContractedUpperRetainedPrefixUpper
    (ε A : ℝ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))) → ℝ :=
  fun i ↦
    activeAnnularOccurrenceSignedUpper k ε A
      ((annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1)

/-- Literal selected signed value at each delayed-prefix coordinate. -/
def annularContractedUpperRetainedPrefixCoordinate
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) :
    Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))) → ℝ :=
  fun i ↦
    let z := annularContractedUpperRetainedPrefixOccurrenceEquiv p i
    (gaussPrefixMarkedPoint N
      ((annularContractedUpperRetainedRealization p).1
        z.1.1 z.1.2)
      (selectedGaussPrefixWord
        ((annularContractedUpperRetainedRealization p).1
          z.1.1 z.1.2) x) x).2.1

/-- Common signed-value freezing radius for one contracted upper tag. -/
def annularContractedUpperRetainedPrefixValueRadius
    (eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℝ :=
  gaussPrefixGoodValueFreezingRadius N
    (annularContractedUpperRetainedShallowDepth p)
    (annularContractedUpperRetainedDelayedDepth p)
    (annularDepthAmbientSize N)
    (upperGoodTransferDenominatorTolerance eta rho)

/-- Enlarged prefix tuple used by the phase-freezing error. -/
def annularContractedUpperRetainedPrefixPhaseEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  let v :=
    annularContractedUpperRetainedPrefixValueRadius eta rho N p
  closedWindowTupleEvent
    (fun i ↦
      annularContractedUpperRetainedPrefixLower ε A p i - v)
    (fun i ↦
      annularContractedUpperRetainedPrefixUpper ε A p i + v)
    (annularContractedUpperRetainedPrefixCoordinate p)

/-- Prefix tuple with one endpoint strip and every other prefix window
enlarged. -/
def annularContractedUpperRetainedPrefixBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) : Set ℝ :=
  closedBoundaryWindowTupleEvent
    (annularContractedUpperRetainedPrefixLower ε A p)
    (annularContractedUpperRetainedPrefixUpper ε A p)
    (annularContractedUpperRetainedPrefixCoordinate p)
    (annularContractedUpperRetainedPrefixValueRadius eta rho N p) j

/-- Complete phase-error event. -/
def annularContractedUpperRetainedCompletePhaseEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho) ∩
    (annularContractedUpperRetainedPrefixPhaseEvent
        ε A eta rho N p ∩
      annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p))

/-- Complete endpoint-strip error event. -/
def annularContractedUpperRetainedCompleteBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ)
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
    (annularContractedUpperRetainedPrefixBoundaryEvent
        ε A eta rho N p j ∩
      annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p))

/-! ## Full chronological masked events -/

/-- Chronological index belonging to one enumerated delayed-prefix
occurrence. -/
def annularContractedUpperRetainedPrefixChronologicalIndex
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    Fin (MixedOccurrenceCount k) :=
  p.1.symm
    (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1

/-- Signed lower endpoints on the complete chronological tuple: enlarged
on the delayed prefix and unchanged on the future. -/
def annularContractedUpperRetainedPhaseSignedLower
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  if annularContractedUpperRetainedTimes p j ≤
      annularContractedUpperRetainedDelayedDepth p then
    flattenedAnnularSignedLower ε A p.1 j -
      annularContractedUpperRetainedPrefixValueRadius eta rho N p
  else
    flattenedAnnularSignedLower ε A p.1 j

/-- Signed upper endpoints on the complete chronological tuple: enlarged
on the delayed prefix and unchanged on the future. -/
def annularContractedUpperRetainedPhaseSignedUpper
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  if annularContractedUpperRetainedTimes p j ≤
      annularContractedUpperRetainedDelayedDepth p then
    flattenedAnnularSignedUpper ε A p.1 j +
      annularContractedUpperRetainedPrefixValueRadius eta rho N p
  else
    flattenedAnnularSignedUpper ε A p.1 j

/-- Positive endpoints obtained from the actual prescribed parity of the
chronological depth. -/
def annularContractedUpperRetainedPhaseOrientedLower
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussParityOrientedLower
    (annularContractedUpperRetainedTimes p j)
    (annularContractedUpperRetainedPhaseSignedLower ε A eta rho N p j)
    (annularContractedUpperRetainedPhaseSignedUpper ε A eta rho N p j)

def annularContractedUpperRetainedPhaseOrientedUpper
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussParityOrientedUpper
    (annularContractedUpperRetainedTimes p j)
    (annularContractedUpperRetainedPhaseSignedLower ε A eta rho N p j)
    (annularContractedUpperRetainedPhaseSignedUpper ε A eta rho N p j)

/-- Only genuinely future coordinates are digitized. -/
def annularContractedUpperRetainedDelayedFutureMask
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : Bool :=
  if annularContractedUpperRetainedDelayedDepth p <
      annularContractedUpperRetainedTimes p j then true else false

/-- Full-dimensional mixed exact/digit event dominating the complete
phase event. -/
def annularContractedUpperRetainedPhaseMaskedEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : Set ℝ :=
  maskedOrderedEventIntersection
    (fun j ↦
      gaussApproximationWindow
        (Real.log (N : ℝ))
        (annularContractedUpperRetainedTimes p j)
        (annularContractedUpperRetainedPhaseOrientedLower
          ε A eta rho N p j)
        (annularContractedUpperRetainedPhaseOrientedUpper
          ε A eta rho N p j))
    (fun j ↦
      gaussDigitWindowAt
        (Real.log (N : ℝ))
        (annularContractedUpperRetainedTimes p j)
        (annularContractedUpperRetainedPhaseOrientedLower
          ε A eta rho N p j)
        (annularContractedUpperRetainedPhaseOrientedUpper
          ε A eta rho N p j))
    (annularContractedUpperRetainedDelayedFutureMask p)

theorem annularContractedUpperRetainedPrefixChronologicalIndex_label
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    p.1 (annularContractedUpperRetainedPrefixChronologicalIndex p i) =
      (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 := by
  exact p.1.apply_symm_apply _

theorem annularContractedUpperRetainedPrefixChronologicalIndex_time
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    annularContractedUpperRetainedTimes p
        (annularContractedUpperRetainedPrefixChronologicalIndex p i) =
      ((annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.2 :
          ℕ) := by
  let j := annularContractedUpperRetainedPrefixChronologicalIndex p i
  have htimes :=
    congrFun (annularContractedUpperRetainedRealization_times p) j
  change
    ((annularContractedUpperRetainedRealization p).1
        (p.1 j).1 (p.1 j).2 : ℕ) =
      annularContractedUpperRetainedTimes p j at htimes
  rw [annularContractedUpperRetainedPrefixChronologicalIndex_label p i]
    at htimes
  exact htimes.symm

theorem annularContractedUpperRetainedPrefixChronologicalIndex_le_delayed
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    annularContractedUpperRetainedTimes p
        (annularContractedUpperRetainedPrefixChronologicalIndex p i) ≤
      annularContractedUpperRetainedDelayedDepth p := by
  rw [annularContractedUpperRetainedPrefixChronologicalIndex_time p i]
  exact (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).2

theorem measurable_annularContractedUpperRetainedPrefixCoordinate
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    Measurable
      (fun x ↦
        annularContractedUpperRetainedPrefixCoordinate p x i) := by
  unfold annularContractedUpperRetainedPrefixCoordinate
  dsimp only
  simpa only [
    gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using!
    (measurable_gaussSignedScaledApproximationCoordinate
      (Real.log (N : ℝ))
      ((annularContractedUpperRetainedRealization p).1
        ((annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1)
        ((annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.2)))

theorem measurableSet_annularContractedUpperRetainedPrefixPhaseEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    MeasurableSet
      (annularContractedUpperRetainedPrefixPhaseEvent
        ε A eta rho N p) := by
  unfold annularContractedUpperRetainedPrefixPhaseEvent
  exact measurableSet_closedWindowTupleEvent _ _
    (annularContractedUpperRetainedPrefixCoordinate p)
    (measurable_annularContractedUpperRetainedPrefixCoordinate p)

theorem measurableSet_annularContractedUpperRetainedPrefixBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    MeasurableSet
      (annularContractedUpperRetainedPrefixBoundaryEvent
        ε A eta rho N p j) := by
  unfold annularContractedUpperRetainedPrefixBoundaryEvent
  exact measurableSet_closedBoundaryWindowTupleEvent _ _
    (annularContractedUpperRetainedPrefixCoordinate p) _ j
    (measurable_annularContractedUpperRetainedPrefixCoordinate p)

theorem measurableSet_annularContractedUpperRetainedCompletePhaseEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    MeasurableSet
      (annularContractedUpperRetainedCompletePhaseEvent
        ε A eta rho N p) := by
  exact
    (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).inter
      ((measurableSet_annularContractedUpperRetainedPrefixPhaseEvent
        ε A eta rho N p).inter
        (measurableSet_annularUpperRetainedFutureDigitTupleEvent
          (ε := ε) (A := A)
          (annularContractedUpperRetainedUpperTag p)))

theorem measurableSet_annularContractedUpperRetainedCompleteBoundaryEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p)))) :
    MeasurableSet
      (annularContractedUpperRetainedCompleteBoundaryEvent
        ε A eta rho N p j) := by
  exact
    (measurableSet_gaussDenominatorPrefixGoodEvent _ _ _).inter
      ((measurableSet_annularContractedUpperRetainedPrefixBoundaryEvent
        ε A eta rho N p j).inter
        (measurableSet_annularUpperRetainedFutureDigitTupleEvent
          (ε := ε) (A := A)
          (annularContractedUpperRetainedUpperTag p)))

/-- Event form of the deterministic character envelope before attaching
the good event and future block. -/
theorem
    annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope_eq
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) :
    annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
        ε A eta rho N k hr mode hmode p x =
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        (annularContractedUpperRetainedPrefixPhaseEvent
          ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x +
      ∑ j,
        (annularContractedUpperRetainedPrefixBoundaryEvent
          ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  unfold
    annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope
  dsimp only
  change
    annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        closedIntervalIndicatorProduct
          (fun i ↦
            annularContractedUpperRetainedPrefixLower ε A p i -
              annularContractedUpperRetainedPrefixValueRadius
                eta rho N p)
          (fun i ↦
            annularContractedUpperRetainedPrefixUpper ε A p i +
              annularContractedUpperRetainedPrefixValueRadius
                eta rho N p)
          (annularContractedUpperRetainedPrefixCoordinate p x) +
      ∑ j,
        closedIntervalBoundaryIndicator
            (annularContractedUpperRetainedPrefixLower ε A p j)
            (annularContractedUpperRetainedPrefixUpper ε A p j)
            (annularContractedUpperRetainedPrefixValueRadius eta rho N p)
            (annularContractedUpperRetainedPrefixCoordinate p x j) *
          ∏ i ∈
              (Finset.univ : Finset
                (Fin (Fintype.card
                  (GaussPrefixMixedPrefixOccurrence N k
                    (annularContractedUpperRetainedRealization p).1
                    (annularContractedUpperRetainedDelayedDepth p))))).erase j,
            closedIntervalIndicator
              (annularContractedUpperRetainedPrefixLower ε A p i -
                annularContractedUpperRetainedPrefixValueRadius
                  eta rho N p)
              (annularContractedUpperRetainedPrefixUpper ε A p i +
                annularContractedUpperRetainedPrefixValueRadius
                  eta rho N p)
              (annularContractedUpperRetainedPrefixCoordinate p x i) =
      _
  rw [closedIntervalIndicatorProduct_eq_eventIndicator]
  simp_rw [boundaryIndicatorProduct_eq_eventIndicator]
  rfl

/-- Exact pointwise decomposition of the complete deterministic freezing
envelope into full prefix--future event indicators. -/
theorem annularContractedUpperRetainedJointFreezingEnvelope_eq_events
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (x : ℝ) :
    annularContractedUpperRetainedJointFreezingEnvelope
        ε A eta rho N k hr mode hmode p x =
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        (annularContractedUpperRetainedCompletePhaseEvent
          ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x +
      ∑ j,
        (annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  let G :=
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let U :=
    annularUpperRetainedFutureDigitTupleEvent ε A
      (annularContractedUpperRetainedUpperTag p)
  have hfuture :
      annularContractedUpperRetainedFutureDigitBlock ε A p x =
        U.indicator (fun _ ↦ (1 : ℂ)) x := by
    unfold annularContractedUpperRetainedFutureDigitBlock
      annularContractedUpperRetainedUpperTag U
    exact
      annularUpperRetainedFutureDigitBlock_eq_eventIndicator
        (ε := ε) (A := A)
        (annularContractedUpperRetainedToUpper p) x
  by_cases hxG : x ∈ G
  · by_cases hxU : x ∈ U
    · have hphaseIndicator :
          (annularContractedUpperRetainedCompletePhaseEvent
              ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x =
            (annularContractedUpperRetainedPrefixPhaseEvent
              ε A eta rho N p).indicator (fun _ ↦ (1 : ℝ)) x := by
        by_cases hxP :
            x ∈ annularContractedUpperRetainedPrefixPhaseEvent
              ε A eta rho N p
        · rw [Set.indicator_of_mem hxP]
          rw [Set.indicator_of_mem (by
            exact ⟨hxG, hxP, hxU⟩)]
        · rw [Set.indicator_of_notMem hxP]
          rw [Set.indicator_of_notMem (by
            intro hx
            exact hxP hx.2.1)]
      have hboundaryIndicator :
          ∀ j,
            (annularContractedUpperRetainedCompleteBoundaryEvent
                ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x =
              (annularContractedUpperRetainedPrefixBoundaryEvent
                ε A eta rho N p j).indicator (fun _ ↦ (1 : ℝ)) x := by
        intro j
        by_cases hxB :
            x ∈ annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p j
        · rw [Set.indicator_of_mem hxB]
          rw [Set.indicator_of_mem (by
            exact ⟨hxG, hxB, hxU⟩)]
        · rw [Set.indicator_of_notMem hxB]
          rw [Set.indicator_of_notMem (by
            intro hx
            exact hxB hx.2.1)]
      unfold annularContractedUpperRetainedJointFreezingEnvelope
      rw [Set.indicator_of_mem (by simpa only [G] using! hxG)]
      rw [hfuture, Set.indicator_of_mem hxU, norm_one, mul_one]
      rw [
        annularContractedUpperRetainedDeterministicCharacterFreezingEnvelope_eq]
      rw [hphaseIndicator]
      simp_rw [hboundaryIndicator]
    · have hnotPhase :
          x ∉ annularContractedUpperRetainedCompletePhaseEvent
            ε A eta rho N p := by
        intro hx
        exact hxU hx.2.2
      have hnotBoundary :
          ∀ j,
            x ∉ annularContractedUpperRetainedCompleteBoundaryEvent
              ε A eta rho N p j := by
        intro j hx
        exact hxU hx.2.2
      unfold annularContractedUpperRetainedJointFreezingEnvelope
      rw [Set.indicator_of_mem (by simpa only [G] using! hxG)]
      rw [hfuture, Set.indicator_of_notMem hxU, norm_zero, mul_zero]
      rw [Set.indicator_of_notMem hnotPhase, mul_zero]
      simp_rw [Set.indicator_of_notMem (hnotBoundary _)]
      simp
  · unfold annularContractedUpperRetainedJointFreezingEnvelope
    rw [Set.indicator_of_notMem (by simpa only [G] using! hxG)]
    have hnotPhase :
        x ∉ annularContractedUpperRetainedCompletePhaseEvent
          ε A eta rho N p := by
      intro hx
      exact hxG hx.1
    have hnotBoundary :
        ∀ j,
          x ∉ annularContractedUpperRetainedCompleteBoundaryEvent
            ε A eta rho N p j := by
      intro j hx
      exact hxG hx.1
    rw [Set.indicator_of_notMem hnotPhase, mul_zero]
    simp_rw [Set.indicator_of_notMem (hnotBoundary _)]
    simp

/-- Integrated event-mass identity.  Absolute summability is now reduced
to masses of complete tagged prefix--future events. -/
theorem integral_annularContractedUpperRetainedJointFreezingEnvelope_eq
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    (∫ x,
      annularContractedUpperRetainedJointFreezingEnvelope
        ε A eta rho N k hr mode hmode p x ∂gaussMeasure) =
      annularContractedUpperRetainedPhaseFreezingMajorant
          eta rho N k hr mode hmode p *
        gaussMeasure.real
          (annularContractedUpperRetainedCompletePhaseEvent
            ε A eta rho N p) +
      ∑ j,
        gaussMeasure.real
          (annularContractedUpperRetainedCompleteBoundaryEvent
            ε A eta rho N p j) := by
  have hphase :=
    measurableSet_annularContractedUpperRetainedCompletePhaseEvent
      ε A eta rho N p
  have hboundary :
      ∀ j, MeasurableSet
        (annularContractedUpperRetainedCompleteBoundaryEvent
          ε A eta rho N p j) :=
    measurableSet_annularContractedUpperRetainedCompleteBoundaryEvent
      ε A eta rho N p
  rw [integral_congr_ae
    (ae_of_all gaussMeasure fun x ↦
      annularContractedUpperRetainedJointFreezingEnvelope_eq_events
        ε A eta rho N p x)]
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

end

end Erdos1002
