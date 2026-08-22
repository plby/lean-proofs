/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZMeshSpatialTransitionFactor
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Atomwise low-mesh future factors

The stopped-coordinate candidate ratio and the later spatial escape are
separate factors.  This file packages the deterministic low-mesh escape
theorem on a fixed old-creation atom and on a countable disjoint collection
of such atoms.  It assumes no transition-probability inequality.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZMeshCandidateFutureFactor

open BoundaryVisitRegeneration HLOZGapStoppedCandidate
open HLOZHighSpatialTransitionFactor HLOZMeshSpatialTransitionFactor
open HLOZPathEvents
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open TerminalParameterBounds

noncomputable section

/-- The literal one-walk escape cost selected by a mesh cell.  The first
cell uses the origin boundary and hence the harmless unit cost; every
positive cell uses the literal radius at its lower spatial edge. -/
def meshEscapeCost (m : Nat) (a : GapScale) : ENNReal :=
  if a.1 = 0 then 1
  else ENNReal.ofReal (literalEscapeProbability (meshLowerSpatialRadius m a))

@[simp] theorem meshEscapeCost_of_zero
    (m : Nat) (a : GapScale) (ha : a.1 = 0) :
    meshEscapeCost m a = 1 := by
  simp [meshEscapeCost, ha]

theorem meshEscapeCost_of_pos
    (m : Nat) (a : GapScale) (ha : 0 < a.1) :
    meshEscapeCost m a =
      ENNReal.ofReal (literalEscapeProbability (meshLowerSpatialRadius m a)) := by
  simp [meshEscapeCost, ha.ne']

/-- Exact stopped-atom data for one low-mesh transition.  All fields are
stopped-history observability or deterministic creation facts. -/
structure MeshCreationAtomData
    (past next : Set WalkPath) (m rank nOld : Nat) (a : GapScale) where
  rank_pos : 0 < rank
  proper_scale : a ∈ properGapMesh
  past_observable : IsMeasurableAtStopping (fun _ : StepPath => nOld)
    (trajectory ⁻¹' past)
  next_creation : ∀ omega, trajectory omega ∈ next →
    trajectory omega ∈ past ∧ ∃ nNew,
      ThresholdCreation (trajectory omega) m rank nOld ∧
      ThresholdCreation (trajectory omega) m (rank + 1) nNew ∧
      thresholdCount (trajectory omega) nNew (m + 1) = 0 ∧
      gapScaleOf m (trajectory omega nOld) (trajectory omega nNew) = a

/-- A fixed low-mesh creation atom supplies the literal future escape
certificate. -/
def meshCreationAtomBoundaryEscapeCertificate
    {past next : Set WalkPath} {m rank nOld : Nat} {a : GapScale}
    (hm : 1 ≤ m) (data : MeshCreationAtomData past next m rank nOld a) :
    BoundaryEscapeFutureFactorCertificate Unit past next
      (meshEscapeCost m a) where
  stop := fun _ => nOld
  location := fun _ => ()
  boundary := fun _ => meshSpatialBoundary m a
  stop_isStopping := isFiniteStoppingTime_const nOld
  pastFiber_observable := by
    intro x
    cases x
    simpa using data.past_observable
  escape_le := by
    intro x _hx
    cases x
    by_cases ha : a.1 = 0
    · rw [meshEscapeCost_of_zero m a ha]
      have hreal : escapeBeforePositiveReturnProbability
          (meshSpatialBoundary m a) ≤ 1 := by
        unfold escapeBeforePositiveReturnProbability
        linarith [measureReal_nonneg (μ := fairSteps)
          (s := positiveReturnBeforeBoundary (meshSpatialBoundary m a))]
      simpa using ENNReal.ofReal_le_ofReal hreal
    · have hapos : 0 < a.1 := Nat.pos_of_ne_zero ha
      rw [meshEscapeCost_of_pos m a hapos,
        meshSpatialBoundary_of_pos m a hapos]
      exact le_rfl
  next_subset := by
    intro omega homega
    change trajectory omega ∈ next at homega
    obtain ⟨hpast, nNew, hold, hnew, hnext, hscale⟩ :=
      data.next_creation omega homega
    refine ⟨hpast, ?_⟩
    exact postStoppingSteps_not_positiveReturnBeforeBoundary_of_creation
      hm data.rank_pos hold hnew hnext data.proper_scale hscale

/-- Countable disjoint stopped-clock atoms carrying the same mesh cell and
therefore the same one-walk escape cost. -/
structure CountableMeshCreationData
    (Index : Type) [Countable Index]
    (previous next : Set WalkPath) (m rank : Nat) (a : GapScale) where
  oldCreation : Index → Nat
  pastPiece : Index → Set WalkPath
  nextPiece : Index → Set WalkPath
  past_pairwise : Pairwise fun i j => Disjoint (pastPiece i) (pastPiece j)
  past_measurable : ∀ i, MeasurableSet (pastPiece i)
  next_measurable : ∀ i, MeasurableSet (nextPiece i)
  past_subset : (⋃ i, pastPiece i) ⊆ previous
  next_union : (⋃ i, nextPiece i) = next
  atom : ∀ i, MeshCreationAtomData (pastPiece i) (nextPiece i)
    m rank (oldCreation i) a

namespace CountableMeshCreationData

/-- Convert deterministic mesh-creation atoms into the atomwise strong-
Markov future factor. -/
def futureFactor
    {Index : Type} [Countable Index]
    {previous next : Set WalkPath} {m rank : Nat} {a : GapScale}
    (hm : 1 ≤ m)
    (data : CountableMeshCreationData Index previous next m rank a) :
    CountableAtomFutureFactor Index Unit previous next (meshEscapeCost m a) where
  pastPiece := data.pastPiece
  nextPiece := data.nextPiece
  past_pairwise := data.past_pairwise
  past_measurable := data.past_measurable
  next_measurable := data.next_measurable
  past_subset := data.past_subset
  next_union := data.next_union
  atom := fun i => meshCreationAtomBoundaryEscapeCertificate hm (data.atom i)

/-- Add a previously constructed stopped-coordinate candidate family and
obtain the literal `.lowAtomwise` source factor. -/
def sourceCorrectTransitionFactor
    {Index : Type} {History Candidate : Type*}
    [Countable Index] [Countable History]
    {previous next : Set WalkPath} {m rank : Nat} {a : GapScale}
    {budget : Nat} {candidateRatio q : ENNReal}
    (hm : 1 ≤ m)
    (candidate : StoppedHistoryCandidateFamily
      History Candidate previous budget candidateRatio)
    (data : CountableMeshCreationData Index candidate.someCandidate
      next m rank a)
    (cost_le : (budget : ENNReal) * candidateRatio * meshEscapeCost m a ≤ q) :
    SourceCorrectTransitionFactor History Candidate Unit previous next q :=
  .lowAtomwise budget candidateRatio (meshEscapeCost m a)
    { candidate := candidate, escape := data.futureFactor hm } cost_le

end CountableMeshCreationData

end

end Erdos1165.HLOZMeshCandidateFutureFactor
