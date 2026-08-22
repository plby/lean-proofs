/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZNoLazyFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49MeshFactor

/-!
# Stopped observability of the canonical Proposition 4.9 screen

The physical stopped fibres are unions of cylinders whose lengths vary with
the insertion vector.  On a fixed rank-`k` creation atom, however, creation
time uniqueness forces every contributing cylinder to have exactly the fixed
old-creation length.  This makes the complete some-candidate event observable
at that old clock.  The proof works on `StepPath`; this is important because
`walkLift` contains the global valid-walk condition, which is not a predicate
of an arbitrary `WalkPath` prefix.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceProp49Observability

open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZGapPointReturn
open HLOZNoLazyFilteredPastObservability
open HLOZNoLazyFilteredTransitions
open HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyMeshCandidateCreation
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49MeshFactor
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZProposition48Candidates
open HLOZSpatialAdapter
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition
open PreStoppingFiber
open StoppedInsertion
open TilingCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- A predicate of actual increment paths which is invariant under equality
of the first `n` increments is measurable in the first-`n` filtration. -/
theorem measurableSet_incrementFiltration_of_stepPrefix_dependent
    (n : ℕ) (P : StepPath → Prop)
    (hP : ∀ ω ω' : StepPath, stepPrefix n ω = stepPrefix n ω' →
      (P ω ↔ P ω')) :
    MeasurableSet[incrementFiltration n] {ω | P ω} := by
  rw [incrementFiltration_apply]
  let A : Set (Fin n → Direction) := {u | P (extendPrefix u)}
  refine ⟨A, (Set.to_countable A).measurableSet, ?_⟩
  ext ω
  change P (extendPrefix (stepPrefix n ω)) ↔ P ω
  apply hP
  exact PreStoppingFiber.stepPrefix_extendPrefix n (stepPrefix n ω)

private theorem sourceProp49ScreenedFiber_preimage_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) {ω ω' : StepPath}
    (hp : stepPrefix n ω = stepPrefix n ω')
    (hcreation : ThresholdCreation (trajectory ω) m k n)
    (_hcreation' : ThresholdCreation (trajectory ω') m k n) :
    trajectory ω ∈ sourceProp49ScreenedFiber
        eta a candidate hcandidate low cap →
      trajectory ω' ∈ sourceProp49ScreenedFiber
        eta a candidate hcandidate low cap := by
  let fiber := SourceFiber eta
  let initial := fiber.initial cap
  let start := fiber.start cap
  let retained := fiber.retained cap
  let coordinateCap := fiber.coordinateCap cap
  let tail := fiber.tail cap
  let predicate := sourceProp49ScreenedPredicate
    eta a candidate hcandidate low cap
  have hlt (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      coordinateCap) :
      (prefixedTilingInsertionPrefixList initial t start retained
        (fun j ↦ (q j : ℕ)) tail).length <
        orientedAllCreationCoordinateCutoff eta.1.1 coordinateCap := by
    simpa only [fiber, initial, start, retained, coordinateCap, tail,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        coordinateCap q
  intro hω
  have hraw : ω ∈ prefixedTilingPreStoppingFiberEvent
      (fiber.stoppingTime cap) initial t start retained coordinateCap tail
        predicate := by
    simpa only [sourceProp49ScreenedFiber, walkLift,
      Set.mem_inter_iff, trajectory_mem_validStepWalk, true_and,
      Set.mem_preimage, stepsOfWalk_trajectory] using hω
  rcases Set.mem_iUnion.mp hraw with ⟨q, hq⟩
  let v := prefixedTilingInsertionPrefixList initial t start retained
    (fun j ↦ (q.1 j : ℕ)) tail
  have hstop : fiber.stoppingTime cap ω = v.length := hq.1
  have hvCreation : ThresholdCreation (trajectory ω) m k v.length := by
    apply (PreStoppingFiber.truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1 coordinateCap)
        v.length ω (hlt q.1)).mp
    exact hstop
  have hvn : v.length = n :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hvCreation hcreation
  have hq' : ω' ∈ prefixedTilingStoppedInsertionAtom
      (fiber.stoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail := by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (fiber.isStoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail q.2.2]
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      (fiber.isStoppingTime cap) initial t start retained
        (fun j ↦ (q.1 j : ℕ)) tail q.2.2] at hq
    calc
      stepPrefix v.length ω' = stepPrefix v.length ω := by
        rw [hvn]
        exact hp.symm
      _ = directionVectorOfList v := hq
  have hraw' : ω' ∈ prefixedTilingPreStoppingFiberEvent
      (fiber.stoppingTime cap) initial t start retained coordinateCap tail
        predicate := Set.mem_iUnion.mpr ⟨q, hq'⟩
  simpa only [sourceProp49ScreenedFiber, walkLift,
    Set.mem_inter_iff, trajectory_mem_validStepWalk, true_and,
    Set.mem_preimage, stepsOfWalk_trajectory] using hraw'

private theorem sourceProp49ScreenedFiber_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) {ω ω' : StepPath}
    (hp : stepPrefix n ω = stepPrefix n ω')
    (hcreation : ThresholdCreation (trajectory ω) m k n)
    (hcreation' : ThresholdCreation (trajectory ω') m k n) :
    trajectory ω ∈ sourceProp49ScreenedFiber
        eta a candidate hcandidate low cap ↔
      trajectory ω' ∈ sourceProp49ScreenedFiber
        eta a candidate hcandidate low cap := by
  exact ⟨sourceProp49ScreenedFiber_preimage_of_stepPrefix_eq
      eta a candidate hcandidate low cap hp hcreation hcreation',
    sourceProp49ScreenedFiber_preimage_of_stepPrefix_eq
      eta a candidate hcandidate low cap hp.symm hcreation' hcreation⟩

/-- One canonical narrow stopped fibre is observable at a fixed old-creation
clock after intersecting with that creation atom. -/
theorem sourceProp49ScreenedFiber_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈ sourceProp49ScreenedFiber
          eta a candidate hcandidate low cap } := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_stepPrefix_dependent n
  intro ω ω' hp
  have hpPath : pathPrefix (trajectory ω) n =
      pathPrefix (trajectory ω') n := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have hcreationIff := TilingDistinguishedTraceInvariant.thresholdCreation_iff_of_pathPrefix_eq
    (m := m) (rank := k) hpPath le_rfl
  constructor
  · rintro ⟨hcreation, hscreen⟩
    have hcreation' := hcreationIff.mp hcreation
    exact ⟨hcreation',
      (sourceProp49ScreenedFiber_preimage_iff_of_stepPrefix_eq
        eta a candidate hcandidate low cap hp hcreation hcreation').mp hscreen⟩
  · rintro ⟨hcreation', hscreen'⟩
    have hcreation := hcreationIff.mpr hcreation'
    exact ⟨hcreation,
      (sourceProp49ScreenedFiber_preimage_iff_of_stepPrefix_eq
        eta a candidate hcandidate low cap hp hcreation hcreation').mpr hscreen'⟩

private theorem sourceProp49Near_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) {ω ω' : StepPath}
    (hp : stepPrefix n ω = stepPrefix n ω')
    (hcreation : ThresholdCreation (trajectory ω) m k n)
    (hcreation' : ThresholdCreation (trajectory ω') m k n) :
    trajectory ω ∈ sourceProp49Near eta a candidate hcandidate low ↔
      trajectory ω' ∈ sourceProp49Near eta a candidate hcandidate low := by
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨cap, hcap⟩
    exact Set.mem_iUnion.mpr ⟨cap,
      (sourceProp49ScreenedFiber_preimage_iff_of_stepPrefix_eq
        eta a candidate hcandidate low cap hp hcreation hcreation').mp hcap⟩
  · intro hω'
    rcases Set.mem_iUnion.mp hω' with ⟨cap, hcap⟩
    exact Set.mem_iUnion.mpr ⟨cap,
      (sourceProp49ScreenedFiber_preimage_iff_of_stepPrefix_eq
        eta a candidate hcandidate low cap hp hcreation hcreation').mpr hcap⟩

private theorem sourceProp49CandidateNear_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) {ω ω' : StepPath}
    (hp : stepPrefix n ω = stepPrefix n ω')
    (hcreation : ThresholdCreation (trajectory ω) m k n)
    (hcreation' : ThresholdCreation (trajectory ω') m k n) :
    trajectory ω ∈ sourceProp49CandidateNear eta a low candidate ↔
      trajectory ω' ∈ sourceProp49CandidateNear eta a low candidate := by
  simpa only [sourceProp49CandidateNear, hcandidate, dite_true] using
    sourceProp49Near_preimage_iff_of_stepPrefix_eq eta a candidate hcandidate
      low hp hcreation hcreation'

/-- The prefix-correct narrow event stays inside the exact supported atom.
This is the deterministic fact that recovers the history piece after a
prefix replacement. -/
theorem sourceProp49CandidateNear_subset_atom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (low : ℕ) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2) :
    sourceProp49CandidateNear eta a low candidate ⊆
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2 := by
  intro s hs
  have hnear : s ∈ sourceProp49Near eta a candidate hcandidate low := by
    simpa only [sourceProp49CandidateNear, hcandidate, dite_true] using hs
  rcases Set.mem_iUnion.mp hnear with ⟨cap, hcap⟩
  rcases hcap with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  apply (SourceFiber eta).atom_sound cap
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q.1, q.2.1.1, q.2.2⟩, ?_⟩⟩
  exact hq

private theorem candidateFamily_preimage_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ} {a : GapScale}
    {low : ℕ} {previous : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous)
    {ω ω' : StepPath} (hp : stepPrefix n ω = stepPrefix n ω')
    (hcreation : ThresholdCreation (trajectory ω) m k n)
    (hcreation' : ThresholdCreation (trajectory ω') m k n)
    (hω : trajectory ω ∈ data.candidateFamily.someCandidate) :
    trajectory ω' ∈ data.candidateFamily.someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate at hω ⊢
  rcases Set.mem_iUnion.mp hω with ⟨history, hhistory⟩
  rcases Set.mem_iUnion.mp hhistory with ⟨candidate, hcandidate⟩
  rcases Set.mem_iUnion.mp hcandidate with ⟨hcandidate, hpiece, hnear⟩
  cases history with
  | none =>
      simp [CanonicalSourceProp49PastData.candidateFamily,
        CanonicalSourceProp49PastData.coordinateData,
        sourceProp49FilteredCoordinateData,
        FilteredOrientedAllCreationLowCoordinateData.family,
        filteredHistoryCandidates] at hcandidate
  | some eta =>
      have heligible : SourceProp49EligibleHistory eta ∧
          candidate ∈ eta.1.2 := by
        change candidate ∈ filteredHistoryCandidates t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory (some eta) at hcandidate
        exact (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
            hcandidate
      have hnear' : trajectory ω' ∈
          sourceProp49CandidateNear eta a low candidate :=
        (sourceProp49CandidateNear_preimage_iff_of_stepPrefix_eq
          eta a candidate heligible.2 low hp hcreation hcreation').mp hnear
      have hatom' := sourceProp49CandidateNear_subset_atom
        eta a low candidate heligible.2 hnear'
      have hprevious' : trajectory ω' ∈ previous :=
        data.atom_subset_previous eta heligible.1 hatom'
      have hpiece' : trajectory ω' ∈ historyPiece t o m k
          (SourceSupportAt t o m) previous (some eta) :=
        ⟨hprevious', hatom'⟩
      exact Set.mem_iUnion.mpr ⟨some eta,
        Set.mem_iUnion.mpr ⟨candidate,
          Set.mem_iUnion.mpr ⟨hcandidate, hpiece', hnear'⟩⟩⟩

/-- The complete eligible some-candidate event is observable at the fixed
rank-`k` creation clock.  No observability premise for the candidate event is
left to the consumer. -/
theorem candidateFamily_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ} {a : GapScale}
    {low : ℕ} {previous : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      { ω | ThresholdCreation (trajectory ω) m k n ∧
        trajectory ω ∈ data.candidateFamily.someCandidate } := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_stepPrefix_dependent n
  intro ω ω' hp
  have hpPath : pathPrefix (trajectory ω) n =
      pathPrefix (trajectory ω') n := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have hcreationIff :=
    TilingDistinguishedTraceInvariant.thresholdCreation_iff_of_pathPrefix_eq
      (m := m) (rank := k) hpPath le_rfl
  constructor
  · rintro ⟨hcreation, hcandidate⟩
    have hcreation' := hcreationIff.mp hcreation
    exact ⟨hcreation', candidateFamily_preimage_of_stepPrefix_eq
      data hp hcreation hcreation' hcandidate⟩
  · rintro ⟨hcreation', hcandidate'⟩
    have hcreation := hcreationIff.mpr hcreation'
    exact ⟨hcreation, candidateFamily_preimage_of_stepPrefix_eq
      data hp.symm hcreation' hcreation hcandidate'⟩

/-- Rank one needs no additional stopped-past premise: the candidate union
itself is observable on the fixed first-creation atom. -/
theorem firstCandidatePastAtom_observable
    {t : DominoTiling} {o : Orientation} {m n : ℕ} {a : GapScale}
    {low : ℕ}
    (data : CanonicalSourceProp49PastData t o m 1 a low Set.univ) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' firstCandidatePastAtom
        data.candidateFamily.someCandidate m n) := by
  have h := candidateFamily_fixedCreation_observable (n := n) data
  have heq : trajectory ⁻¹' firstCandidatePastAtom
        data.candidateFamily.someCandidate m n =
      { ω | ThresholdCreation (trajectory ω) m 1 n ∧
        trajectory ω ∈ data.candidateFamily.someCandidate } := by
    ext ω
    rfl
  rw [heq]
  exact h

/-- Once the already-filtered pair atom is observable, intersecting it with
the canonical candidate screen introduces no new stopped-observability
premise. -/
theorem secondCandidatePastAtom_observable
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 2 a.1.2 low
      (HLOZNoLazyFilteredTransitions.filteredFirstTransitionEvent
        stagedCandidate₁ t m a))
    (z : PairCreationIndex)
    (hfiltered : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' noLazyFilteredFirstPairCreationAtom
        stagedCandidate₁ t m a z)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' secondCandidatePastAtom
        data.candidateFamily.someCandidate stagedCandidate₁ t m a z) := by
  have hcandidate := candidateFamily_fixedCreation_observable
    (n := z.2) data
  have hinter := isMeasurableAtStopping_inter hfiltered hcandidate
  have heq : trajectory ⁻¹' secondCandidatePastAtom
        data.candidateFamily.someCandidate stagedCandidate₁ t m a z =
      (trajectory ⁻¹' noLazyFilteredFirstPairCreationAtom
        stagedCandidate₁ t m a z) ∩
      { ω | ThresholdCreation (trajectory ω) m 2 z.2 ∧
        trajectory ω ∈ data.candidateFamily.someCandidate } := by
    ext ω
    simp only [secondCandidatePastAtom, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hfilteredAtom, hcandidateAtom⟩
      exact ⟨hfilteredAtom, hfilteredAtom.1.2.1, hcandidateAtom⟩
    · rintro ⟨hfilteredAtom, _hcreation, hcandidateAtom⟩
      exact ⟨hfilteredAtom, hcandidateAtom⟩
  rw [heq]
  exact hinter

/-- Rank-three analogue of `secondCandidatePastAtom_observable`. -/
theorem thirdCandidatePastAtom_observable
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 3 a.2 low
      (HLOZNoLazyFilteredTransitions.filteredSecondTransitionEvent
        stagedCandidate₁ stagedCandidate₂ t m a))
    (z : TripleCreationIndex)
    (hfiltered : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' noLazyFilteredSecondTripleCreationAtom
        stagedCandidate₁ stagedCandidate₂ t m a z)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' thirdCandidatePastAtom
        data.candidateFamily.someCandidate stagedCandidate₁
          stagedCandidate₂ t m a z) := by
  have hcandidate := candidateFamily_fixedCreation_observable
    (n := z.2) data
  have hinter := isMeasurableAtStopping_inter hfiltered hcandidate
  have heq : trajectory ⁻¹' thirdCandidatePastAtom
        data.candidateFamily.someCandidate stagedCandidate₁
          stagedCandidate₂ t m a z =
      (trajectory ⁻¹' noLazyFilteredSecondTripleCreationAtom
        stagedCandidate₁ stagedCandidate₂ t m a z) ∩
      { ω | ThresholdCreation (trajectory ω) m 3 z.2 ∧
        trajectory ω ∈ data.candidateFamily.someCandidate } := by
    ext ω
    simp only [thirdCandidatePastAtom, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hfilteredAtom, hcandidateAtom⟩
      exact ⟨hfilteredAtom, hfilteredAtom.1.2.2.1, hcandidateAtom⟩
    · rintro ⟨hfilteredAtom, _hcreation, hcandidateAtom⟩
      exact ⟨hfilteredAtom, hcandidateAtom⟩
  rw [heq]
  exact hinter

/-! ## Rankwise factors with the candidate observability seam closed -/

/-- The canonical rank-one mesh datum now needs only literal containment of
the filtered transition in the selected candidate union. -/
noncomputable def firstMeshLowCoordinateDataOfContainment
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 1 a.1.1 low Set.univ)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hnext : filteredFirstTransitionEvent stagedCandidate₁ t m a ⊆
      data.candidateFamily.someCandidate) :
    HLOZNoLazyInitialBudgetMixedTransitionFactors.FirstStripMeshLowCoordinateData
      HLOZPrefixedProp49CandidateWindowRatio.prop49WindowRatioConstant
      m 1 a.1.1 Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a) :=
  firstMeshLowCoordinateData stagedCandidate₁ data hproper hcandidate₁
    hnext (fun n ↦ firstCandidatePastAtom_observable (n := n) data)

/-- Rank two reuses exactly the staged-candidate stopped observability already
needed by the high branch; the canonical coordinate screen contributes no
additional `hpast` premise. -/
noncomputable def secondMeshLowCoordinateDataOfContainment
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 2 a.1.2 low
      (filteredFirstTransitionEvent stagedCandidate₁ t m a))
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hnext : filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a ⊆ data.candidateFamily.someCandidate)
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (HLOZSpatialAdapter.pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a))) :
    HLOZNoLazyInitialBudgetMixedTransitionFactors.FirstStripMeshLowCoordinateData
      HLOZPrefixedProp49CandidateWindowRatio.prop49WindowRatioConstant
      m 2 a.1.2 (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) :=
  secondMeshLowCoordinateData stagedCandidate₁ stagedCandidate₂ data
    hproper hcandidate₁ hcandidate₂ hnext (fun z ↦
      secondCandidatePastAtom_observable stagedCandidate₁ data z (by
        simpa only [noLazyFilteredFirstPairCreationAtom] using
          pairCreationAtom_inter_filteredFirstTransitionEvent_observable
            stagedCandidate₁ t m a z (hstaged₁ z)))

/-- Rank-three analogue of
`secondMeshLowCoordinateDataOfContainment`. -/
noncomputable def thirdMeshLowCoordinateDataOfContainment
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ}
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 3 a.2 low
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a))
    (hproper : a.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hnext : filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a ⊆ data.candidateFamily.someCandidate)
    (hstaged₁ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (HLOZSpatialAdapter.tripleCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstaged₂ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (HLOZSpatialAdapter.tripleCreationAtom t m a z ∩
          stagedCandidate₂ t m a))) :
    HLOZNoLazyInitialBudgetMixedTransitionFactors.FirstStripMeshLowCoordinateData
      HLOZPrefixedProp49CandidateWindowRatio.prop49WindowRatioConstant
      m 3 a.2
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) :=
  thirdMeshLowCoordinateData stagedCandidate₁ stagedCandidate₂
    stagedCandidate₃ data hproper hcandidate₁ hcandidate₂
      hcandidate₃ hnext (fun z ↦
        thirdCandidatePastAtom_observable stagedCandidate₁ stagedCandidate₂
          data z (by
            simpa only [noLazyFilteredSecondTripleCreationAtom] using
              tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
                stagedCandidate₁ stagedCandidate₂ t m a z
                  (hstaged₁ z) (hstaged₂ z)))

end

end Erdos1165.HLOZPrefixedCanonicalSourceProp49Observability
