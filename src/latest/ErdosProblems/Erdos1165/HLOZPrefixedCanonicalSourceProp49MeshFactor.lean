/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZNoLazyMeshCandidateCreation
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement

/-!
# Canonical Proposition 4.9 mesh factors

This module joins the prefix-correct conditional coordinate law to the
rankwise low-mesh future adapter.  It exposes the two remaining deterministic
seams explicitly: containment of the filtered next event in the selected
candidate union, and stopped observability of that union on fixed creation
atoms.  No probability inequality is an input.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceProp49MeshFactor

open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidateFutureFactor HLOZNoLazyFilteredTransitions
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZNoLazyMeshCandidateCreation
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSpatialAdapter
open LazyDecomposition TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- All deterministic past data needed by the canonical coordinate factor.
In particular, `atom_subset_previous` is the precise conditional-history
compatibility requirement for later ranks. -/
structure CanonicalSourceProp49PastData
    (t : DominoTiling) (o : Orientation) (m k : ℕ) (a : GapScale)
    (low : ℕ) (previous : Set WalkPath) where
  previous_measurable : MeasurableSet previous
  atom_subset_previous : ∀ eta : SourceSupportedIndex t o m k,
    SourceProp49EligibleHistory eta →
    orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
      eta.1.1 eta.1.2 ⊆ previous
  m_gt_one : 1 < m
  rank_pos : 0 < k
  window : Prop49WindowArithmeticAt m a
  shell_arithmetic : ShellZeroWindowArithmeticAt m
  external_arithmetic : ShellZeroExternalWindowArithmeticAt m
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)

namespace CanonicalSourceProp49PastData

noncomputable def coordinateData
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {a : GapScale}
    {low : ℕ} {previous : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous) :=
  sourceProp49FilteredCoordinateData a low previous
    data.previous_measurable data.atom_subset_previous data.m_gt_one
    data.rank_pos data.window data.shell_arithmetic data.external_arithmetic

noncomputable def candidateFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {a : GapScale}
    {low : ℕ} {previous : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous) :=
  data.coordinateData.family

theorem candidateFamily_measurable
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {a : GapScale}
    {low : ℕ} {previous : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous) :
    MeasurableSet data.candidateFamily.someCandidate := by
  unfold HLOZStoppedHistoryCandidateFuture.StoppedHistoryCandidateFamily.someCandidate
  apply MeasurableSet.iUnion
  intro h
  apply MeasurableSet.iUnion
  intro candidate
  apply MeasurableSet.iUnion
  intro hcandidate
  apply (data.coordinateData.family.piece_measurable h).inter
  cases h with
  | none => exact MeasurableSet.empty
  | some eta => exact data.coordinateData.near_measurable eta candidate

/-- Package the already constructed candidate family with a countable
mesh-creation decomposition. -/
noncomputable def meshLowCoordinateData
    {Index : Type} [Countable Index]
    {t : DominoTiling} {o : Orientation} {m k : ℕ} {a : GapScale}
    {low : ℕ} {previous next : Set WalkPath}
    (data : CanonicalSourceProp49PastData t o m k a low previous)
    (creation : CountableMeshCreationData Index data.candidateFamily.someCandidate
      next m k a) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a
      previous next :=
  sourceProp49FirstStripMeshLowCoordinateData a low previous next
    data.previous_measurable data.atom_subset_previous data.m_gt_one
    data.rank_pos data.window data.shell_arithmetic data.external_arithmetic
    creation

end CanonicalSourceProp49PastData

/-! ## No-lazy rankwise future decompositions -/

noncomputable def firstNoLazyMeshCreation
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 1 a.1.1 low Set.univ)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hnext : filteredFirstTransitionEvent stagedCandidate₁ t m a ⊆
      data.candidateFamily.someCandidate)
    (hpast : ∀ nOld,
      IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
        (trajectory ⁻¹' firstCandidatePastAtom
          data.candidateFamily.someCandidate m nOld)) :
    CountableMeshCreationData ℕ data.candidateFamily.someCandidate
      (filteredFirstTransitionEvent stagedCandidate₁ t m a) m 1 a.1.1 :=
  firstCountableMeshCreationData data.candidateFamily.someCandidate
    stagedCandidate₁ t m a hproper data.candidateFamily_measurable
    hcandidate₁ hnext hpast

noncomputable def secondNoLazyMeshCreation
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 2 a.1.2 low
      (filteredFirstTransitionEvent stagedCandidate₁ t m a))
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hnext : filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a ⊆ data.candidateFamily.someCandidate)
    (hpast : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' secondCandidatePastAtom
          data.candidateFamily.someCandidate stagedCandidate₁ t m a z)) :
    CountableMeshCreationData PairCreationIndex
      data.candidateFamily.someCandidate
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) m 2 a.1.2 :=
  secondCountableMeshCreationData data.candidateFamily.someCandidate
    stagedCandidate₁ stagedCandidate₂ t m a hproper
    data.candidateFamily_measurable hcandidate₁ hcandidate₂ hnext hpast

noncomputable def thirdNoLazyMeshCreation
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
    (hpast : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' thirdCandidatePastAtom
          data.candidateFamily.someCandidate stagedCandidate₁ stagedCandidate₂
            t m a z)) :
    CountableMeshCreationData TripleCreationIndex
      data.candidateFamily.someCandidate
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) m 3 a.2 :=
  thirdCountableMeshCreationData data.candidateFamily.someCandidate
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hproper
    data.candidateFamily_measurable hcandidate₁ hcandidate₂ hcandidate₃
    hnext hpast

/-! ## Final mixed-selector inputs -/

noncomputable def firstMeshLowCoordinateData
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 1 a.1.1 low Set.univ)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hnext : filteredFirstTransitionEvent stagedCandidate₁ t m a ⊆
      data.candidateFamily.someCandidate)
    (hpast : ∀ nOld,
      IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
        (trajectory ⁻¹' firstCandidatePastAtom
          data.candidateFamily.someCandidate m nOld)) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m 1 a.1.1
      Set.univ (filteredFirstTransitionEvent stagedCandidate₁ t m a) :=
  data.meshLowCoordinateData <|
    firstNoLazyMeshCreation stagedCandidate₁ data hproper hcandidate₁
      hnext hpast

noncomputable def secondMeshLowCoordinateData
    {t : DominoTiling} {o : Orientation} {m : ℕ} {a : GapTriple}
    {low : ℕ} (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (data : CanonicalSourceProp49PastData t o m 2 a.1.2 low
      (filteredFirstTransitionEvent stagedCandidate₁ t m a))
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hnext : filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a ⊆ data.candidateFamily.someCandidate)
    (hpast : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' secondCandidatePastAtom
          data.candidateFamily.someCandidate stagedCandidate₁ t m a z)) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m 2 a.1.2
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) :=
  data.meshLowCoordinateData <|
    secondNoLazyMeshCreation stagedCandidate₁ stagedCandidate₂ data hproper
      hcandidate₁ hcandidate₂ hnext hpast

noncomputable def thirdMeshLowCoordinateData
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
    (hpast : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' thirdCandidatePastAtom
          data.candidateFamily.someCandidate stagedCandidate₁ stagedCandidate₂
            t m a z)) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m 3 a.2
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) :=
  data.meshLowCoordinateData <|
    thirdNoLazyMeshCreation stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ data hproper hcandidate₁ hcandidate₂ hcandidate₃
      hnext hpast

end

end Erdos1165.HLOZPrefixedCanonicalSourceProp49MeshFactor
