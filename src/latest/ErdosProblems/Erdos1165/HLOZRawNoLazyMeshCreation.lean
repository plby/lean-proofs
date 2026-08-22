/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyMeshCandidateCreation

/-!
# Candidate-independent no-lazy mesh creation atoms

The future spatial escape depends only on the raw fixed old-creation atom.
This module constructs that countable decomposition before choosing any
canonical or transported Proposition 4.9 candidate row.  A row can then be
inserted by exact stopped-event intersection.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZRawNoLazyMeshCreation

open HLOZGapFixedPair HLOZHighSpatialTransitionFactor
open HLOZMeshCandidateFutureFactor
open HLOZNoLazyFilteredPastObservability HLOZNoLazyFilteredTransitions
open HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyMeshCandidateCreation HLOZPathEvents HLOZSpatialAdapter

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- Raw rank-one mesh decomposition, before selecting a source row. -/
noncomputable def firstRawCountableMeshCreationData
    (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a)) :
    CountableMeshCreationData ℕ Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      m 1 a.1.1 :=
  firstCountableMeshCreationData Set.univ stagedCandidate₁ t m a hproper
    MeasurableSet.univ hcandidate₁ (fun _ _ ↦ Set.mem_univ _) (fun n ↦ by
      apply isMeasurableAtStopping_const_of_measurableSet
      simpa only [firstCandidatePastAtom, inter_univ, firstCreationAtom,
        thresholdCreationSet, Set.preimage_ofPred_eq] using
          measurableSet_trajectory_thresholdCreation_filtration m 1 n)

/-- Raw rank-two mesh decomposition.  The only nonstructural input is the
same staged-candidate stopped observability already required by the high
branch. -/
noncomputable def secondRawCountableMeshCreationData
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a))) :
    CountableMeshCreationData PairCreationIndex Set.univ
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) m 2 a.1.2 :=
  secondCountableMeshCreationData Set.univ stagedCandidate₁ stagedCandidate₂
    t m a hproper MeasurableSet.univ hcandidate₁ hcandidate₂
      (fun _ _ ↦ Set.mem_univ _) (fun z ↦ by
        simpa only [secondCandidatePastAtom, inter_univ,
          noLazyFilteredFirstPairCreationAtom] using
          pairCreationAtom_inter_filteredFirstTransitionEvent_observable
            stagedCandidate₁ t m a z (hstaged₁ z))

/-- Raw rank-three mesh decomposition. -/
noncomputable def thirdRawCountableMeshCreationData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hstaged₁ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstaged₂ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₂ t m a))) :
    CountableMeshCreationData TripleCreationIndex Set.univ
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) m 3 a.2 :=
  thirdCountableMeshCreationData Set.univ stagedCandidate₁ stagedCandidate₂
    stagedCandidate₃ t m a hproper MeasurableSet.univ hcandidate₁
      hcandidate₂ hcandidate₃ (fun _ _ ↦ Set.mem_univ _) (fun z ↦ by
        simpa only [thirdCandidatePastAtom, inter_univ,
          noLazyFilteredSecondTripleCreationAtom] using
          tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
            stagedCandidate₁ stagedCandidate₂ t m a z
              (hstaged₁ z) (hstaged₂ z))

end

end Erdos1165.HLOZRawNoLazyMeshCreation
