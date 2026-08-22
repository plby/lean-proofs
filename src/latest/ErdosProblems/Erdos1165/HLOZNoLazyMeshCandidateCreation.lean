/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZMeshCandidateFutureFactor
import ErdosProblems.Erdos1165.HLOZNoLazyHighSpatialTransitionFactor

/-!
# Countable low-mesh creation atoms after the candidate screen

The Proposition 4.9 coordinate screen precedes the future spatial escape.
This file intersects the standard no-lazy rank-one/two/three creation atoms
with that screened past and constructs `CountableMeshCreationData`.  The only
new input is stopped observability of those intersections; the creation and
mesh facts are derived from the filtered transition definitions.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZNoLazyMeshCandidateCreation

open HLOZFilteredTransitionAssembly HLOZMeshCandidateFutureFactor
open HLOZNoLazyFilteredTransitions
open HLOZNoLazyHighSpatialTransitionFactor HLOZPathEvents
open HLOZSpatialAdapter

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## Fixed-clock atoms -/

def firstCandidatePastAtom
    (candidatePast : Set WalkPath) (m nOld : ℕ) : Set WalkPath :=
  firstCreationAtom m nOld ∩ candidatePast

def secondCandidatePastAtom
    (candidatePast : Set WalkPath) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) : Set WalkPath :=
  noLazyFilteredFirstPairCreationAtom stagedCandidate₁ t m a z ∩
    candidatePast

def thirdCandidatePastAtom
    (candidatePast : Set WalkPath)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) : Set WalkPath :=
  noLazyFilteredSecondTripleCreationAtom stagedCandidate₁ stagedCandidate₂
    t m a z ∩ candidatePast

theorem firstMeshCreationAtomData
    (candidatePast : Set WalkPath) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (nOld : ℕ)
    (hproper : a.1.1 ∈ properGapMesh)
    (hnextCandidate : filteredFirstTransitionEvent stagedCandidate₁ t m a ⊆
      candidatePast)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      (trajectory ⁻¹' firstCandidatePastAtom candidatePast m nOld)) :
    MeshCreationAtomData
      (firstCandidatePastAtom candidatePast m nOld)
      (noLazyFilteredFirstTransitionAtom stagedCandidate₁ t m a nOld)
      m 1 nOld a.1.1 where
  rank_pos := by omega
  proper_scale := hproper
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, holdAtom⟩
    rcases Set.mem_iUnion.mp hfiltered.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hpair⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      thresholdCount (trajectory omega) n₂ (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₂) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 at hpair
    have hn₁eq : n₁ = nOld :=
      thresholdCreation_time_unique hpair.1 holdAtom
    subst n₁
    exact ⟨⟨holdAtom, hnextCandidate hfiltered⟩, n₂, hpair.1,
      hpair.2.1, hpair.2.2.1, hpair.2.2.2.2⟩

theorem secondMeshCreationAtomData
    (candidatePast : Set WalkPath)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) (hproper : a.1.2 ∈ properGapMesh)
    (hnextCandidate :
      filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a ⊆ candidatePast)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' secondCandidatePastAtom candidatePast
        stagedCandidate₁ t m a z)) :
    MeshCreationAtomData
      (secondCandidatePastAtom candidatePast stagedCandidate₁ t m a z)
      (noLazyFilteredSecondTransitionAtom stagedCandidate₁ stagedCandidate₂
        t m a z) m 2 z.2 a.1.2 where
  rank_pos := by omega
  proper_scale := hproper
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, hpairAtom⟩
    have hprevious := filteredSecondTransitionEvent_subset_filteredFirst
      stagedCandidate₁ stagedCandidate₂ t m a hfiltered
    have hpast' : trajectory omega ∈ secondCandidatePastAtom candidatePast
        stagedCandidate₁ t m a z :=
      ⟨⟨hpairAtom, hprevious⟩, hnextCandidate hfiltered⟩
    rcases Set.mem_iUnion.mp hfiltered.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
    rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, htriple⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      ThresholdCreation (trajectory omega) m 3 n₃ ∧
      thresholdCount (trajectory omega) n₃ (m + 1) = 0 ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₂) ∧
      ¬Tilings.sameDomino t (trajectory omega n₁) (trajectory omega n₃) ∧
      ¬Tilings.sameDomino t (trajectory omega n₂) (trajectory omega n₃) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 ∧
      gapScaleOf m (trajectory omega n₂) (trajectory omega n₃) = a.1.2 at htriple
    have hn₁ : n₁ = z.1 :=
      thresholdCreation_time_unique htriple.1 hpairAtom.1
    have hn₂ : n₂ = z.2 :=
      thresholdCreation_time_unique htriple.2.1 hpairAtom.2.1
    subst n₁
    subst n₂
    exact ⟨hpast', n₃, htriple.2.1, htriple.2.2.1,
      htriple.2.2.2.1, htriple.2.2.2.2.2.2.2.2⟩

theorem thirdMeshCreationAtomData
    (candidatePast : Set WalkPath)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) (hproper : a.2 ∈ properGapMesh)
    (hnextCandidate : filteredThirdTransitionEvent stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a ⊆ candidatePast)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
      (trajectory ⁻¹' thirdCandidatePastAtom candidatePast stagedCandidate₁
        stagedCandidate₂ t m a z)) :
    MeshCreationAtomData
      (thirdCandidatePastAtom candidatePast stagedCandidate₁ stagedCandidate₂
        t m a z)
      (noLazyFilteredThirdTransitionAtom stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a z) m 3 z.2 a.2 where
  rank_pos := by omega
  proper_scale := hproper
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, htripleAtom⟩
    have hprevious := filteredThirdTransitionEvent_subset_filteredSecond
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hfiltered
    have hpast' : trajectory omega ∈ thirdCandidatePastAtom candidatePast
        stagedCandidate₁ stagedCandidate₂ t m a z :=
      ⟨⟨htripleAtom, hprevious⟩, hnextCandidate hfiltered⟩
    rcases Set.mem_iUnion.mp hfiltered.1.1 with ⟨n₁, hn₁⟩
    rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
    rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
    rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad⟩
    change ThresholdCreation (trajectory omega) m 1 n₁ ∧
      ThresholdCreation (trajectory omega) m 2 n₂ ∧
      ThresholdCreation (trajectory omega) m 3 n₃ ∧
      ThresholdCreation (trajectory omega) m 4 n₄ ∧
      thresholdCount (trajectory omega) n₄ (m + 1) = 0 ∧
      fourPointsSeparated t (trajectory omega n₁) (trajectory omega n₂)
        (trajectory omega n₃) (trajectory omega n₄) ∧
      gapScaleOf m (trajectory omega n₁) (trajectory omega n₂) = a.1.1 ∧
      gapScaleOf m (trajectory omega n₂) (trajectory omega n₃) = a.1.2 ∧
      gapScaleOf m (trajectory omega n₃) (trajectory omega n₄) = a.2 at hquad
    have hn₁ : n₁ = z.1.1 :=
      thresholdCreation_time_unique hquad.1 htripleAtom.1
    have hn₂ : n₂ = z.1.2 :=
      thresholdCreation_time_unique hquad.2.1 htripleAtom.2.1
    have hn₃ : n₃ = z.2 :=
      thresholdCreation_time_unique hquad.2.2.1 htripleAtom.2.2.1
    subst n₁
    subst n₂
    subst n₃
    exact ⟨hpast', n₄, hquad.2.2.1, hquad.2.2.2.1,
      hquad.2.2.2.2.1, hquad.2.2.2.2.2.2.2.2⟩

/-! ## Countable disintegrations -/

noncomputable def firstCountableMeshCreationData
    (candidatePast : Set WalkPath) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidatePast : MeasurableSet candidatePast)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hnextCandidate : filteredFirstTransitionEvent stagedCandidate₁ t m a ⊆
      candidatePast)
    (hpast : ∀ nOld, IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      (trajectory ⁻¹' firstCandidatePastAtom candidatePast m nOld)) :
    CountableMeshCreationData ℕ candidatePast
      (filteredFirstTransitionEvent stagedCandidate₁ t m a) m 1 a.1.1 where
  oldCreation := id
  pastPiece := firstCandidatePastAtom candidatePast m
  nextPiece := noLazyFilteredFirstTransitionAtom stagedCandidate₁ t m a
  past_pairwise := by
    intro n n' hne
    exact (firstCreationAtom_pairwiseDisjoint m hne).mono
      inter_subset_left inter_subset_left
  past_measurable := fun n ↦
    (measurableSet_firstCreationAtom m n).inter hcandidatePast
  next_measurable := fun n ↦
    (measurableSet_filteredFirstTransitionEvent stagedCandidate₁
      t m a hcandidate₁).inter (measurableSet_firstCreationAtom m n)
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
    exact hn.2
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
      exact hn.1
    · intro s hs
      have hcreated :=
        firstTransitionEvent_subset_iUnion_firstCreationAtom t m a hs.1
      rcases Set.mem_iUnion.mp hcreated with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, hs, hn⟩
  atom := fun n ↦ firstMeshCreationAtomData candidatePast stagedCandidate₁
    t m a n hproper hnextCandidate (hpast n)

noncomputable def secondCountableMeshCreationData
    (candidatePast : Set WalkPath)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidatePast : MeasurableSet candidatePast)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hnextCandidate : filteredSecondTransitionEvent stagedCandidate₁
      stagedCandidate₂ t m a ⊆ candidatePast)
    (hpast : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' secondCandidatePastAtom candidatePast
          stagedCandidate₁ t m a z)) :
    CountableMeshCreationData PairCreationIndex candidatePast
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) m 2 a.1.2 where
  oldCreation := Prod.snd
  pastPiece := secondCandidatePastAtom candidatePast stagedCandidate₁ t m a
  nextPiece := noLazyFilteredSecondTransitionAtom stagedCandidate₁
    stagedCandidate₂ t m a
  past_pairwise := by
    intro z w hzw
    exact (pairCreationAtom_pairwiseDisjoint t m a hzw).mono
      (inter_subset_left.trans inter_subset_left)
      (inter_subset_left.trans inter_subset_left)
  past_measurable := fun z ↦
    ((measurableSet_pairCreationAtom t m a z).inter
      (measurableSet_filteredFirstTransitionEvent stagedCandidate₁
        t m a hcandidate₁)).inter hcandidatePast
  next_measurable := fun z ↦
    (measurableSet_filteredSecondTransitionEvent stagedCandidate₁
      stagedCandidate₂ t m a hcandidate₁ hcandidate₂).inter
        (measurableSet_pairCreationAtom t m a z)
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
    exact hz.2
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
      exact hz.1
    · intro s hs
      have hfirst := filteredSecondTransitionEvent_subset_filteredFirst
        stagedCandidate₁ stagedCandidate₂ t m a hs
      have hatom : s ∈ ⋃ z : PairCreationIndex,
          pairCreationAtom t m a z := by
        rw [iUnion_pairCreationAtom t m a]
        exact hfirst.1
      rcases Set.mem_iUnion.mp hatom with ⟨z, hz⟩
      exact Set.mem_iUnion.mpr ⟨z, hs, hz⟩
  atom := fun z ↦ secondMeshCreationAtomData candidatePast stagedCandidate₁
    stagedCandidate₂ t m a z hproper hnextCandidate (hpast z)

noncomputable def thirdCountableMeshCreationData
    (candidatePast : Set WalkPath)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hproper : a.2 ∈ properGapMesh)
    (hcandidatePast : MeasurableSet candidatePast)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hnextCandidate : filteredThirdTransitionEvent stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a ⊆ candidatePast)
    (hpast : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' thirdCandidatePastAtom candidatePast stagedCandidate₁
          stagedCandidate₂ t m a z)) :
    CountableMeshCreationData TripleCreationIndex candidatePast
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) m 3 a.2 where
  oldCreation := Prod.snd
  pastPiece := thirdCandidatePastAtom candidatePast stagedCandidate₁
    stagedCandidate₂ t m a
  nextPiece := noLazyFilteredThirdTransitionAtom stagedCandidate₁
    stagedCandidate₂ stagedCandidate₃ t m a
  past_pairwise := by
    intro z w hzw
    exact (tripleCreationAtom_pairwiseDisjoint t m a hzw).mono
      (inter_subset_left.trans inter_subset_left)
      (inter_subset_left.trans inter_subset_left)
  past_measurable := fun z ↦
    ((measurableSet_tripleCreationAtom t m a z).inter
      (measurableSet_filteredSecondTransitionEvent stagedCandidate₁
        stagedCandidate₂ t m a hcandidate₁ hcandidate₂)).inter
      hcandidatePast
  next_measurable := fun z ↦
    (measurableSet_filteredThirdTransitionEvent stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a hcandidate₁ hcandidate₂
        hcandidate₃).inter (measurableSet_tripleCreationAtom t m a z)
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
    exact hz.2
  next_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨z, hz⟩
      exact hz.1
    · intro s hs
      have hsecond := filteredThirdTransitionEvent_subset_filteredSecond
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hs
      have hatom : s ∈ ⋃ z : TripleCreationIndex,
          tripleCreationAtom t m a z := by
        rw [iUnion_tripleCreationAtom t m a]
        exact hsecond.1
      rcases Set.mem_iUnion.mp hatom with ⟨z, hz⟩
      exact Set.mem_iUnion.mpr ⟨z, hs, hz⟩
  atom := fun z ↦ thirdMeshCreationAtomData candidatePast stagedCandidate₁
    stagedCandidate₂ stagedCandidate₃ t m a z hproper hnextCandidate
      (hpast z)

end

end Erdos1165.HLOZNoLazyMeshCandidateCreation
