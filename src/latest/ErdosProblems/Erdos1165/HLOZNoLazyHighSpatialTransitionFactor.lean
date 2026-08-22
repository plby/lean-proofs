/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZHighSpatialTransitionFactor
import ErdosProblems.Erdos1165.HLOZNoLazyFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZNoLazyHeterogeneousTransitionFactors

/-!
# High-spatial factors for the no-lazy filtered chain

This adapter reuses the literal boundary-escape theorem from
`HLOZHighSpatialTransitionFactor`, but its countable stopped atoms target the
final candidate-local filters in `HLOZNoLazyFilteredTransitions`.  The only
old-clock inputs are the exact staged-candidate atom observability families
consumed by `HLOZNoLazyFilteredPastObservability`.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZNoLazyHighSpatialTransitionFactor

open HLOZFilteredTransitionAssembly HLOZHighSpatialTransitionFactor
open HLOZNoLazyFilteredPastObservability
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyFilteredTransitions HLOZPathEvents HLOZSpatialAdapter
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open StoppedInsertion TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## Fixed no-lazy creation atoms -/

/-- First no-lazy filtered transition with its rank-one creation time fixed. -/
def noLazyFilteredFirstTransitionAtom
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) (nOld : ℕ) : Set WalkPath :=
  filteredFirstTransitionEvent stagedCandidate₁ t m a ∩
    firstCreationAtom m nOld

/-- Rank-two stopped past, with the pair atom written first to match the
frozen no-lazy observability API literally. -/
def noLazyFilteredFirstPairCreationAtom
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) (z : PairCreationIndex) : Set WalkPath :=
  pairCreationAtom t m a z ∩
    filteredFirstTransitionEvent stagedCandidate₁ t m a

/-- Rank-two no-lazy next piece. -/
def noLazyFilteredSecondTransitionAtom
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) : Set WalkPath :=
  filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
      t m a ∩ pairCreationAtom t m a z

/-- Rank-three stopped past. -/
def noLazyFilteredSecondTripleCreationAtom
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) : Set WalkPath :=
  tripleCreationAtom t m a z ∩
    filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
      t m a

/-- Rank-three no-lazy next piece. -/
def noLazyFilteredThirdTransitionAtom
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) : Set WalkPath :=
  filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ t m a ∩ tripleCreationAtom t m a z

/-! ## Deterministic high-gap data -/

theorem noLazyFilteredFirstHighCreationAtomData
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) (nOld : ℕ) (ha : a.1.1 ∈ highGapMesh) :
    HighCreationAtomData (firstCreationAtom m nOld)
      (noLazyFilteredFirstTransitionAtom stagedCandidate₁ t m a nOld)
      m 1 nOld a.1.1 where
  rank_pos := by omega
  high_scale := ha
  past_observable := by
    change IsMeasurableAtStopping (fun _ : StepPath => nOld)
      {omega | ThresholdCreation (trajectory omega) m 1 nOld}
    apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
    exact measurableSet_trajectory_thresholdCreation_filtration m 1 nOld
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
    exact ⟨holdAtom, n₂, hpair.1, hpair.2.1, hpair.2.2.1,
      hpair.2.2.2.2⟩

theorem noLazyFilteredSecondHighCreationAtomData
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : PairCreationIndex) (ha : a.1.2 ∈ highGapMesh)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath => z.2)
      (trajectory ⁻¹' noLazyFilteredFirstPairCreationAtom
        stagedCandidate₁ t m a z)) :
    HighCreationAtomData
      (noLazyFilteredFirstPairCreationAtom stagedCandidate₁ t m a z)
      (noLazyFilteredSecondTransitionAtom stagedCandidate₁ stagedCandidate₂
        t m a z) m 2 z.2 a.1.2 where
  rank_pos := by omega
  high_scale := ha
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, hpairAtom⟩
    have hpastFiltered := filteredSecondTransitionEvent_subset_filteredFirst
      stagedCandidate₁ stagedCandidate₂ t m a hfiltered
    have hpast : trajectory omega ∈
        noLazyFilteredFirstPairCreationAtom stagedCandidate₁ t m a z :=
      ⟨hpairAtom, hpastFiltered⟩
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
    exact ⟨hpast, n₃, htriple.2.1, htriple.2.2.1,
      htriple.2.2.2.1, htriple.2.2.2.2.2.2.2.2⟩

theorem noLazyFilteredThirdHighCreationAtomData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (z : TripleCreationIndex) (ha : a.2 ∈ highGapMesh)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath => z.2)
      (trajectory ⁻¹' noLazyFilteredSecondTripleCreationAtom
        stagedCandidate₁ stagedCandidate₂ t m a z)) :
    HighCreationAtomData
      (noLazyFilteredSecondTripleCreationAtom stagedCandidate₁ stagedCandidate₂
        t m a z)
      (noLazyFilteredThirdTransitionAtom stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a z) m 3 z.2 a.2 where
  rank_pos := by omega
  high_scale := ha
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases homega with ⟨hfiltered, htripleAtom⟩
    have hpastFiltered := filteredThirdTransitionEvent_subset_filteredSecond
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hfiltered
    have hpast : trajectory omega ∈
        noLazyFilteredSecondTripleCreationAtom stagedCandidate₁ stagedCandidate₂
          t m a z := ⟨htripleAtom, hpastFiltered⟩
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
    exact ⟨hpast, n₄, hquad.2.2.1, hquad.2.2.2.1,
      hquad.2.2.2.2.1, hquad.2.2.2.2.2.2.2.2⟩

/-! ## Countable-atom escape factors -/

def noLazyFilteredFirstHighCountableAtomFutureFactor
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (a : GapTriple) (hm : 1 ≤ m) (ha : a.1.1 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a)) :
    CountableAtomFutureFactor ℕ Unit Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := firstCreationAtom m
  nextPiece := noLazyFilteredFirstTransitionAtom stagedCandidate₁ t m a
  past_pairwise := firstCreationAtom_pairwiseDisjoint m
  past_measurable := measurableSet_firstCreationAtom m
  next_measurable := fun n ↦
    (measurableSet_filteredFirstTransitionEvent stagedCandidate₁
      t m a hcandidate₁).inter (measurableSet_firstCreationAtom m n)
  past_subset := fun _ _ ↦ Set.mem_univ _
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
  atom := fun n ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (noLazyFilteredFirstHighCreationAtomData stagedCandidate₁
        t m a n ha)

def noLazyFilteredSecondHighCountableAtomFutureFactor
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (ha : a.1.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a))) :
    CountableAtomFutureFactor PairCreationIndex Unit
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := noLazyFilteredFirstPairCreationAtom stagedCandidate₁ t m a
  nextPiece := noLazyFilteredSecondTransitionAtom stagedCandidate₁
    stagedCandidate₂ t m a
  past_pairwise := by
    intro z w hzw
    exact (pairCreationAtom_pairwiseDisjoint t m a hzw).mono
      Set.inter_subset_left Set.inter_subset_left
  past_measurable := fun z ↦
    (measurableSet_pairCreationAtom t m a z).inter
      (measurableSet_filteredFirstTransitionEvent stagedCandidate₁
        t m a hcandidate₁)
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
  atom := fun z ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (noLazyFilteredSecondHighCreationAtomData stagedCandidate₁
        stagedCandidate₂ t m a z ha
          (pairCreationAtom_inter_filteredFirstTransitionEvent_observable
            stagedCandidate₁ t m a z (hstaged₁ z)))

def noLazyFilteredThirdHighCountableAtomFutureFactor
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (ha : a.2 ∈ highGapMesh)
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
    CountableAtomFutureFactor TripleCreationIndex Unit
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (ENNReal.ofReal
        (literalEscapeProbability (highSpatialRadius m))) where
  pastPiece := noLazyFilteredSecondTripleCreationAtom stagedCandidate₁
    stagedCandidate₂ t m a
  nextPiece := noLazyFilteredThirdTransitionAtom stagedCandidate₁
    stagedCandidate₂ stagedCandidate₃ t m a
  past_pairwise := by
    intro z w hzw
    exact (tripleCreationAtom_pairwiseDisjoint t m a hzw).mono
      Set.inter_subset_left Set.inter_subset_left
  past_measurable := fun z ↦
    (measurableSet_tripleCreationAtom t m a z).inter
      (measurableSet_filteredSecondTransitionEvent stagedCandidate₁
        stagedCandidate₂ t m a hcandidate₁ hcandidate₂)
  next_measurable := fun z ↦
    (measurableSet_filteredThirdTransitionEvent stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a hcandidate₁
        hcandidate₂ hcandidate₃).inter
      (measurableSet_tripleCreationAtom t m a z)
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
  atom := fun z ↦
    highCreationAtomBoundaryEscapeCertificate hm
      (noLazyFilteredThirdHighCreationAtomData stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a z ha
          (tripleCreationAtom_inter_filteredSecondTransitionEvent_observable
            stagedCandidate₁ stagedCandidate₂ t m a z
              (hstaged₁ z) (hstaged₂ z)))

/-! ## Whole-event source-correct constructors -/

def noLazyFilteredFirstHighSourceCorrectTransitionFactor
    (stagedCandidate₁ : BranchEvent) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (ha : a.1.1 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (noLazyFilteredFirstHighCountableAtomFutureFactor stagedCandidate₁
      t m a hm ha hcandidate₁) hcost

def noLazyFilteredSecondHighSourceCorrectTransitionFactor
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (ha : a.1.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (noLazyFilteredSecondHighCountableAtomFutureFactor stagedCandidate₁
      stagedCandidate₂ t m a hm ha hcandidate₁ hcandidate₂ hstaged₁)
    hcost

def noLazyFilteredThirdHighSourceCorrectTransitionFactor
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (ha : a.2 ∈ highGapMesh)
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
          stagedCandidate₂ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    SourceCorrectTransitionFactor Unit Unit Unit
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m) :=
  .highAtomwise _
    (noLazyFilteredThirdHighCountableAtomFutureFactor stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a hm ha hcandidate₁
        hcandidate₂ hcandidate₃ hstaged₁ hstaged₂) hcost

/-! ## All-high no-lazy branch package -/

def noLazyAllHighFilteredBranchTransitionFactorPackage
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m)
    (ha₁ : a.1.1 ∈ highGapMesh) (ha₂ : a.1.2 ∈ highGapMesh)
    (ha₃ : a.2 ∈ highGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (hstagedPair₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstagedTriple₁ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstagedTriple₂ : ∀ z : TripleCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₂ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m) :
    NoLazyFilteredBranchTransitionFactorPackage stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ K t m a :=
  noLazyFilteredBranchTransitionFactorPackageOfFactors
    hcandidate₁ hcandidate₂ hcandidate₃ Set.univ MeasurableSet.univ
    (noLazyFilteredFirstHighSourceCorrectTransitionFactor stagedCandidate₁
      K t m a hm ha₁ hcandidate₁ hcost)
    (noLazyFilteredSecondHighSourceCorrectTransitionFactor stagedCandidate₁
      stagedCandidate₂ K t m a hm ha₂ hcandidate₁ hcandidate₂
        hstagedPair₁ hcost)
    (noLazyFilteredThirdHighSourceCorrectTransitionFactor stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ K t m a hm ha₃ hcandidate₁
        hcandidate₂ hcandidate₃ hstagedTriple₁ hstagedTriple₂ hcost)

end

end Erdos1165.HLOZNoLazyHighSpatialTransitionFactor
