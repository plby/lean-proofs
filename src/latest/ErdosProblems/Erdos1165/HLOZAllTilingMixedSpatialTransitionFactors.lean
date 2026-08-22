/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllTilingDominantStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZHighSpatialTransitionFactor

/-!
# Mixed high/low factors with both dominant spatial sources

The low branch in this module is the joint canonical/opposite construction:
one stopped history records both normalized `J / 4` candidate sets, and the
opposite narrow screen is the literal checker-shift or column-reflection
pullback.  The old raw-band stopped family is not used.

Each mesh coordinate is selected independently.  High coordinates use the
countable fixed-creation strong-Markov factor, while low coordinates use the
joint conditional coordinate product followed by an atomwise future escape.
No transition probability inequality is an input.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZAllTilingMixedSpatialTransitionFactors

open HLOZAllTilingDominantStoppedCandidateFamily
open HLOZFilteredPastObservability HLOZHighSpatialTransitionFactor
open HLOZHeterogeneousFilteredTransitionFactors HLOZPathEvents
open HLOZSourceCorrectFilteredTransitions HLOZSourceCorrectFutureTransition
open HLOZSpatialAdapter HLOZStoppedHistoryCandidateFuture
open TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-! ## Whole-source low data -/

/-- Concrete data for one low coordinate.  The deterministic field is the
joint all-tiling dominant conditional product.  The only later input is the
countable-atom escape factor, so this structure contains no estimate for the
target transition event. -/
structure AllTilingDominantLowTransitionData
    (t : DominoTiling) (m k : ℕ)
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  Index : Type
  State : Type
  [index_countable : Countable Index]
  [state_countable : Countable State]
  candidateRatio : ℝ≥0∞
  escapeCost : ℝ≥0∞
  coordinate : CandidateBudgetAllTilingDominantLowConditionalData
    t m k previous candidateRatio
  escape : CountableAtomFutureFactor Index State
    coordinate.family.someCandidate next escapeCost
  cost_le :
    (((coordinate.sourceBudget + coordinate.sourceBudget : ℕ) : ℝ≥0∞) *
      candidateRatio * escapeCost) ≤ q

namespace AllTilingDominantLowTransitionData

/-- Invoke the corrected joint `.lowAtomwise` constructor and hide its
rank-specific history and future-state carriers. -/
noncomputable def factor
    {t : DominoTiling} {m k : ℕ}
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (data : AllTilingDominantLowTransitionData
      t m k previous next q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q := by
  letI := data.index_countable
  letI := data.state_countable
  exact data.coordinate.factor data.escape data.cost_le

end AllTilingDominantLowTransitionData

/-! ## Rankwise high/low selection -/

/-- Triple-mesh membership projected without evaluating the concrete proper
mesh decision procedure. -/
theorem mem_meshTriples_components
    {mesh : Finset GapScale} {a : GapTriple}
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    a.1.1 ∈ mesh ∧ a.1.2 ∈ mesh ∧ a.2 ∈ mesh := by
  have h := Finset.mem_product.mp (Finset.mem_product.mp ha).1
  exact ⟨h.1, h.2, (Finset.mem_product.mp ha).2⟩

/-- Select the corrected all-tiling low factor or the literal high factor at
rank one. -/
noncomputable def firstAllTilingMixedSourceCorrectTransitionFactor
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (low : a.1.1 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor Set.univ
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.1.1 ∈ highGapMesh
  · exact .of (filteredFirstHighSourceCorrectTransitionFactor cap
      stagedCandidate₁ K t m a hm hhigh hcandidate₁ hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-- Rank-two selector.  Structural stopped observability is derived by
`HLOZFilteredPastObservability`; only the fixed pair atom intersected with
the staged candidate remains as an input. -/
noncomputable def secondAllTilingMixedSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (low : a.1.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.1.2 ∈ highGapMesh
  · exact .of (filteredSecondHighSourceCorrectTransitionFactor cap
      stagedCandidate₁ stagedCandidate₂ K t m a hm hhigh hcandidate₁
      hcandidate₂
      (fun z ↦ filteredFirstPairCreationAtom_observable cap stagedCandidate₁
        t m a z (hstaged₁ z)) hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-- Rank-three selector with the two exact staged-candidate observability
families needed at a fixed triple creation clock. -/
noncomputable def thirdAllTilingMixedSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.2 ∈ properGapMesh)
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
        UpperCanonical.hlozTransitionCost K m)
    (low : a.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.2 ∈ highGapMesh
  · exact .of (filteredThirdHighSourceCorrectTransitionFactor cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm hhigh
      hcandidate₁ hcandidate₂ hcandidate₃
      (fun z ↦ filteredSecondTripleCreationAtom_observable cap
        stagedCandidate₁ stagedCandidate₂ t m a z (hstaged₁ z) (hstaged₂ z))
      hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-! ## One branch and an eventual mesh package -/

/-- Assemble the three independently selected corrected factors. -/
noncomputable def allTilingMixedFilteredBranchTransitionFactorPackage
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m)
    (hproper₁ : a.1.1 ∈ properGapMesh)
    (hproper₂ : a.1.2 ∈ properGapMesh)
    (hproper₃ : a.2 ∈ properGapMesh)
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
        UpperCanonical.hlozTransitionCost K m)
    (low₁ : a.1.1 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₂ : a.1.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₃ : a.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a :=
  { stagedCandidate₁_measurable := hcandidate₁
    stagedCandidate₂_measurable := hcandidate₂
    stagedCandidate₃_measurable := hcandidate₃
    firstPast := Set.univ
    firstPast_measurable := MeasurableSet.univ
    first_next_subset_past := subset_univ _
    firstPast_measure_le_one := by simp
    firstFactor := firstAllTilingMixedSourceCorrectTransitionFactor cap
      stagedCandidate₁ K t m a hm hproper₁ hcandidate₁ hcost low₁
    secondFactor := secondAllTilingMixedSourceCorrectTransitionFactor cap
      stagedCandidate₁ stagedCandidate₂ K t m a hm hproper₂ hcandidate₁
      hcandidate₂ hstagedPair₁ hcost low₂
    thirdFactor := thirdAllTilingMixedSourceCorrectTransitionFactor cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm hproper₃
      hcandidate₁ hcandidate₂ hcandidate₃ hstagedTriple₁ hstagedTriple₂
      hcost low₃ }

/-- Eventual concrete low data over the finite proper mesh.  It stores only
joint conditional coordinate products, atomwise future escapes, and their
explicit numerical cost comparisons. -/
structure PositiveLevelAllTilingDominantLowTransitionData
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh →
    a.1.1 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh →
    a.1.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh →
    a.2 ∈ lowGapMesh →
      AllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)

/-- Combine eventual concrete low data with the premise-free high escape
envelope.  The three ordinary and three stopped measurability families are
expected to come from the concrete raw staged-candidate promotion layer. -/
noncomputable def positiveLevelAllTilingMixedTransitionFactorPackage
    (mesh : Finset GapScale)
    (hmesh : ∀ b ∈ mesh, b ∈ properGapMesh)
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (data : PositiveLevelAllTilingDominantLowTransitionData cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (costStart : ℕ)
    (hcost : ∀ m, costStart ≤ m → ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (hcandidate₁ : ∀ m a,
      MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : ∀ m a,
      MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : ∀ m a,
      MeasurableSet (stagedCandidate₃ t m a))
    (hstagedPair₁ : ∀ m a (z : PairCreationIndex),
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstagedTriple₁ : ∀ m a (z : TripleCreationIndex),
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hstagedTriple₂ : ∀ m a (z : TripleCreationIndex),
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (tripleCreationAtom t m a z ∩
          stagedCandidate₂ t m a))) :
    PositiveLevelHeterogeneousTransitionFactorPackage mesh cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t where
  levelStart := max data.levelStart costStart
  levelStart_pos := data.levelStart_pos.trans_le
    (Nat.le_max_left data.levelStart costStart)
  branch := by
    intro m hm a ha
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart costStart).trans hm
    have hmCost : costStart ≤ m :=
      (Nat.le_max_right data.levelStart costStart).trans hm
    have hmOne : 1 ≤ m := data.levelStart_pos.trans_le hmData
    obtain ⟨ha₁Mesh, ha₂Mesh, ha₃Mesh⟩ :=
      mem_meshTriples_components (mesh := mesh) ha
    have ha₁ := hmesh a.1.1 ha₁Mesh
    have ha₂ := hmesh a.1.2 ha₂Mesh
    have ha₃ := hmesh a.2 ha₃Mesh
    exact allTilingMixedFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hmOne
      ha₁ ha₂ ha₃ (hcandidate₁ m a) (hcandidate₂ m a)
      (hcandidate₃ m a) (hstagedPair₁ m a) (hstagedTriple₁ m a)
      (hstagedTriple₂ m a) (hcost m hmCost)
      (data.first m hmData a ha₁) (data.second m hmData a ha₂)
      (data.third m hmData a ha₃)

end

end Erdos1165.HLOZAllTilingMixedSpatialTransitionFactors
