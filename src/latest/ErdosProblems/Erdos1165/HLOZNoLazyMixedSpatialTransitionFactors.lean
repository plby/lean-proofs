/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllTilingDominantStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZNoLazyHighSpatialTransitionFactor
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion

/-!
# Mixed high/low factors for the candidate-local no-lazy chain

Every mesh coordinate is selected independently.  High coordinates use the
countable fixed-creation boundary-escape factor.  Low coordinates use the
joint canonical/opposite dominant stopped-candidate product followed by an
atomwise future escape.  Both branches target the events in
`HLOZNoLazyFilteredTransitions`; no global or away-lazy event occurs here.

The raw specialization derives ordinary measurability and all three
old-clock observability families from `HLOZRawFullGapProductPromotion`.
Those facts are consequently not public premises of the preferred package
constructor.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZNoLazyMixedSpatialTransitionFactors

open HLOZAllTilingDominantStoppedCandidateFamily
open HLOZHighSpatialTransitionFactor HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyFilteredTransitions HLOZPathEvents
open HLOZRawFullGapProductPromotion
open HLOZSourceCorrectFutureTransition HLOZSpatialAdapter
open HLOZStoppedHistoryCandidateFuture TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## Corrected whole-source low data -/

/-- Literal low-coordinate data for one no-lazy transition.

The stopped history simultaneously records the canonical and transported
opposite dominant candidate sets.  The target-event estimate is not a
field: it is derived by the conditional coordinate product and the
countable-atom future escape. -/
structure NoLazyAllTilingDominantLowTransitionData
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

namespace NoLazyAllTilingDominantLowTransitionData

/-- Invoke the literal joint `.lowAtomwise` construction and hide its
rank-specific stopped-history and future-state carriers. -/
noncomputable def factor
    {t : DominoTiling} {m k : ℕ}
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (data : NoLazyAllTilingDominantLowTransitionData
      t m k previous next q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q := by
  letI := data.index_countable
  letI := data.state_countable
  exact .of (data.coordinate.data.factor data.escape data.cost_le)

end NoLazyAllTilingDominantLowTransitionData

/-! ## Rankwise mixed selection -/

/-- Project membership in the product mesh without evaluating the concrete
proper-mesh decision procedure. -/
theorem mem_meshTriples_components
    {mesh : Finset GapScale} {a : GapTriple}
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    a.1.1 ∈ mesh ∧ a.1.2 ∈ mesh ∧ a.2 ∈ mesh := by
  have h := Finset.mem_product.mp (Finset.mem_product.mp ha).1
  exact ⟨h.1, h.2, (Finset.mem_product.mp ha).2⟩

/-- Select the literal high or corrected all-tiling dominant low factor at
rank one. -/
noncomputable def firstNoLazyMixedSourceCorrectTransitionFactor
    (stagedCandidate₁ : BranchEvent) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (low : a.1.1 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.1.1 ∈ highGapMesh
  · exact .of (noLazyFilteredFirstHighSourceCorrectTransitionFactor
      stagedCandidate₁ K t m a hm hhigh hcandidate₁ hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-- Rank-two selector.  The high branch derives filtered-past observability
from the fixed pair atom intersected with the raw staged candidate. -/
noncomputable def secondNoLazyMixedSourceCorrectTransitionFactor
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
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
      NoLazyAllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.1.2 ∈ highGapMesh
  · exact .of (noLazyFilteredSecondHighSourceCorrectTransitionFactor
      stagedCandidate₁ stagedCandidate₂ K t m a hm hhigh hcandidate₁
        hcandidate₂ hstaged₁ hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-- Rank-three selector, with precisely the two raw staged-candidate
observability families needed at a fixed triple creation clock. -/
noncomputable def thirdNoLazyMixedSourceCorrectTransitionFactor
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
      NoLazyAllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.2 ∈ highGapMesh
  · exact .of (noLazyFilteredThirdHighSourceCorrectTransitionFactor
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm hhigh
        hcandidate₁ hcandidate₂ hcandidate₃ hstaged₁ hstaged₂ hcost)
  · exact (low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)).factor

/-! ## Branch and eventual packages -/

/-- Assemble three independently selected no-lazy factors. -/
noncomputable def noLazyMixedFilteredBranchTransitionFactorPackage
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
      NoLazyAllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₂ : a.1.2 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₃ : a.2 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    NoLazyFilteredBranchTransitionFactorPackage stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ K t m a where
  stagedCandidate₁_measurable := hcandidate₁
  stagedCandidate₂_measurable := hcandidate₂
  stagedCandidate₃_measurable := hcandidate₃
  firstPast := Set.univ
  firstPast_measurable := MeasurableSet.univ
  firstFactor := firstNoLazyMixedSourceCorrectTransitionFactor
    stagedCandidate₁ K t m a hm hproper₁ hcandidate₁ hcost low₁
  secondFactor := secondNoLazyMixedSourceCorrectTransitionFactor
    stagedCandidate₁ stagedCandidate₂ K t m a hm hproper₂ hcandidate₁
      hcandidate₂ hstagedPair₁ hcost low₂
  thirdFactor := thirdNoLazyMixedSourceCorrectTransitionFactor
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm hproper₃
      hcandidate₁ hcandidate₂ hcandidate₃ hstagedTriple₁ hstagedTriple₂
      hcost low₃

/-- Eventual low-coordinate data over a finite proper mesh.  It stores only
literal joint conditional products, atomwise future escapes, and explicit
cost comparisons. -/
structure PositiveLevelNoLazyAllTilingDominantLowTransitionData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh → a.1.1 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh → a.1.2 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 2
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh → a.2 ∈ lowGapMesh →
      NoLazyAllTilingDominantLowTransitionData t m 3
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)

/-- Generic eventual mixed package.  This remains useful for testing other
staged families; the raw specialization below removes all measurability and
old-clock premises. -/
noncomputable def positiveLevelNoLazyMixedTransitionFactorPackage
    (mesh : Finset GapScale)
    (hmesh : ∀ b ∈ mesh, b ∈ properGapMesh)
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (data : PositiveLevelNoLazyAllTilingDominantLowTransitionData
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
    PositiveLevelNoLazyHeterogeneousTransitionFactorPackage mesh
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
    exact noLazyMixedFilteredBranchTransitionFactorPackage
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hmOne
      ha₁ ha₂ ha₃ (hcandidate₁ m a) (hcandidate₂ m a)
      (hcandidate₃ m a) (hstagedPair₁ m a) (hstagedTriple₁ m a)
      (hstagedTriple₂ m a) (hcost m hmCost)
      (data.first m hmData a ha₁) (data.second m hmData a ha₂)
      (data.third m hmData a ha₃)

/-! ## Raw staged-candidate specialization -/

/-- Preferred mixed package for the honest raw staged candidates.  Their
ordinary and stopped measurability are derived internally, as is the
eventual high-spatial escape envelope. -/
noncomputable def rawNoLazyMixedTransitionFactorPackage
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (mesh : Finset GapScale)
    (hmesh : ∀ b ∈ mesh, b ∈ properGapMesh)
    {K : ℝ≥0} (hK : 1 ≤ K) (t : DominoTiling)
    (data : PositiveLevelNoLazyAllTilingDominantLowTransitionData
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) K t) :
    PositiveLevelNoLazyHeterogeneousTransitionFactorPackage mesh
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) K t := by
  have hevent :=
    eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost_of_one_le
      K hK
  rw [eventually_atTop] at hevent
  let costStart := Classical.choose hevent
  have hcost := Classical.choose_spec hevent
  exact positiveLevelNoLazyMixedTransitionFactorPackage mesh hmesh data
    costStart hcost
    (measurableSet_firstRawStagedCandidate product t)
    (measurableSet_secondRawStagedCandidate product t)
    (measurableSet_thirdRawStagedCandidate product t)
    (pairCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_secondRawStagedCandidate_observable product t)

/-- Final-mesh specialization with the common transition constant `K = 1`.
The proper-mesh membership and numerical lower bound on `K` are discharged
definitionally, so the only remaining input is the literal low-coordinate
construction. -/
noncomputable def rawProperNoLazyMixedTransitionFactorPackage
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (data : PositiveLevelNoLazyAllTilingDominantLowTransitionData
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1 t) :
    PositiveLevelNoLazyHeterogeneousTransitionFactorPackage properGapMesh
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1 t :=
  rawNoLazyMixedTransitionFactorPackage product properGapMesh
    (fun _ hb ↦ hb) (by norm_num) t data

/-- All six tilings at once.  This is the factor family consumed by the
direct-series endgame; the public upper assembly obtains `data` from the
literal all-creation broad/narrow constructor. -/
noncomputable def rawProperNoLazyMixedTransitionFactorPackages
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (data : ∀ t : DominoTiling,
      PositiveLevelNoLazyAllTilingDominantLowTransitionData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) 1 t) :
    ∀ t : DominoTiling,
      PositiveLevelNoLazyHeterogeneousTransitionFactorPackage properGapMesh
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) 1 t :=
  fun t ↦ rawProperNoLazyMixedTransitionFactorPackage product t (data t)

end

end Erdos1165.HLOZNoLazyMixedSpatialTransitionFactors
