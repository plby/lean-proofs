/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFiniteSourceRowMeshLowTransition
import ErdosProblems.Erdos1165.HLOZNoLazyDirectSeriesEndgame
import ErdosProblems.Erdos1165.HLOZNoLazyFullGapSeriesAssembly
import ErdosProblems.Erdos1165.HLOZNoLazyHighSpatialTransitionFactor

/-!
# No-lazy upper assembly with finite overlapping source rows

The canonical and transported Proposition 4.9 source rows need not be
disjoint as stopped histories.  This module therefore replaces the old
single-family low input by a finite row union.  Every row carries its own
literal stopped-candidate and future-escape factor; only the deterministic
sum of row ratios is compared with the common polynomial envelope.

The assembly is independent of the temporary full-beta product carrier.  It
accepts the three staged events directly and leaves their concrete
source/Theta construction to the final source module.  No lazy event,
transition-probability inequality, legacy gap interface, or obsolete product
carrier occurs here.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZNoLazyFiniteSourceRowUpperAssembly

open HLOZFilteredTransitionAssembly
open HLOZFiniteSourceRowMeshLowTransition
open HLOZFiniteSourceRowTransitionFactors
open HLOZHighSpatialTransitionFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyDirectSeriesEndgame
open HLOZNoLazyFilteredTransitions
open HLOZNoLazyFullBetaProductBranch HLOZNoLazyFullGapSeriesAssembly
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPathEvents HLOZPositiveLevelFilteredTransitionAssembly
open HLOZProposition48Candidates HLOZSpatialAdapter
open HLOZRawFullGapProductPromotion HLOZSourceCorrectFullGapClosure
open TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## Hidden finite row carriers -/

/-- Finite-row mesh data with its row type hidden. -/
structure HeterogeneousFiniteSourceRowMeshLowCoordinateData
    (C : ℝ) (m rank : ℕ) (a : GapScale)
    (previous next : Set WalkPath) where
  Row : Type
  [row_fintype : Fintype Row]
  data : FiniteSourceRowMeshLowCoordinateData
    Row C m rank a previous next

namespace HeterogeneousFiniteSourceRowMeshLowCoordinateData

/-- Close the polynomial numeric inequality after hiding the row carrier. -/
noncomputable def transitionFactor
    {C : ℝ} {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath}
    (data : HeterogeneousFiniteSourceRowMeshLowCoordinateData
      C m rank a previous next)
    (hm : 1 ≤ m)
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope C m a *
        HLOZMeshCandidateFutureFactor.meshEscapeCost m a ≤
      UpperCanonical.hlozTransitionCost 1 m) :
    HeterogeneousFiniteSourceRowTransitionFactor previous next
      (UpperCanonical.hlozTransitionCost 1 m) := by
  letI := data.row_fintype
  exact data.data.transitionFactor hm hnumeric

end HeterogeneousFiniteSourceRowMeshLowCoordinateData

/-! ## Eventual low data and numerical closure -/

/-- Eventual finite-row factors after all low numerical comparisons have
been closed. -/
structure PositiveLevelNoLazyFiniteSourceRowLowTransitionData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh → a.1.1 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost 1 m)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh → a.1.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost 1 m)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh → a.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost 1 m)

/-- Literal finite-row mesh data before the common polynomial envelope is
absorbed.  The row types may differ at every rank, mesh cell, and level. -/
structure PositiveLevelNoLazyFiniteSourceRowMeshCreationData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) where
  C : ℝ
  C_nonneg : 0 ≤ C
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh → a.1.1 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowMeshLowCoordinateData C m 1 a.1.1 Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh → a.1.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowMeshLowCoordinateData C m 2 a.1.2
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh → a.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowMeshLowCoordinateData C m 3 a.2
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)

namespace PositiveLevelNoLazyFiniteSourceRowMeshCreationData

/-- Close the common polynomial inequality uniformly over the finite mesh. -/
noncomputable def toLowTransitionData
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyFiniteSourceRowMeshCreationData
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t) :
    PositiveLevelNoLazyFiniteSourceRowLowTransitionData
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t := by
  have heach : ∀ b ∈ properGapMesh, ∀ᶠ m : ℕ in atTop,
      (initialBudget48 m : ℝ≥0∞) *
          prop49CandidateRatioEnvelope data.C m b *
            HLOZMeshCandidateFutureFactor.meshEscapeCost m b ≤
        UpperCanonical.hlozTransitionCost 1 m := by
    intro b _hb
    exact
      eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
        data.C data.C_nonneg b
  have hall := (Finset.eventually_all properGapMesh).2 heach
  rw [eventually_atTop] at hall
  let numericStart := Classical.choose hall
  have hnumeric := Classical.choose_spec hall
  refine
    { levelStart := max data.levelStart numericStart
      levelStart_pos := data.levelStart_pos.trans_le
        (Nat.le_max_left data.levelStart numericStart)
      first := ?_
      second := ?_
      third := ?_ }
  · intro m hm a hproper _hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.first m hmData a hproper _hlow).transitionFactor
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.1.1 hproper)
  · intro m hm a hproper _hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.second m hmData a hproper _hlow).transitionFactor
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.1.2 hproper)
  · intro m hm a hproper _hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.third m hmData a hproper _hlow).transitionFactor
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.2 hproper)

end PositiveLevelNoLazyFiniteSourceRowMeshCreationData

/-! ## Mixed high/finite-row-low branches -/

noncomputable def firstMixedFactor
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling)
    (m : ℕ) (a : GapTriple) (hm : 1 ≤ m)
    (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m)
    (low : a.1.1 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost 1 m)) :
    HeterogeneousFiniteSourceRowTransitionFactor Set.univ
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost 1 m) := by
  by_cases hhigh : a.1.1 ∈ highGapMesh
  · apply HeterogeneousFiniteSourceRowTransitionFactor.ofFactor
      (measurableSet_filteredFirstTransitionEvent stagedCandidate₁ t m a
        hcandidate₁)
    exact .of (noLazyFilteredFirstHighSourceCorrectTransitionFactor
      stagedCandidate₁ 1 t m a hm hhigh hcandidate₁ hcost)
  · exact low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)

noncomputable def secondMixedFactor
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (hm : 1 ≤ m)
    (hproper : a.1.2 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hstaged₁ : ∀ z : PairCreationIndex,
      IsMeasurableAtStopping (fun _ : StepPath ↦ z.2)
        (trajectory ⁻¹' (pairCreationAtom t m a z ∩
          stagedCandidate₁ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m)
    (low : a.1.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost 1 m)) :
    HeterogeneousFiniteSourceRowTransitionFactor
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (UpperCanonical.hlozTransitionCost 1 m) := by
  by_cases hhigh : a.1.2 ∈ highGapMesh
  · apply HeterogeneousFiniteSourceRowTransitionFactor.ofFactor
      (measurableSet_filteredSecondTransitionEvent stagedCandidate₁
        stagedCandidate₂ t m a hcandidate₁ hcandidate₂)
    exact .of (noLazyFilteredSecondHighSourceCorrectTransitionFactor
      stagedCandidate₁ stagedCandidate₂ 1 t m a hm hhigh hcandidate₁
        hcandidate₂ hstaged₁ hcost)
  · exact low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)

noncomputable def thirdMixedFactor
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) (hm : 1 ≤ m)
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
          stagedCandidate₂ t m a)))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m)
    (low : a.2 ∈ lowGapMesh →
      HeterogeneousFiniteSourceRowTransitionFactor
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost 1 m)) :
    HeterogeneousFiniteSourceRowTransitionFactor
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost 1 m) := by
  by_cases hhigh : a.2 ∈ highGapMesh
  · apply HeterogeneousFiniteSourceRowTransitionFactor.ofFactor
      (measurableSet_filteredThirdTransitionEvent stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃ t m a hcandidate₁
          hcandidate₂ hcandidate₃)
    exact .of (noLazyFilteredThirdHighSourceCorrectTransitionFactor
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ 1 t m a hm
        hhigh hcandidate₁ hcandidate₂ hcandidate₃ hstaged₁ hstaged₂
        hcost)
  · exact low
      ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
        hhigh)

/-! ## Positive-level finite-row packages -/

/-- Eventual transition package using a finite row factor at every rank. -/
structure PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage
    (mesh : Finset GapScale)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  branch : ∀ m, levelStart ≤ m → ∀ a,
    a ∈ UpperAssembly.meshTriples mesh →
      FiniteSourceRowFilteredBranchPackage stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ 1 t m a

namespace PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage

theorem first_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage mesh
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (m : ℕ) (hm : data.levelStart ≤ m) (a : GapTriple)
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    simpleRandomWalk (filteredFirstTransitionEvent stagedCandidate₁ t m a) ≤
      UpperCanonical.hlozTransitionCost 1 m :=
  (data.branch m hm a ha).measure_estimates.1

theorem second_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage mesh
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (m : ℕ) (hm : data.levelStart ≤ m) (a : GapTriple)
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    simpleRandomWalk
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a) ≤
      UpperCanonical.hlozTransitionCost 1 m *
        simpleRandomWalk
          (filteredFirstTransitionEvent stagedCandidate₁ t m a) :=
  (data.branch m hm a ha).measure_estimates.2.1

theorem third_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage mesh
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (m : ℕ) (hm : data.levelStart ≤ m) (a : GapTriple)
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    simpleRandomWalk
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a) ≤
      UpperCanonical.hlozTransitionCost 1 m *
        simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m a) :=
  (data.branch m hm a ha).measure_estimates.2.2

end PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage

/-- Combine the literal finite-row low factors with the premise-free high
escape construction. -/
noncomputable def positiveLevelMixedPackage
    (mesh : Finset GapScale)
    (hmesh : ∀ b ∈ mesh, b ∈ properGapMesh)
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyFiniteSourceRowLowTransitionData
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (costStart : ℕ)
    (hcost : ∀ m, costStart ≤ m → ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m)
    (hcandidate₁ : ∀ m a, MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : ∀ m a, MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : ∀ m a, MeasurableSet (stagedCandidate₃ t m a))
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
    PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage mesh
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t where
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
    refine
      { stagedCandidate₁_measurable := hcandidate₁ m a
        stagedCandidate₂_measurable := hcandidate₂ m a
        stagedCandidate₃_measurable := hcandidate₃ m a
        firstPast := Set.univ
        firstPast_measurable := MeasurableSet.univ
        firstFactor := firstMixedFactor stagedCandidate₁ t m a hmOne ha₁
          (hcandidate₁ m a) (hcost m hmCost) (data.first m hmData a ha₁)
        secondFactor := secondMixedFactor stagedCandidate₁ stagedCandidate₂
          t m a hmOne ha₂ (hcandidate₁ m a) (hcandidate₂ m a)
          (hstagedPair₁ m a) (hcost m hmCost)
          (data.second m hmData a ha₂)
        thirdFactor := thirdMixedFactor stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a hmOne ha₃ (hcandidate₁ m a)
          (hcandidate₂ m a) (hcandidate₃ m a)
          (hstagedTriple₁ m a) (hstagedTriple₂ m a) (hcost m hmCost)
          (data.third m hmData a ha₃) }

/-! ## Corrected raw-product specialization -/

/-- The current cofinal all-tiling product contains only the positive-shell
interface law and its arithmetic thresholds.  Its shell-zero comparison is
the concrete actual-increment construction, so this adapter does not consume
the retired abstract fibre family. -/
noncomputable def rawProperMixedPackageOfMeshCreation
    (product : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (data : PositiveLevelNoLazyFiniteSourceRowMeshCreationData
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) t) :
    PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage properGapMesh
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) t := by
  have hevent :=
    eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost_of_one_le
      1 (by norm_num)
  rw [eventually_atTop] at hevent
  let costStart := Classical.choose hevent
  have hcost := Classical.choose_spec hevent
  exact positiveLevelMixedPackage properGapMesh (fun _ hb ↦ hb)
    data.toLowTransitionData costStart hcost
    (measurableSet_firstRawStagedCandidate product t)
    (measurableSet_secondRawStagedCandidate product t)
    (measurableSet_thirdRawStagedCandidate product t)
    (pairCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_secondRawStagedCandidate_observable product t)

/-! ## Carrier-independent final endgame -/

set_option linter.constructorNameAsVariable false in
/-- Direct-series no-lazy endgame for finite overlapping source rows. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_finiteRows
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (factors : ∀ t : DominoTiling,
      PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage properGapMesh
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion properGapMesh
        (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m)) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  let start : DominoTiling → ℕ := fun t ↦ (factors t).levelStart
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevel_filtered_estimates
      start 1
      (firstFactorBadHistory stagedCandidate₁)
      (secondFactorBadHistory stagedCandidate₂)
      (thirdFactorBadHistory stagedCandidate₃)
      (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃)
      (noLazy_terminalFilteredBadHistoryRouting stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃)
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodFirstTransitionEvent, if_pos hm]
    exact (factors t).first_measure_estimate m hm' a
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodSecondTransitionEvent, if_pos hm,
      tailGoodFirstTransitionEvent, if_pos hm]
    exact (factors t).second_measure_estimate m hm' a
  · intro t m a hm
    have hm' : (factors t).levelStart ≤ m := by
      simpa only [start] using hm
    rw [tailGoodThirdTransitionEvent, if_pos hm,
      tailGoodSecondTransitionEvent, if_pos hm]
    exact (factors t).third_measure_estimate m hm' a
  · exact hbase
  · exact hpaid

set_option linter.constructorNameAsVariable false in
/-- Rank-majorant form matching the concrete source/Theta decomposition. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_finiteRows_and_rank_majorants
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (factors : ∀ t : DominoTiling,
      PositiveLevelNoLazyFiniteSourceRowTransitionFactorPackage properGapMesh
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (hsubset₁ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₁ t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₂ t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        stagedCandidate₃ t m a ⊆ major₃ t m)
    (hmajor₁ : ∀ t, ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∀ t, ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∀ t, ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_finiteRows
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ factors hbase
  intro t
  exact candidatePaidBadHistoryEvent_series_ne_top_of_rank_majorants
    properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃
    major₁ major₂ major₃ t (hsubset₁ t) (hsubset₂ t) (hsubset₃ t)
      (hmajor₁ t) (hmajor₂ t) (hmajor₃ t)

/-! ## Current concrete source-series consumer -/

/-- Smallest upper wrapper over the corrected cofinal product and finite
overlapping Proposition 4.9 rows.

The remaining series arguments are precisely the outputs of the unfinished
source-Theta marginalization.  The HLOZ exceptional series, high transition
factors, low polynomial numerical comparison, and finite source-row union are
all constructed internally. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_correctedProduct
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (product : FullBetaSourceCorrectAllTilingProductData)
    (low : ∀ t : DominoTiling,
      PositiveLevelNoLazyFiniteSourceRowMeshCreationData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) t)
    (hbalance : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent
        product t m) ≠ ∞)
    (hsourceOne : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 1 m) ≠ ∞)
    (hsourceTwo : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 2 m) ≠ ∞)
    (hsourceThree : ∀ t, ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 3 m) ≠ ∞)
    (hcomplement : ∀ t, ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m
        (product.externalThreshold m)) ≠ ∞)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (hsubset₁ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        firstRawStagedCandidate product t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        secondRawStagedCandidate product t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ t m a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        thirdRawStagedCandidate product t m a ⊆ major₃ t m)
    (hmajor₁ : ∀ t, ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∀ t, ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∀ t, ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_finiteRows_and_rank_majorants
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product)
      (fun t ↦ rawProperMixedPackageOfMeshCreation product t (low t))
  · intro t
    exact
      simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_rank_source_series
        hmax product t (hbalance t) (hsourceOne t) (hsourceTwo t)
          (hsourceThree t) (hcomplement t)
  · exact hsubset₁
  · exact hsubset₂
  · exact hsubset₃
  · exact hmajor₁
  · exact hmajor₂
  · exact hmajor₃

/-! ## Exact source/Theta payment seam -/

/-- The five analytic series still owed by the concrete source/Theta and
positive-interface balance layers.

The three rank payments simultaneously majorize the oriented-source term in
the raw staged-candidate recurrence and the corresponding candidate-local
source term in the product-beta exceptional event.  Thus no arbitrary paid
event, transition estimate, or event-probability bound is exposed by the
final adapter below.  All remaining fields are deterministic containments
or the five exact summability conclusions produced by the balance and source
marginalizations. -/
structure CorrectedProductSourceThetaSeriesData
    (product : FullBetaSourceCorrectAllTilingProductData) where
  balance : DominoTiling → ℕ → Set WalkPath
  sourceOne : DominoTiling → ℕ → Set WalkPath
  sourceTwo : DominoTiling → ℕ → Set WalkPath
  sourceThree : DominoTiling → ℕ → Set WalkPath
  candidateLocalBalance_subset : ∀ t m,
    candidateLocalProductPositiveInterfaceBalanceRemainderEvent product t m ⊆
      balance t m
  candidateLocalOne_subset : ∀ t m,
    candidateLocalOrientedSourceEventAtRank product t 1 m ⊆ sourceOne t m
  candidateLocalTwo_subset : ∀ t m,
    candidateLocalOrientedSourceEventAtRank product t 2 m ⊆ sourceTwo t m
  candidateLocalThree_subset : ∀ t m,
    candidateLocalOrientedSourceEventAtRank product t 3 m ⊆ sourceThree t m
  firstRawBalance_subset : ∀ t m a,
    firstRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank product t 1 m ⊆
      balance t m
  secondRawBalance_subset : ∀ t m a,
    secondRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank product t 2 m ⊆
      balance t m
  thirdRawBalance_subset : ∀ t m a,
    thirdRawCandidatePreliminary t m a ∩
        positiveInterfaceBalanceRemainderUnionAtRank product t 3 m ⊆
      balance t m
  firstRawSource_subset : ∀ t m a,
    firstRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank product t 1 m ⊆
      sourceOne t m
  secondRawSource_subset : ∀ t m a,
    secondRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank product t 2 m ⊆
      sourceTwo t m
  thirdRawSource_subset : ∀ t m a,
    thirdRawCandidatePreliminary t m a ∩
        orientedCreationSourceOverflowUnionAtRank product t 3 m ⊆
      sourceThree t m
  balance_series : ∀ t, ∑' m, simpleRandomWalk (balance t m) ≠ ∞
  sourceOne_series : ∀ t, ∑' m, simpleRandomWalk (sourceOne t m) ≠ ∞
  sourceTwo_series : ∀ t, ∑' m, simpleRandomWalk (sourceTwo t m) ≠ ∞
  sourceThree_series : ∀ t, ∑' m, simpleRandomWalk (sourceThree t m) ≠ ∞
  complement_series : ∀ t, ∑' m, simpleRandomWalk
    (onTimeProductBetaCandidateLocalComplementEvent t m
      (product.externalThreshold m)) ≠ ∞

namespace CorrectedProductSourceThetaSeriesData

private theorem measure_union_series_ne_top
    {first second : ℕ → Set WalkPath}
    (hfirst : ∑' m, simpleRandomWalk (first m) ≠ ∞)
    (hsecond : ∑' m, simpleRandomWalk (second m) ≠ ∞) :
    ∑' m, simpleRandomWalk (first m ∪ second m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (first m) + simpleRandomWalk (second m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩
  exact ne_top_of_le_ne_top hmajor
    (ENNReal.tsum_le_tsum fun m ↦ measure_union_le _ _)

theorem candidateLocalOne_series
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 1 m) ≠ ∞ :=
  ne_top_of_le_ne_top (data.sourceOne_series t) <|
    ENNReal.tsum_le_tsum fun m ↦ measure_mono (data.candidateLocalOne_subset t m)

theorem candidateLocalBalance_series
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalProductPositiveInterfaceBalanceRemainderEvent
        product t m) ≠ ∞ :=
  ne_top_of_le_ne_top (data.balance_series t) <|
    ENNReal.tsum_le_tsum fun m ↦
      measure_mono (data.candidateLocalBalance_subset t m)

theorem candidateLocalTwo_series
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 2 m) ≠ ∞ :=
  ne_top_of_le_ne_top (data.sourceTwo_series t) <|
    ENNReal.tsum_le_tsum fun m ↦ measure_mono (data.candidateLocalTwo_subset t m)

theorem candidateLocalThree_series
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalOrientedSourceEventAtRank product t 3 m) ≠ ∞ :=
  ne_top_of_le_ne_top (data.sourceThree_series t) <|
    ENNReal.tsum_le_tsum fun m ↦ measure_mono (data.candidateLocalThree_subset t m)

/-- The rank-one staged candidate is paid by the internally summable
recurrence term and the concrete rank-one source payment. -/
theorem firstRawStagedCandidate_subset_majorant
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    firstRawStagedCandidate product t m a ⊆
      rawRankRecurrencePaymentEvent product t 1 m ∪
        (data.balance t m ∪ data.sourceOne t m) := by
  intro s hs
  have hroute :=
    preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
      product t 1 m (firstRawCandidatePreliminary t m a)
      (fun u hu ↦ firstRawCandidatePreliminary_creationProfile hu) hs
  rcases hroute with hrecurrence | hrest
  · exact Or.inl hrecurrence
  · rcases hrest with hbalance | hsource
    · exact Or.inr (Or.inl
        (data.firstRawBalance_subset t m a ⟨hs.1, hbalance⟩))
    · exact Or.inr (Or.inr (data.firstRawSource_subset t m a hsource))

theorem secondRawStagedCandidate_subset_majorant
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    secondRawStagedCandidate product t m a ⊆
      rawRankRecurrencePaymentEvent product t 2 m ∪
        (data.balance t m ∪ data.sourceTwo t m) := by
  intro s hs
  have hroute :=
    preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
      product t 2 m (secondRawCandidatePreliminary t m a)
      (fun u hu ↦ secondRawCandidatePreliminary_creationProfile hu) hs
  rcases hroute with hrecurrence | hrest
  · exact Or.inl hrecurrence
  · rcases hrest with hbalance | hsource
    · exact Or.inr (Or.inl
        (data.secondRawBalance_subset t m a ⟨hs.1, hbalance⟩))
    · exact Or.inr (Or.inr (data.secondRawSource_subset t m a hsource))

theorem thirdRawStagedCandidate_subset_majorant
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    thirdRawStagedCandidate product t m a ⊆
      rawRankRecurrencePaymentEvent product t 3 m ∪
        (data.balance t m ∪ data.sourceThree t m) := by
  intro s hs
  have hroute :=
    preliminary_inter_rankCandidateOverflow_subset_recurrence_or_source
      product t 3 m (thirdRawCandidatePreliminary t m a)
      (fun u hu ↦ thirdRawCandidatePreliminary_creationProfile hu) hs
  rcases hroute with hrecurrence | hrest
  · exact Or.inl hrecurrence
  · rcases hrest with hbalance | hsource
    · exact Or.inr (Or.inl
        (data.thirdRawBalance_subset t m a ⟨hs.1, hbalance⟩))
    · exact Or.inr (Or.inr (data.thirdRawSource_subset t m a hsource))

theorem firstMajorant_series
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (rawRankRecurrencePaymentEvent product t 1 m ∪
        (data.balance t m ∪ data.sourceOne t m)) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
      hmax product t 1 (by omega))
    (measure_union_series_ne_top (data.balance_series t)
      (data.sourceOne_series t))

theorem secondMajorant_series
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (rawRankRecurrencePaymentEvent product t 2 m ∪
        (data.balance t m ∪ data.sourceTwo t m)) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
      hmax product t 2 (by omega))
    (measure_union_series_ne_top (data.balance_series t)
      (data.sourceTwo_series t))

theorem thirdMajorant_series
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    {product : FullBetaSourceCorrectAllTilingProductData}
    (data : CorrectedProductSourceThetaSeriesData product) (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (rawRankRecurrencePaymentEvent product t 3 m ∪
        (data.balance t m ∪ data.sourceThree t m)) ≠ ∞ :=
  measure_union_series_ne_top
    (simpleRandomWalk_rawRankRecurrencePaymentEvent_series_ne_top
      hmax product t 3 (by omega))
    (measure_union_series_ne_top (data.balance_series t)
      (data.sourceThree_series t))

end CorrectedProductSourceThetaSeriesData

set_option linter.constructorNameAsVariable false in
/-- Current smallest upper wrapper over the corrected actual-increment
product, finite overlapping low rows, and the exact source/Theta series.

All recurrence, positive-interface, late-level, finite-prefix, high-spatial,
and transition-product estimates are derived internally.  A future concrete
source module should construct `source`; it must not add probability fields
to `product` or the low-coordinate package. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_correctedInterfaces
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (product : FullBetaSourceCorrectAllTilingProductData)
    (low : ∀ t : DominoTiling,
      PositiveLevelNoLazyFiniteSourceRowMeshCreationData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) t)
    (source : CorrectedProductSourceThetaSeriesData product) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  apply simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_correctedProduct
    hmax product low source.candidateLocalBalance_series
    source.candidateLocalOne_series source.candidateLocalTwo_series
      source.candidateLocalThree_series source.complement_series
    (fun t m ↦ rawRankRecurrencePaymentEvent product t 1 m ∪
      (source.balance t m ∪ source.sourceOne t m))
    (fun t m ↦ rawRankRecurrencePaymentEvent product t 2 m ∪
      (source.balance t m ∪ source.sourceTwo t m))
    (fun t m ↦ rawRankRecurrencePaymentEvent product t 3 m ∪
      (source.balance t m ∪ source.sourceThree t m))
  · intro t m a _ha
    exact source.firstRawStagedCandidate_subset_majorant t m a
  · intro t m a _ha
    exact source.secondRawStagedCandidate_subset_majorant t m a
  · intro t m a _ha
    exact source.thirdRawStagedCandidate_subset_majorant t m a
  · exact source.firstMajorant_series hmax
  · exact source.secondMajorant_series hmax
  · exact source.thirdMajorant_series hmax

end

end Erdos1165.HLOZNoLazyFiniteSourceRowUpperAssembly
