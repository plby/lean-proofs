/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFilteredPastObservability
import ErdosProblems.Erdos1165.HLOZHeterogeneousFilteredTransitionFactors
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateFamily

/-!
# Heterogeneous high/low transition selection

Each proper HLOZ mesh gap is either high or low.  The high branch is built
from the concrete countable fixed-creation escape factor; the low branch is
built from the typed stopped-candidate coordinate family followed by the
same atomwise future escape.  This file selects the appropriate constructor
independently at the three ranks and packages their unrelated carrier types.

No target transition measure inequality is an input.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZMixedSpatialTransitionFactors

open HLOZFilteredPastObservability HLOZHighSpatialTransitionFactor
open HLOZHeterogeneousFilteredTransitionFactors HLOZPathEvents
open HLOZGapCandidateMeasurability HLOZGapRandomClockScreen
open HLOZProposition48Candidates HLOZSpatialAdapter
open HLOZSourceCorrectFilteredTransitions HLOZSourceCorrectFutureTransition
open HLOZStoppedHistoryCandidateFuture HLOZTypedStoppedCandidateFamily
open HLOZTilingGapRandomClockScreen HLOZTraceCappedProductScreening
open TilingCappedMarginalization TilingStoppedProductDisintegration
open TilingTypedFavoriteTrace TilingVariableStoppedTracePartition
open TerminalParameterBounds VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale
abbrev BranchEvent := DominoTiling → ℕ → GapTriple → Set WalkPath

/-! ## Literal low-factor data -/

/-- The complete literal input to one typed low-scale factor.  Its fields
are stopped-coordinate factorizations and an atomwise future escape
certificate; no probability inequality for `next` is stored. -/
structure CandidateBudgetTypedLowTransitionData
    (t : DominoTiling) (m k : ℕ)
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  Index : Type
  State : Type
  [index_countable : Countable Index]
  [state_countable : Countable State]
  cutoff : ℕ
  stage : Set WalkPath
  band : RandomClockBand
  window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ
  candidateRatio : ℝ≥0∞
  escapeCost : ℝ≥0∞
  stage_measurable : MeasurableSet stage
  previous_measurable : MeasurableSet previous
  stage_subset : stage ⊆ thresholdReachStage m k
  candidateRatio_ne_top : candidateRatio ≠ ∞
  coordinateData : ∀
    (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
    (x : Point), x ∈ typedStoppedCandidates h →
      TilingFactoredStoppedCoordinateData
        (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
          (candidateBudget48 m band.beta) stage previous band h)
        (typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h ∩
          typedStoppedCandidateNear m cutoff band window h x)
        candidateRatio
  escape : CountableAtomFutureFactor Index State
    (candidateBudgetTypedStoppedHistoryCandidateFamily t m k cutoff
      stage previous band window candidateRatio stage_measurable
      previous_measurable stage_subset candidateRatio_ne_top
      coordinateData).someCandidate
    next escapeCost
  cost_le : (candidateBudget48 m band.beta : ℝ≥0∞) *
    candidateRatio * escapeCost ≤ q

/-- Construct the heterogeneous wrapper by invoking the concrete typed
`.lowAtomwise` constructor. -/
noncomputable def CandidateBudgetTypedLowTransitionData.factor
    {t : DominoTiling} {m k : ℕ}
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (data : CandidateBudgetTypedLowTransitionData
      t m k previous next q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q := by
  letI := data.index_countable
  letI := data.state_countable
  exact .of
    (candidateBudgetTypedSourceCorrectTransitionFactorLowAtomwise
      (Index := data.Index) (State := data.State)
      t m k data.cutoff data.stage previous next data.band data.window
      data.candidateRatio data.escapeCost q data.stage_measurable
      data.previous_measurable data.stage_subset
      data.candidateRatio_ne_top data.coordinateData data.escape data.cost_le)

/-! ## Mesh projections -/

/-- Membership in a triple mesh supplies membership of all three entries.
The mesh stays abstract so concrete proper-mesh decision procedures are not
unfolded by downstream elaboration. -/
theorem mem_meshTriples_components
    {mesh : Finset GapScale} {a : GapTriple}
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    a.1.1 ∈ mesh ∧ a.1.2 ∈ mesh ∧ a.2 ∈ mesh := by
  have h := (Finset.mem_product.mp (Finset.mem_product.mp ha).1)
  exact ⟨h.1, h.2, (Finset.mem_product.mp ha).2⟩

/-! ## Rankwise mixed selectors -/

/-- Select the literal rank-one high or low constructor. -/
noncomputable def firstMixedSourceCorrectTransitionFactor
    (cap : ℕ → ℕ)
    (stagedCandidate₁ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (low : a.1.1 ∈ lowGapMesh →
      CandidateBudgetTypedLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousSourceCorrectTransitionFactor Set.univ
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (UpperCanonical.hlozTransitionCost K m) := by
  by_cases hhigh : a.1.1 ∈ highGapMesh
  · exact .of (filteredFirstHighSourceCorrectTransitionFactor cap
      stagedCandidate₁ K t m a hm hhigh hcandidate₁ hcost)
  · exact (low ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
      hhigh)).factor

/-- Select the literal rank-two high or low constructor.  In the high case,
the stopped-past premise is derived from the fixed pair atom and the
rank-one bad-filter observability adapter. -/
noncomputable def secondMixedSourceCorrectTransitionFactor
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
      CandidateBudgetTypedLowTransitionData t m 2
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
  · exact (low ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
      hhigh)).factor

/-- Select the literal rank-three high or low constructor. -/
noncomputable def thirdMixedSourceCorrectTransitionFactor
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
      CandidateBudgetTypedLowTransitionData t m 3
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
  · exact (low ((mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right
      hhigh)).factor

/-! ## Heterogeneous branch package -/

/-- Select high/low independently at all three ranks and assemble the
heterogeneous branch package.  Rank one starts from the whole path space;
the corrected typed low family has an explicit outside/overflow atom, so
this does not require a false global no-overflow condition. -/
noncomputable def mixedFilteredBranchTransitionFactorPackage
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
      CandidateBudgetTypedLowTransitionData t m 1 Set.univ
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₂ : a.1.2 ∈ lowGapMesh →
      CandidateBudgetTypedLowTransitionData t m 2
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₃ : a.2 ∈ lowGapMesh →
      CandidateBudgetTypedLowTransitionData t m 3
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a := by
  exact
    { stagedCandidate₁_measurable := hcandidate₁
      stagedCandidate₂_measurable := hcandidate₂
      stagedCandidate₃_measurable := hcandidate₃
      firstPast := Set.univ
      firstPast_measurable := MeasurableSet.univ
      first_next_subset_past := subset_univ _
      firstPast_measure_le_one := by simp
      firstFactor := firstMixedSourceCorrectTransitionFactor cap
        stagedCandidate₁ K t m a hm hproper₁ hcandidate₁ hcost low₁
      secondFactor := secondMixedSourceCorrectTransitionFactor cap
        stagedCandidate₁ stagedCandidate₂ K t m a hm hproper₂
        hcandidate₁ hcandidate₂ hstagedPair₁ hcost low₂
      thirdFactor := thirdMixedSourceCorrectTransitionFactor cap
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm
        hproper₃ hcandidate₁ hcandidate₂ hcandidate₃ hstagedTriple₁
        hstagedTriple₂ hcost low₃ }

end

end Erdos1165.HLOZMixedSpatialTransitionFactors
