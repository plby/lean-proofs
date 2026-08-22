/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZMeshCandidateFutureFactor
import ErdosProblems.Erdos1165.HLOZMeshCandidatePolynomialNumerics
import ErdosProblems.Erdos1165.HLOZNoLazyHighSpatialTransitionFactor
import ErdosProblems.Erdos1165.HLOZRawFullGapProductPromotion

/-!
# Fixed-first-strip low factors for the no-lazy transition chain

The candidate union in HLOZ Proposition 4.9 has the fixed first-strip
budget `initialBudget48 m`.  It is not the beta-dependent Proposition 4.8
overflow budget.  This module keeps that distinction in the type of the
low factor and combines it with the no-lazy high-spatial constructors.

The low numerical input is only the source product comparison

`initialBudget48 m * candidateRatio * escapeCost ≤ hlozTransitionCost K m`.

In particular, no adjacent-beta geometric-return comparison is present.
The stopped-candidate and future-event estimates are derived by the literal
countable-atom constructors.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZNoLazyInitialBudgetMixedTransitionFactors

open HLOZHighSpatialTransitionFactor HLOZNoLazyHighSpatialTransitionFactor
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyFilteredTransitions HLOZPathEvents
open HLOZProposition48Candidates HLOZRawFullGapProductPromotion
open HLOZSourceCorrectFutureTransition HLOZSpatialAdapter
open HLOZStoppedHistoryCandidateFuture TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-! ## The source-correct low factor -/

/-- Literal low-coordinate data with exactly the fixed Proposition 4.9
first-strip budget.

The carrier types are private to one rank and mesh coordinate.  The event
estimate is not stored: it follows from the stopped-history candidate family
and the countable fixed-clock future escape. -/
structure FirstStripLowTransitionData
    (m : ℕ) (previous next : Set WalkPath) (q : ℝ≥0∞) where
  History : Type
  Candidate : Type
  Index : Type
  State : Type
  [history_countable : Countable History]
  [index_countable : Countable Index]
  [state_countable : Countable State]
  candidateRatio : ℝ≥0∞
  escapeCost : ℝ≥0∞
  candidate : StoppedHistoryCandidateFamily History Candidate previous
    (initialBudget48 m) candidateRatio
  escape : CountableAtomFutureFactor Index State
    candidate.someCandidate next escapeCost
  cost_le :
    ((initialBudget48 m : ℕ) : ℝ≥0∞) * candidateRatio * escapeCost ≤ q

namespace FirstStripLowTransitionData

/-- Construct fixed-first-strip low data from literal mesh-creation atoms.
The future factor is derived by strong Markov from `CountableMeshCreationData`;
it is not an event-probability premise. -/
noncomputable def ofMeshCreation
    {Index History Candidate : Type}
    [Countable Index] [Countable History]
    {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath} {q candidateRatio : ℝ≥0∞}
    (hm : 1 ≤ m)
    (candidate : StoppedHistoryCandidateFamily History Candidate previous
      (initialBudget48 m) candidateRatio)
    (creation : CountableMeshCreationData Index candidate.someCandidate
      next m rank a)
    (cost_le : ((initialBudget48 m : ℕ) : ℝ≥0∞) * candidateRatio *
      meshEscapeCost m a ≤ q) :
    FirstStripLowTransitionData m previous next q where
  History := History
  Candidate := Candidate
  Index := Index
  State := Unit
  candidateRatio := candidateRatio
  escapeCost := meshEscapeCost m a
  candidate := candidate
  escape := creation.futureFactor hm
  cost_le := cost_le

/-- Fixed-level constructor in the exact form supplied by the polynomial
Proposition 4.9 numerics.  A concrete coordinate product proves only its
conditional ratio against `prop49CandidateRatioEnvelope`; the transition
cost is then obtained monotonically from the numerical envelope. -/
noncomputable def ofMeshCreationOfEnvelope
    {Index History Candidate : Type}
    [Countable Index] [Countable History]
    {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath} {candidateRatio : ℝ≥0∞}
    (hm : 1 ≤ m) (C : ℝ)
    (candidate : StoppedHistoryCandidateFamily History Candidate previous
      (initialBudget48 m) candidateRatio)
    (creation : CountableMeshCreationData Index candidate.someCandidate
      next m rank a)
    (hratio : candidateRatio ≤ prop49CandidateRatioEnvelope C m a)
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope C m a * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    FirstStripLowTransitionData m previous next
      (UpperCanonical.hlozTransitionCost 1 m) :=
  ofMeshCreation hm candidate creation <| by
    calc
      (initialBudget48 m : ℝ≥0∞) * candidateRatio * meshEscapeCost m a ≤
          (initialBudget48 m : ℝ≥0∞) *
            prop49CandidateRatioEnvelope C m a * meshEscapeCost m a := by
        gcongr
      _ ≤ UpperCanonical.hlozTransitionCost 1 m := hnumeric

/-- The exact fixed-budget `.lowAtomwise` factor, with all stopped carriers
hidden behind the heterogeneous wrapper. -/
noncomputable def factor
    {m : ℕ} {previous next : Set WalkPath} {q : ℝ≥0∞}
    (data : FirstStripLowTransitionData m previous next q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q := by
  letI := data.history_countable
  letI := data.index_countable
  letI := data.state_countable
  exact .of (.lowAtomwise (initialBudget48 m) data.candidateRatio
    data.escapeCost ⟨data.candidate, data.escape⟩ data.cost_le)

end FirstStripLowTransitionData

/-! ## Concrete mesh-creation data before numerical closure -/

/-- Literal low data at one mesh cell before the polynomial numerical
comparison is applied.  This is the preferred input shape for the incoming
all-creation coordinate constructor: its only quantitative field is the
Proposition 4.9 conditional-ratio envelope. -/
structure FirstStripMeshLowCoordinateData
    (C : ℝ) (m rank : ℕ) (a : GapScale)
    (previous next : Set WalkPath) where
  History : Type
  Candidate : Type
  Index : Type
  [history_countable : Countable History]
  [index_countable : Countable Index]
  candidateRatio : ℝ≥0∞
  candidate : StoppedHistoryCandidateFamily History Candidate previous
    (initialBudget48 m) candidateRatio
  creation : CountableMeshCreationData Index candidate.someCandidate
    next m rank a
  ratio_le : candidateRatio ≤ prop49CandidateRatioEnvelope C m a

namespace FirstStripMeshLowCoordinateData

/-- Apply the already derived polynomial envelope and obtain the exact low
transition certificate. -/
noncomputable def transitionData
    {C : ℝ} {m rank : ℕ} {a : GapScale}
    {previous next : Set WalkPath}
    (data : FirstStripMeshLowCoordinateData C m rank a previous next)
    (hm : 1 ≤ m)
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope C m a * meshEscapeCost m a ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    FirstStripLowTransitionData m previous next
      (UpperCanonical.hlozTransitionCost 1 m) := by
  letI := data.history_countable
  letI := data.index_countable
  exact FirstStripLowTransitionData.ofMeshCreationOfEnvelope hm C
    data.candidate data.creation data.ratio_le hnumeric

end FirstStripMeshLowCoordinateData

/-! ## Rankwise mixed selection -/

/-- Project membership in the product mesh. -/
theorem mem_meshTriples_components
    {mesh : Finset GapScale} {a : GapTriple}
    (ha : a ∈ UpperAssembly.meshTriples mesh) :
    a.1.1 ∈ mesh ∧ a.1.2 ∈ mesh ∧ a.2 ∈ mesh := by
  have h := Finset.mem_product.mp (Finset.mem_product.mp ha).1
  exact ⟨h.1, h.2, (Finset.mem_product.mp ha).2⟩

/-- Rank-one high/low selector.  Its low branch uses exactly
`initialBudget48 m`. -/
noncomputable def firstNoLazyInitialBudgetMixedFactor
    (stagedCandidate₁ : BranchEvent) (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hm : 1 ≤ m) (hproper : a.1.1 ∈ properGapMesh)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
    (low : a.1.1 ∈ lowGapMesh →
      FirstStripLowTransitionData m Set.univ
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

/-- Rank-two high/low selector. -/
noncomputable def secondNoLazyInitialBudgetMixedFactor
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
      FirstStripLowTransitionData m
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

/-- Rank-three high/low selector. -/
noncomputable def thirdNoLazyInitialBudgetMixedFactor
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
      FirstStripLowTransitionData m
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

/-! ## Three-factor and eventual packages -/

/-- Assemble three independently selected no-lazy factors, using the fixed
first-strip budget in every low branch. -/
noncomputable def noLazyInitialBudgetMixedBranchPackage
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
      FirstStripLowTransitionData m Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₂ : a.1.2 ∈ lowGapMesh →
      FirstStripLowTransitionData m
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (low₃ : a.2 ∈ lowGapMesh →
      FirstStripLowTransitionData m
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
  firstFactor := firstNoLazyInitialBudgetMixedFactor
    stagedCandidate₁ K t m a hm hproper₁ hcandidate₁ hcost low₁
  secondFactor := secondNoLazyInitialBudgetMixedFactor
    stagedCandidate₁ stagedCandidate₂ K t m a hm hproper₂ hcandidate₁
      hcandidate₂ hstagedPair₁ hcost low₂
  thirdFactor := thirdNoLazyInitialBudgetMixedFactor
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hm hproper₃
      hcandidate₁ hcandidate₂ hcandidate₃ hstagedTriple₁ hstagedTriple₂
      hcost low₃

/-- Eventual fixed-first-strip low data over a finite proper mesh. -/
structure PositiveLevelNoLazyInitialBudgetLowTransitionData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh → a.1.1 ∈ lowGapMesh →
      FirstStripLowTransitionData m Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh → a.1.2 ∈ lowGapMesh →
      FirstStripLowTransitionData m
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (UpperCanonical.hlozTransitionCost K m)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh → a.2 ∈ lowGapMesh →
      FirstStripLowTransitionData m
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)
        (UpperCanonical.hlozTransitionCost K m)

/-- Eventual literal coordinate and creation-atom data with a uniform
Proposition 4.9 constant.  Unlike
`PositiveLevelNoLazyInitialBudgetLowTransitionData`, this structure has no
transition-cost comparison field. -/
structure PositiveLevelNoLazyInitialBudgetMeshCreationData
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) where
  C : ℝ
  C_nonneg : 0 ≤ C
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  first : ∀ m, levelStart ≤ m → ∀ a,
    a.1.1 ∈ properGapMesh → a.1.1 ∈ lowGapMesh →
      FirstStripMeshLowCoordinateData C m 1 a.1.1 Set.univ
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
  second : ∀ m, levelStart ≤ m → ∀ a,
    a.1.2 ∈ properGapMesh → a.1.2 ∈ lowGapMesh →
      FirstStripMeshLowCoordinateData C m 2 a.1.2
        (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
  third : ∀ m, levelStart ≤ m → ∀ a,
    a.2 ∈ properGapMesh → a.2 ∈ lowGapMesh →
      FirstStripMeshLowCoordinateData C m 3 a.2
        (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m a)
        (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a)

namespace PositiveLevelNoLazyInitialBudgetMeshCreationData

/-- Close the low transition numerics uniformly over the finite proper mesh.
This constructs the eventual low-transition package; no cost estimate is
left to the caller. -/
noncomputable def toLowTransitionData
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {t : DominoTiling}
    (data : PositiveLevelNoLazyInitialBudgetMeshCreationData
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t) :
    PositiveLevelNoLazyInitialBudgetLowTransitionData stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ 1 t := by
  have heach : ∀ b ∈ properGapMesh, ∀ᶠ m : ℕ in atTop,
      (initialBudget48 m : ℝ≥0∞) *
          prop49CandidateRatioEnvelope data.C m b * meshEscapeCost m b ≤
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
  · intro m hm a hproper hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.first m hmData a hproper hlow).transitionData
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.1.1 hproper)
  · intro m hm a hproper hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.second m hmData a hproper hlow).transitionData
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.1.2 hproper)
  · intro m hm a hproper hlow
    have hmData : data.levelStart ≤ m :=
      (Nat.le_max_left data.levelStart numericStart).trans hm
    have hmNumeric : numericStart ≤ m :=
      (Nat.le_max_right data.levelStart numericStart).trans hm
    exact (data.third m hmData a hproper hlow).transitionData
      (data.levelStart_pos.trans_le hmData) (hnumeric m hmNumeric a.2 hproper)

end PositiveLevelNoLazyInitialBudgetMeshCreationData

/-- Lift eventual fixed-first-strip low data and the existing high envelope
to the generic no-lazy heterogeneous transition package. -/
noncomputable def positiveLevelNoLazyInitialBudgetMixedPackage
    (mesh : Finset GapScale)
    (hmesh : ∀ b ∈ mesh, b ∈ properGapMesh)
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (data : PositiveLevelNoLazyInitialBudgetLowTransitionData
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (costStart : ℕ)
    (hcost : ∀ m, costStart ≤ m → ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost K m)
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
    exact noLazyInitialBudgetMixedBranchPackage
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a hmOne
      ha₁ ha₂ ha₃ (hcandidate₁ m a) (hcandidate₂ m a)
      (hcandidate₃ m a) (hstagedPair₁ m a) (hstagedTriple₁ m a)
      (hstagedTriple₂ m a) (hcost m hmCost)
      (data.first m hmData a ha₁) (data.second m hmData a ha₂)
      (data.third m hmData a ha₃)

/-! ## Raw staged-candidate specialization -/

/-- The honest raw staged candidates discharge their ordinary and stopped
measurability internally.  The only data argument is the still-intermediate
literal fixed-first-strip low construction. -/
noncomputable def rawProperNoLazyInitialBudgetMixedPackage
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (data : PositiveLevelNoLazyInitialBudgetLowTransitionData
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1 t) :
    PositiveLevelNoLazyHeterogeneousTransitionFactorPackage properGapMesh
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1 t := by
  have hevent :=
    eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost_of_one_le
      1 (by norm_num)
  rw [eventually_atTop] at hevent
  let costStart := Classical.choose hevent
  have hcost := Classical.choose_spec hevent
  exact positiveLevelNoLazyInitialBudgetMixedPackage properGapMesh
    (fun _ hb ↦ hb) data costStart hcost
    (measurableSet_firstRawStagedCandidate product t)
    (measurableSet_secondRawStagedCandidate product t)
    (measurableSet_thirdRawStagedCandidate product t)
    (pairCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_firstRawStagedCandidate_observable product t)
    (tripleCreationAtom_inter_secondRawStagedCandidate_observable product t)

/-- Raw specialization from literal mesh-creation data.  Both the high
escape envelope and the low polynomial transition envelope are closed
internally. -/
noncomputable def rawProperNoLazyInitialBudgetMixedPackageOfMeshCreation
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling)
    (data : PositiveLevelNoLazyInitialBudgetMeshCreationData
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) t) :
    PositiveLevelNoLazyHeterogeneousTransitionFactorPackage properGapMesh
      (firstRawStagedCandidate product)
      (secondRawStagedCandidate product)
      (thirdRawStagedCandidate product) 1 t :=
  rawProperNoLazyInitialBudgetMixedPackage product t data.toLowTransitionData

/-- All six tilings, with the low numerical closure performed independently
inside each literal mesh-creation package. -/
noncomputable def rawProperNoLazyInitialBudgetMixedPackagesOfMeshCreation
    (product :
      HLOZSourceCorrectFullGapClosure.FullBetaSourceCorrectAllTilingProductData)
    (data : ∀ t : DominoTiling,
      PositiveLevelNoLazyInitialBudgetMeshCreationData
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) t) :
    ∀ t : DominoTiling,
      PositiveLevelNoLazyHeterogeneousTransitionFactorPackage properGapMesh
        (firstRawStagedCandidate product)
        (secondRawStagedCandidate product)
        (thirdRawStagedCandidate product) 1 t :=
  fun t ↦ rawProperNoLazyInitialBudgetMixedPackageOfMeshCreation
    product t (data t)

end

end Erdos1165.HLOZNoLazyInitialBudgetMixedTransitionFactors
