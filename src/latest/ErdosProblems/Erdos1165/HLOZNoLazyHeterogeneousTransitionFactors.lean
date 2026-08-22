/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZNoLazyFilteredTransitions
import ErdosProblems.Erdos1165.HLOZUpperEstimates
import ErdosProblems.Erdos1165.Proposition13DirectTransferAssembly

/-!
# Heterogeneous factors for the candidate-local transition chain

Each of the three HLOZ ranks may use different stopped-history, candidate,
and future-state carrier types.  This module packages those literal
coordinate/strong-Markov certificates and feeds their derived estimates to
the positive-level filtered assembly.

The paid family is exactly the finite mesh union of the three staged
candidate histories.  There is no global or rankwise lazy-overflow event and
no lazy summability premise.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZNoLazyHeterogeneousTransitionFactors

open HLOZFilteredTransitionAssembly HLOZNoLazyFilteredTransitions
open HLOZPathEvents HLOZPositiveLevelFilteredTransitionAssembly
open HLOZStoppedHistoryCandidateFuture

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- A source-correct factor with private rank-specific carrier types. -/
structure HeterogeneousSourceCorrectTransitionFactor
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  History : Type
  Candidate : Type
  State : Type
  [history_countable : Countable History]
  [state_countable : Countable State]
  factor : SourceCorrectTransitionFactor
    History Candidate State previous next q

/-- Package an already constructed high- or low-source factor. -/
def HeterogeneousSourceCorrectTransitionFactor.of
    {History Candidate State : Type}
    [Countable History] [Countable State]
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (factor : SourceCorrectTransitionFactor
      History Candidate State previous next q) :
    HeterogeneousSourceCorrectTransitionFactor previous next q where
  History := History
  Candidate := Candidate
  State := State
  factor := factor

/-- Strong Markov and the stopped-candidate product law derive the relative
measure estimate hidden behind a heterogeneous carrier. -/
theorem HeterogeneousSourceCorrectTransitionFactor.measure_next_le
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (certificate : HeterogeneousSourceCorrectTransitionFactor
      previous next q)
    (hprevious : MeasurableSet previous) (hnext : MeasurableSet next) :
    simpleRandomWalk next ≤ q * simpleRandomWalk previous := by
  exact @SourceCorrectTransitionFactor.measure_next_le
    certificate.History certificate.Candidate certificate.State
    certificate.history_countable certificate.state_countable
    previous next q certificate.factor hprevious hnext

/-- Three no-lazy filtered factors with unrelated rankwise carriers.

Rank one starts from an explicit measurable past.  Its mass bound by one is
derived internally from the probability measure, so neither a redundant
containment nor a measure inequality is stored as package data. -/
structure NoLazyFilteredBranchTransitionFactorPackage
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple) where
  stagedCandidate₁_measurable : MeasurableSet (stagedCandidate₁ t m a)
  stagedCandidate₂_measurable : MeasurableSet (stagedCandidate₂ t m a)
  stagedCandidate₃_measurable : MeasurableSet (stagedCandidate₃ t m a)
  firstPast : Set WalkPath
  firstPast_measurable : MeasurableSet firstPast
  firstFactor : HeterogeneousSourceCorrectTransitionFactor
    firstPast
    (filteredFirstTransitionEvent stagedCandidate₁ t m a)
    (UpperCanonical.hlozTransitionCost K m)
  secondFactor : HeterogeneousSourceCorrectTransitionFactor
    (filteredFirstTransitionEvent stagedCandidate₁ t m a)
    (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
      t m a)
    (UpperCanonical.hlozTransitionCost K m)
  thirdFactor : HeterogeneousSourceCorrectTransitionFactor
    (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
      t m a)
    (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ t m a)
    (UpperCanonical.hlozTransitionCost K m)

/-- Direct constructor for a mixed high/low branch. -/
def noLazyFilteredBranchTransitionFactorPackageOfFactors
    {History₁ Candidate₁ State₁ : Type}
    {History₂ Candidate₂ State₂ : Type}
    {History₃ Candidate₃ State₃ : Type}
    [Countable History₁] [Countable State₁]
    [Countable History₂] [Countable State₂]
    [Countable History₃] [Countable State₃]
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (firstPast : Set WalkPath)
    (hfirstPastMeasurable : MeasurableSet firstPast)
    (first : SourceCorrectTransitionFactor History₁ Candidate₁ State₁
      firstPast (filteredFirstTransitionEvent stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (second : SourceCorrectTransitionFactor History₂ Candidate₂ State₂
      (filteredFirstTransitionEvent stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) (UpperCanonical.hlozTransitionCost K m))
    (third : SourceCorrectTransitionFactor History₃ Candidate₃ State₃
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m)) :
    NoLazyFilteredBranchTransitionFactorPackage
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a where
  stagedCandidate₁_measurable := hcandidate₁
  stagedCandidate₂_measurable := hcandidate₂
  stagedCandidate₃_measurable := hcandidate₃
  firstPast := firstPast
  firstPast_measurable := hfirstPastMeasurable
  firstFactor := .of first
  secondFactor := .of second
  thirdFactor := .of third

/-- The three transition estimates are consequences, not fields, of the
rank-local source-correct factors. -/
theorem NoLazyFilteredBranchTransitionFactorPackage.measure_estimates
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (package : NoLazyFilteredBranchTransitionFactorPackage
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a) :
    simpleRandomWalk
        (filteredFirstTransitionEvent stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m ∧
      simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredFirstTransitionEvent stagedCandidate₁ t m a) ∧
      simpleRandomWalk
          (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
            stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
                t m a) := by
  have hfirstMeas := measurableSet_filteredFirstTransitionEvent
    stagedCandidate₁ t m a package.stagedCandidate₁_measurable
  have hsecondMeas := measurableSet_filteredSecondTransitionEvent
    stagedCandidate₁ stagedCandidate₂ t m a
      package.stagedCandidate₁_measurable package.stagedCandidate₂_measurable
  have hthirdMeas := measurableSet_filteredThirdTransitionEvent
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a
      package.stagedCandidate₁_measurable package.stagedCandidate₂_measurable
      package.stagedCandidate₃_measurable
  have h₁ := package.firstFactor.measure_next_le
    package.firstPast_measurable hfirstMeas
  have h₂ := package.secondFactor.measure_next_le hfirstMeas hsecondMeas
  have h₃ := package.thirdFactor.measure_next_le hsecondMeas hthirdMeas
  have hfirstPastMass : simpleRandomWalk package.firstPast ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ package.firstPast)
  refine ⟨?_, h₂, h₃⟩
  calc
    simpleRandomWalk
        (filteredFirstTransitionEvent stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk package.firstPast := h₁
    _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
      exact mul_le_mul_right hfirstPastMass _
    _ = UpperCanonical.hlozTransitionCost K m := mul_one _

/-- Eventual heterogeneous factor constructors for one tiling. -/
structure PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
    (mesh : Finset GapScale)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  branch : ∀ m, levelStart ≤ m → ∀ a,
    a ∈ UpperAssembly.meshTriples mesh →
      NoLazyFilteredBranchTransitionFactorPackage
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a

theorem PositiveLevelNoLazyHeterogeneousTransitionFactorPackage.first_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
      mesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
          (filteredFirstTransitionEvent stagedCandidate₁ t m a) ≤
            UpperCanonical.hlozTransitionCost K m := by
  intro m hm a ha
  exact (NoLazyFilteredBranchTransitionFactorPackage.measure_estimates
    (package.branch m hm a ha)).1

theorem PositiveLevelNoLazyHeterogeneousTransitionFactorPackage.second_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
      mesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredFirstTransitionEvent stagedCandidate₁ t m a) := by
  intro m hm a ha
  exact (NoLazyFilteredBranchTransitionFactorPackage.measure_estimates
    (package.branch m hm a ha)).2.1

theorem PositiveLevelNoLazyHeterogeneousTransitionFactorPackage.third_measure_estimate
    {mesh : Finset GapScale}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
      mesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
          (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
            stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
                t m a) := by
  intro m hm a ha
  exact (NoLazyFilteredBranchTransitionFactorPackage.measure_estimates
    (package.branch m hm a ha)).2.2

/-! ## Candidate-only paid summability -/

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

private theorem meshBranchUnion_series_ne_top_of_branch
    {Scale : Type*} (mesh : Finset Scale)
    (branch : ℕ → ((Scale × Scale) × Scale) → Set WalkPath)
    (hbranch : ∀ a, a ∈ UpperAssembly.meshTriples mesh →
      ∑' m, simpleRandomWalk (branch m a) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion mesh (branch m)) ≠ ∞ := by
  have hpoint : ∀ m,
      simpleRandomWalk (UpperAssembly.meshBranchUnion mesh (branch m)) ≤
        ∑ a ∈ UpperAssembly.meshTriples mesh,
          simpleRandomWalk (branch m a) := by
    intro m
    simpa only [UpperAssembly.meshBranchUnion] using
      (measure_biUnion_finset_le (μ := simpleRandomWalk)
        (UpperAssembly.meshTriples mesh) (branch m))
  have hle :
      (∑' m, simpleRandomWalk
        (UpperAssembly.meshBranchUnion mesh (branch m))) ≤
      ∑' m, ∑ a ∈ UpperAssembly.meshTriples mesh,
        simpleRandomWalk (branch m a) :=
    ENNReal.tsum_le_tsum hpoint
  have hswap :
      (∑' m, ∑ a ∈ UpperAssembly.meshTriples mesh,
        simpleRandomWalk (branch m a)) =
      ∑ a ∈ UpperAssembly.meshTriples mesh,
        ∑' m, simpleRandomWalk (branch m a) := by
    simpa only [Finset.sum_attach, Finset.mem_univ, forall_const] using
      (Summable.tsum_finsetSum
        (s := UpperAssembly.meshTriples mesh)
        (f := fun a m ↦ simpleRandomWalk (branch m a))
        (fun _ _ ↦ ENNReal.summable))
  rw [hswap] at hle
  apply ne_top_of_le_ne_top _ hle
  exact ENNReal.sum_ne_top.mpr fun a ha ↦ hbranch a ha

/-- The finite-mesh paid event is summable using only the three staged
candidate series. -/
theorem candidatePaidBadHistoryEvent_series_ne_top_of_staged
    (mesh : Finset GapScale)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling)
    (hcandidate₁ : ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        ∑' m, simpleRandomWalk (stagedCandidate₁ t m a) ≠ ∞)
    (hcandidate₂ : ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        ∑' m, simpleRandomWalk (stagedCandidate₂ t m a) ≠ ∞)
    (hcandidate₃ : ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        ∑' m, simpleRandomWalk (stagedCandidate₃ t m a) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion mesh
        (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m)) ≠ ∞ := by
  apply meshBranchUnion_series_ne_top_of_branch mesh
  intro a ha
  exact measure_union_series_ne_top
    (measure_union_series_ne_top (hcandidate₁ a ha) (hcandidate₂ a ha))
    (hcandidate₃ a ha)

/-- A convenient concrete seam: it is enough to dominate every mesh branch
at rank `k` by one summable rankwise payment event.  This is the shape
exported by the raw source/Theta/positive-interface decomposition. -/
theorem candidatePaidBadHistoryEvent_series_ne_top_of_rank_majorants
    (mesh : Finset GapScale)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (major₁ major₂ major₃ : DominoTiling → ℕ → Set WalkPath)
    (t : DominoTiling)
    (hsubset₁ : ∀ m a, a ∈ UpperAssembly.meshTriples mesh →
      stagedCandidate₁ t m a ⊆ major₁ t m)
    (hsubset₂ : ∀ m a, a ∈ UpperAssembly.meshTriples mesh →
      stagedCandidate₂ t m a ⊆ major₂ t m)
    (hsubset₃ : ∀ m a, a ∈ UpperAssembly.meshTriples mesh →
      stagedCandidate₃ t m a ⊆ major₃ t m)
    (hmajor₁ : ∑' m, simpleRandomWalk (major₁ t m) ≠ ∞)
    (hmajor₂ : ∑' m, simpleRandomWalk (major₂ t m) ≠ ∞)
    (hmajor₃ : ∑' m, simpleRandomWalk (major₃ t m) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion mesh
        (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m)) ≠ ∞ := by
  apply candidatePaidBadHistoryEvent_series_ne_top_of_staged mesh
  · intro a ha
    exact ne_top_of_le_ne_top hmajor₁
      (ENNReal.tsum_le_tsum fun m ↦ measure_mono (hsubset₁ m a ha))
  · intro a ha
    exact ne_top_of_le_ne_top hmajor₂
      (ENNReal.tsum_le_tsum fun m ↦ measure_mono (hsubset₂ m a ha))
  · intro a ha
    exact ne_top_of_le_ne_top hmajor₃
      (ENNReal.tsum_le_tsum fun m ↦ measure_mono (hsubset₃ m a ha))

/-! ## Intermediate analytic endgame -/

set_option linter.constructorNameAsVariable false in
/-- Candidate-local heterogeneous endgame.

This theorem is an intermediate adapter: the completed raw full-gap module
will discharge `hgap` and the three staged series from its literal data.  In
particular this statement has no lazy-event series and assumes no transition
probability inequality. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_noLazy_factors_and_staged_series
    (hdirect : Proposition13DirectTransferAssembly.HasDirectAnnularScaleData)
    {c : ℝ} (hc : 0 < c)
    (hgap : HLOZUpperEstimates.HasGapDeficitReturnHarnack c)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0)
    (factors : ∀ t : DominoTiling,
      PositiveLevelNoLazyHeterogeneousTransitionFactorPackage
        properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (hcandidate₁ : ∀ t a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₁ t m a) ≠ ∞)
    (hcandidate₂ : ∀ t a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₂ t m a) ≠ ∞)
    (hcandidate₃ : ∀ t a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₃ t m a) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  let start : DominoTiling → ℕ := fun t ↦ (factors t).levelStart
  have hProp13 : HasPlanarMaximumLowerDeviation simpleRandomWalk :=
    Proposition13DirectTransferAssembly.hasPlanarMaximumLowerDeviation_of_directData
      hdirect
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevel_filtered_estimates
      start K
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
  · intro t
    exact HLOZUpperEstimates.simpleRandomWalk_hlozExceptional_series_ne_top
      hProp13 hc hgap t
  · intro t
    exact candidatePaidBadHistoryEvent_series_ne_top_of_staged
      properGapMesh stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t
      (hcandidate₁ t) (hcandidate₂ t) (hcandidate₃ t)

end

end Erdos1165.HLOZNoLazyHeterogeneousTransitionFactors
