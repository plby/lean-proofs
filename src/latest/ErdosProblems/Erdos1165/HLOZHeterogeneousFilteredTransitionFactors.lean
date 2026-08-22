/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPositiveLevelFilteredTransitionAssembly
import ErdosProblems.Erdos1165.HLOZSourceCorrectFilteredTransitions

/-!
# Heterogeneous source-correct transition factors

The three HLOZ transitions need not use the same stopped-history carrier.
In particular a low-scale typed history depends on its rank, band, and
candidate budget, while a high-scale factor may use a countable family of
fixed creation clocks with unit state.  This module packages each factor
with its own carrier types.

The first low-scale factor also starts from an honest rank-one past event,
not from the whole path space.  Its past mass is at most one, which is all
the multiplicative endgame needs.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZHeterogeneousFilteredTransitionFactors

open HLOZSourceCorrectFilteredTransitions
open HLOZStoppedHistoryCandidateFuture
open HLOZPositiveLevelFilteredTransitionAssembly
open HLOZFilteredTransitionAssembly HLOZPathEvents

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent :=
  HLOZFilteredTransitionAssembly.BranchEvent

/-- One source-correct factor with private stopped-history and future-state
carrier types.  The factor itself still contains only literal coordinate and
strong-Markov certificates, never a transition probability inequality. -/
structure HeterogeneousSourceCorrectTransitionFactor
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  History : Type
  Candidate : Type
  State : Type
  [history_countable : Countable History]
  [state_countable : Countable State]
  factor : SourceCorrectTransitionFactor
    History Candidate State previous next q

/-- Forget the private carrier types and derive the relative measure bound. -/
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

/-- Wrap one already constructed high- or low-source factor while retaining
its own carrier types. -/
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

/-- Three filtered transition factors with independent carrier types.

For rank one, `firstPast` is the actual good stopped-history stage.  The
explicit containment records that the first filtered transition really
starts there; `firstPast_measure_le_one` converts the relative factor into
the absolute first-step estimate required by the mesh endgame. -/
structure HeterogeneousFilteredBranchTransitionFactorPackage
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ) (a : GapTriple) where
  stagedCandidate₁_measurable : MeasurableSet (stagedCandidate₁ t m a)
  stagedCandidate₂_measurable : MeasurableSet (stagedCandidate₂ t m a)
  stagedCandidate₃_measurable : MeasurableSet (stagedCandidate₃ t m a)
  firstPast : Set WalkPath
  firstPast_measurable : MeasurableSet firstPast
  first_next_subset_past :
    filteredFirstTransitionEvent cap stagedCandidate₁ t m a ⊆ firstPast
  firstPast_measure_le_one : simpleRandomWalk firstPast ≤ 1
  firstFactor : HeterogeneousSourceCorrectTransitionFactor
    firstPast
    (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
    (UpperCanonical.hlozTransitionCost K m)
  secondFactor : HeterogeneousSourceCorrectTransitionFactor
    (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
    (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
      t m a)
    (UpperCanonical.hlozTransitionCost K m)
  thirdFactor : HeterogeneousSourceCorrectTransitionFactor
    (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
      t m a)
    (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ t m a)
    (UpperCanonical.hlozTransitionCost K m)

/-- Compatibility adapter for the old homogeneous package.  It is useful for
an all-high branch, while mixed branches should construct the three
heterogeneous fields independently. -/
def HeterogeneousFilteredBranchTransitionFactorPackage.ofHomogeneous
    {History Candidate State : Type}
    [Countable History] [Countable State]
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (package : FilteredBranchTransitionFactorPackage
      History Candidate State cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ K t m a) :
    HeterogeneousFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a where
  stagedCandidate₁_measurable := package.stagedCandidate₁_measurable
  stagedCandidate₂_measurable := package.stagedCandidate₂_measurable
  stagedCandidate₃_measurable := package.stagedCandidate₃_measurable
  firstPast := Set.univ
  firstPast_measurable := MeasurableSet.univ
  first_next_subset_past := subset_univ _
  firstPast_measure_le_one := by simp
  firstFactor := .of package.factors.firstFactor
  secondFactor := .of package.factors.secondFactor
  thirdFactor := .of package.factors.thirdFactor

/-- Direct mixed high/low constructor.  Each rank may use unrelated literal
history, candidate, and future-state carriers. -/
def heterogeneousFilteredBranchTransitionFactorPackageOfFactors
    {History₁ Candidate₁ State₁ : Type}
    {History₂ Candidate₂ State₂ : Type}
    {History₃ Candidate₃ State₃ : Type}
    [Countable History₁] [Countable State₁]
    [Countable History₂] [Countable State₂]
    [Countable History₃] [Countable State₃]
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a))
    (firstPast : Set WalkPath)
    (hfirstPastMeasurable : MeasurableSet firstPast)
    (hfirstNextPast :
      filteredFirstTransitionEvent cap stagedCandidate₁ t m a ⊆ firstPast)
    (hfirstPastMass : simpleRandomWalk firstPast ≤ 1)
    (first : SourceCorrectTransitionFactor History₁ Candidate₁ State₁
      firstPast (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
        (UpperCanonical.hlozTransitionCost K m))
    (second : SourceCorrectTransitionFactor History₂ Candidate₂ State₂
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a) (UpperCanonical.hlozTransitionCost K m))
    (third : SourceCorrectTransitionFactor History₃ Candidate₃ State₃
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a)
      (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a)
      (UpperCanonical.hlozTransitionCost K m)) :
    HeterogeneousFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a where
  stagedCandidate₁_measurable := hcandidate₁
  stagedCandidate₂_measurable := hcandidate₂
  stagedCandidate₃_measurable := hcandidate₃
  firstPast := firstPast
  firstPast_measurable := hfirstPastMeasurable
  first_next_subset_past := hfirstNextPast
  firstPast_measure_le_one := hfirstPastMass
  firstFactor := .of first
  secondFactor := .of second
  thirdFactor := .of third

/-- The same three transition estimates as the old homogeneous package,
now derived from genuinely rank-dependent literal factor certificates. -/
theorem HeterogeneousFilteredBranchTransitionFactorPackage.measure_estimates
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (package : HeterogeneousFilteredBranchTransitionFactorPackage cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a) :
    simpleRandomWalk
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m ∧
      simpleRandomWalk
          (filteredSecondTransitionEvent cap stagedCandidate₁
            stagedCandidate₂ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ∧
      simpleRandomWalk
          (filteredThirdTransitionEvent cap stagedCandidate₁
            stagedCandidate₂ stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredSecondTransitionEvent cap stagedCandidate₁
                stagedCandidate₂ t m a) := by
  have hfirstMeas := measurableSet_filteredFirstTransitionEvent cap
    stagedCandidate₁ t m a package.stagedCandidate₁_measurable
  have hsecondMeas := measurableSet_filteredSecondTransitionEvent cap
    stagedCandidate₁ stagedCandidate₂ t m a
      package.stagedCandidate₁_measurable
      package.stagedCandidate₂_measurable
  have hthirdMeas := measurableSet_filteredThirdTransitionEvent cap
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a
      package.stagedCandidate₁_measurable
      package.stagedCandidate₂_measurable
      package.stagedCandidate₃_measurable
  have h₁ := package.firstFactor.measure_next_le
    package.firstPast_measurable hfirstMeas
  have h₂ := package.secondFactor.measure_next_le hfirstMeas hsecondMeas
  have h₃ := package.thirdFactor.measure_next_le hsecondMeas hthirdMeas
  refine ⟨?_, h₂, h₃⟩
  calc
    simpleRandomWalk
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m *
          simpleRandomWalk package.firstPast := h₁
    _ ≤ UpperCanonical.hlozTransitionCost K m * 1 := by
      exact mul_le_mul_right package.firstPast_measure_le_one _
    _ = UpperCanonical.hlozTransitionCost K m := mul_one _

/-- Eventual heterogeneous factors for one tiling.  The threshold may depend
on the tiling because the literal cap and source-stage laws do. -/
structure PositiveLevelHeterogeneousTransitionFactorPackage
    (mesh : Finset HLOZPathEvents.GapScale)
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) (t : DominoTiling) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  branch : ∀ m, levelStart ≤ m → ∀ a,
    a ∈ UpperAssembly.meshTriples mesh →
      HeterogeneousFilteredBranchTransitionFactorPackage cap
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a

/-- All three relative estimates supplied by an eventual heterogeneous
package.  The mesh is kept abstract here so elaboration never unfolds the
large concrete HLOZ mesh decision procedure. -/
theorem PositiveLevelHeterogeneousTransitionFactorPackage.measure_estimates
    {mesh : Finset HLOZPathEvents.GapScale}
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelHeterogeneousTransitionFactorPackage mesh cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
            (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ≤
            UpperCanonical.hlozTransitionCost K m ∧
          simpleRandomWalk
              (filteredSecondTransitionEvent cap stagedCandidate₁
                stagedCandidate₂ t m a) ≤
              UpperCanonical.hlozTransitionCost K m *
                simpleRandomWalk
                  (filteredFirstTransitionEvent cap stagedCandidate₁
                    t m a) ∧
          simpleRandomWalk
              (filteredThirdTransitionEvent cap stagedCandidate₁
                stagedCandidate₂ stagedCandidate₃ t m a) ≤
              UpperCanonical.hlozTransitionCost K m *
                simpleRandomWalk
                  (filteredSecondTransitionEvent cap stagedCandidate₁
                    stagedCandidate₂ t m a) := by
  intro m hm a ha
  exact (package.branch m hm a ha).measure_estimates

/-- Rank-one projection of `measure_estimates`, kept polymorphic in the mesh
so callers can pass the membership-consuming function without elaborating a
large concrete mesh proof. -/
theorem PositiveLevelHeterogeneousTransitionFactorPackage.first_measure_estimate
    {mesh : Finset HLOZPathEvents.GapScale}
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelHeterogeneousTransitionFactorPackage mesh cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
            (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ≤
          UpperCanonical.hlozTransitionCost K m := by
  intro m hm a ha
  exact (package.measure_estimates m hm a ha).1

/-- Rank-two projection of `measure_estimates`. -/
theorem PositiveLevelHeterogeneousTransitionFactorPackage.second_measure_estimate
    {mesh : Finset HLOZPathEvents.GapScale}
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelHeterogeneousTransitionFactorPackage mesh cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
            (filteredSecondTransitionEvent cap stagedCandidate₁
              stagedCandidate₂ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) := by
  intro m hm a ha
  exact (package.measure_estimates m hm a ha).2.1

/-- Rank-three projection of `measure_estimates`. -/
theorem PositiveLevelHeterogeneousTransitionFactorPackage.third_measure_estimate
    {mesh : Finset HLOZPathEvents.GapScale}
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0} {t : DominoTiling}
    (package : PositiveLevelHeterogeneousTransitionFactorPackage mesh cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t) :
    ∀ m, package.levelStart ≤ m → ∀ a,
      a ∈ UpperAssembly.meshTriples mesh →
        simpleRandomWalk
            (filteredThirdTransitionEvent cap stagedCandidate₁
              stagedCandidate₂ stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredSecondTransitionEvent cap stagedCandidate₁
                stagedCandidate₂ t m a) := by
  intro m hm a ha
  exact (package.measure_estimates m hm a ha).2.2

/-! ## Finite-mesh paid summability -/

/-- A pointwise union of two summable event families is summable. -/
theorem measure_union_series_ne_top
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

/-- Summability over every branch of a finite mesh implies summability of
the mesh union.  This is kept polymorphic in the mesh to avoid unfolding the
large concrete HLOZ mesh during elaboration. -/
theorem meshBranchUnion_series_ne_top_of_branch
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

/-- The honest paid family is summable once the global lazy event and each
of the three source-supported staged candidate families are summable on
every branch of a finite mesh. -/
theorem sourceCorrectPaidMesh_series_ne_top_of_staged
    (mesh : Finset HLOZPathEvents.GapScale)
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling)
    (hlazy : ∑' m,
      simpleRandomWalk (sourceCorrectLazyBadHistoryEvent t m (cap m)) ≠ ∞)
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
      (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃ t m)) ≠ ∞
    := by
  apply meshBranchUnion_series_ne_top_of_branch mesh
  intro a ha
  change ∑' m, simpleRandomWalk
    (sourceCorrectLazyBadHistoryEvent t m (cap m) ∪
      ((stagedCandidate₁ t m a ∪ stagedCandidate₂ t m a) ∪
        stagedCandidate₃ t m a)) ≠ ∞
  exact measure_union_series_ne_top hlazy
    (measure_union_series_ne_top
      (measure_union_series_ne_top (hcandidate₁ a ha) (hcandidate₂ a ha))
      (hcandidate₃ a ha))

/-- Specialization of `sourceCorrectPaidMesh_series_ne_top_of_staged` to the
fixed HLOZ mesh used by the filtered transition assembly. -/
theorem sourceCorrectPaidBadHistoryEvent_series_ne_top_of_staged
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling)
    (hlazy : ∑' m,
      simpleRandomWalk (sourceCorrectLazyBadHistoryEvent t m (cap m)) ≠ ∞)
    (hcandidate₁ : ∀ a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₁ t m a) ≠ ∞)
    (hcandidate₂ : ∀ a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₂ t m a) ≠ ∞)
    (hcandidate₃ : ∀ a,
      a ∈ UpperAssembly.meshTriples properGapMesh →
        ∑' m, simpleRandomWalk (stagedCandidate₃ t m a) ≠ ∞) :
    ∑' m, simpleRandomWalk
      (paidTransitionBadHistoryEvent
        (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
          stagedCandidate₂ stagedCandidate₃) t m) ≠ ∞ := by
  change ∑' m, simpleRandomWalk
    (UpperAssembly.meshBranchUnion properGapMesh
      (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃ t m)) ≠ ∞
  exact sourceCorrectPaidMesh_series_ne_top_of_staged properGapMesh cap
    stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t hlazy
      hcandidate₁ hcandidate₂ hcandidate₃

/-! ## Positive-level endgame -/

set_option linter.constructorNameAsVariable false in
/-- Feed literal heterogeneous rank factors into the positive-level filtered
assembly.  The three transition estimates are derived internally from the
rank-local coordinate and future-factor certificates; callers provide only
the exceptional-family summability proved by the concrete gap and lazy
screens. -/
theorem
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_heterogeneous_factors
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0)
    (factors : ∀ t : DominoTiling,
      PositiveLevelHeterogeneousTransitionFactorPackage properGapMesh cap
        stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t)
    (hbase : ∀ t,
      ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞)
    (hpaid : ∀ t, ∑' m,
      simpleRandomWalk
        (paidTransitionBadHistoryEvent
          (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
            stagedCandidate₂ stagedCandidate₃) t m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∀ᶠ n in Filter.atTop, favoriteCount s n ≤ 3 := by
  let start : DominoTiling → ℕ := fun t ↦ (factors t).levelStart
  apply
    simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_positiveLevel_filtered_estimates
      start K
      (firstFactorBadHistory cap stagedCandidate₁)
      (secondFactorBadHistory cap stagedCandidate₂)
      (thirdFactorBadHistory cap stagedCandidate₃)
      (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃)
      (sourceCorrect_terminalFilteredBadHistoryRouting cap stagedCandidate₁
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

end

end Erdos1165.HLOZHeterogeneousFilteredTransitionFactors
