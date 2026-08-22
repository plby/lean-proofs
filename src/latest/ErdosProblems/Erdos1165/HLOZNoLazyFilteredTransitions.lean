/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPositiveLevelFilteredTransitionAssembly
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture
import ErdosProblems.Erdos1165.HLOZSpatialAdapter

/-!
# Candidate-local filtered HLOZ transitions

The source proof does not pay a global lazy-overflow event.  The lazy local
time bound is needed only at the selected near-level candidate, where it is a
deterministic consequence of the restricted-Theta source condition and the
external window.  Consequently the transition filters in this file remove
only

* the rank-local low-gap failure, which is already charged to
  `hlozExceptionalEvent` on a terminal four-favorite path; and
* the source-supported staged candidate failure.

This is deliberately parallel to the older lazy-filtered transition module.
No global or rankwise lazy event occurs in the definitions or terminal
routing theorem below.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZNoLazyFilteredTransitions

open HLOZFilteredTransitionAssembly HLOZPathEvents

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- Rank-one low-gap failure restricted to the first transition history. -/
def firstLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, pairConfiguration t m a.1.1 n₁ n₂ ∩
    {s | lowGapDeficitFailure s m n₁ n₂}

/-- Rank-two low-gap failure restricted to the second transition history. -/
def secondLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃,
    tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃ ∩
      {s | lowGapDeficitFailure s m n₂ n₃}

/-- Rank-three low-gap failure restricted to the terminal history. -/
def thirdLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄,
    quadrupleConfiguration t m a.1.1 a.1.2 a.2 n₁ n₂ n₃ n₄ ∩
      {s | lowGapDeficitFailure s m n₃ n₄}

/-- The rank-one factor filter.  There is no lazy-overflow component. -/
def firstFactorBadHistory (stagedCandidate₁ : BranchEvent) : BranchEvent :=
  fun t m a ↦ firstLowGapFailureEvent t m a ∪ stagedCandidate₁ t m a

/-- The rank-two factor filter. -/
def secondFactorBadHistory (stagedCandidate₂ : BranchEvent) : BranchEvent :=
  fun t m a ↦ secondLowGapFailureEvent t m a ∪ stagedCandidate₂ t m a

/-- The rank-three factor filter. -/
def thirdFactorBadHistory (stagedCandidate₃ : BranchEvent) : BranchEvent :=
  fun t m a ↦ thirdLowGapFailureEvent t m a ∪ stagedCandidate₃ t m a

/-- First source-correct transition filtered only by the rank-one gap and
staged-candidate conditions. -/
def filteredFirstTransitionEvent (stagedCandidate₁ : BranchEvent) :
    BranchEvent :=
  goodFirstTransitionEvent (firstFactorBadHistory stagedCandidate₁)

/-- Cumulatively filtered second transition. -/
def filteredSecondTransitionEvent
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent) : BranchEvent :=
  goodSecondTransitionEvent
    (firstFactorBadHistory stagedCandidate₁)
    (secondFactorBadHistory stagedCandidate₂)

/-- Cumulatively filtered terminal transition. -/
def filteredThirdTransitionEvent
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    BranchEvent :=
  goodThirdTransitionEvent
    (firstFactorBadHistory stagedCandidate₁)
    (secondFactorBadHistory stagedCandidate₂)
    (thirdFactorBadHistory stagedCandidate₃)

/-- The only newly paid histories are the three staged candidate families. -/
def candidatePaidBadHistoryEvent
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    BranchEvent := fun t m a ↦
  (stagedCandidate₁ t m a ∪ stagedCandidate₂ t m a) ∪
    stagedCandidate₃ t m a

theorem measurableSet_firstLowGapFailureEvent
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (firstLowGapFailureEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    (measurableSet_pairConfiguration t m a.1.1 n₁ n₂).inter
      (measurableSet_gapDeficitFailure m n₁ n₂)

theorem measurableSet_secondLowGapFailureEvent
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (secondLowGapFailureEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦
      (measurableSet_tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃).inter
        (measurableSet_gapDeficitFailure m n₂ n₃)

theorem measurableSet_thirdLowGapFailureEvent
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    MeasurableSet (thirdLowGapFailureEvent t m a) := by
  exact MeasurableSet.iUnion fun n₁ ↦ MeasurableSet.iUnion fun n₂ ↦
    MeasurableSet.iUnion fun n₃ ↦ MeasurableSet.iUnion fun n₄ ↦
      (measurableSet_quadrupleConfiguration t m a.1.1 a.1.2 a.2
        n₁ n₂ n₃ n₄).inter (measurableSet_gapDeficitFailure m n₃ n₄)

theorem measurableSet_firstFactorBadHistory
    (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₁ t m a)) :
    MeasurableSet (firstFactorBadHistory stagedCandidate₁ t m a) :=
  (measurableSet_firstLowGapFailureEvent t m a).union hcandidate

theorem measurableSet_secondFactorBadHistory
    (stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₂ t m a)) :
    MeasurableSet (secondFactorBadHistory stagedCandidate₂ t m a) :=
  (measurableSet_secondLowGapFailureEvent t m a).union hcandidate

theorem measurableSet_thirdFactorBadHistory
    (stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet (thirdFactorBadHistory stagedCandidate₃ t m a) :=
  (measurableSet_thirdLowGapFailureEvent t m a).union hcandidate

theorem measurableSet_candidatePaidBadHistoryEvent
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (h₁ : MeasurableSet (stagedCandidate₁ t m a))
    (h₂ : MeasurableSet (stagedCandidate₂ t m a))
    (h₃ : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet
      (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) :=
  (h₁.union h₂).union h₃

theorem measurableSet_filteredFirstTransitionEvent
    (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₁ t m a)) :
    MeasurableSet (filteredFirstTransitionEvent stagedCandidate₁ t m a) :=
  (measurableSet_firstTransitionEvent t m a).diff
    (measurableSet_firstFactorBadHistory stagedCandidate₁ t m a hcandidate)

theorem measurableSet_filteredSecondTransitionEvent
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a)) :
    MeasurableSet
      (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a) :=
  (measurableSet_secondTransitionEvent t m a).diff
    ((measurableSet_firstFactorBadHistory stagedCandidate₁ t m a
        hcandidate₁).union
      (measurableSet_secondFactorBadHistory stagedCandidate₂ t m a
        hcandidate₂))

theorem measurableSet_filteredThirdTransitionEvent
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet
      (filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) :=
  (measurableSet_screenedThirdTransitionEvent t m a).diff
    (((measurableSet_firstFactorBadHistory stagedCandidate₁ t m a
        hcandidate₁).union
      (measurableSet_secondFactorBadHistory stagedCandidate₂ t m a
        hcandidate₂)).union
      (measurableSet_thirdFactorBadHistory stagedCandidate₃ t m a
        hcandidate₃))

theorem filteredSecondTransitionEvent_subset_filteredFirst
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂ t m a ⊆
      filteredFirstTransitionEvent stagedCandidate₁ t m a :=
  goodSecondTransitionEvent_subset_goodFirst _ _ _ _ _

theorem filteredThirdTransitionEvent_subset_filteredSecond
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a ⊆
      filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m a :=
  goodThirdTransitionEvent_subset_goodSecond _ _ _ _ _ _

private theorem third_and_firstLowGapFailure_subset_exceptional
    {t : DominoTiling} {m : ℕ} {a : GapTriple} :
    thirdTransitionEvent t m a ∩ firstLowGapFailureEvent t m a ⊆
      hlozExceptionalEvent t m := by
  intro s hs
  rcases Set.mem_iUnion.mp hs.1 with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
  rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
  rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 ∧
    gapScaleOf m (s n₂) (s n₃) = a.1.2 ∧
    gapScaleOf m (s n₃) (s n₄) = a.2 at hquad
  rcases hquad with
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, _ha₁, _ha₂, _ha₃⟩
  rcases Set.mem_iUnion.mp hs.2 with ⟨q₁, hq₁union⟩
  rcases Set.mem_iUnion.mp hq₁union with ⟨q₂, hpair, hfail⟩
  change ThresholdCreation s m 1 q₁ ∧ ThresholdCreation s m 2 q₂ ∧
    thresholdCount s q₂ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s q₁) (s q₂) ∧
    gapScaleOf m (s q₁) (s q₂) = a.1.1 at hpair
  rcases hpair with ⟨hq₁, hq₂, _hqnext, _hqsep, _hqa⟩
  have hq₁eq : q₁ = n₁ :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hq₁ h₁
  have hq₂eq : q₂ = n₂ :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hq₂ h₂
  change lowGapDeficitFailure s m q₁ q₂ at hfail
  apply gapDeficitExceptionalEvent_subset_hlozExceptionalEvent t m
  exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    Or.inl (by simpa only [hq₁eq, hq₂eq] using hfail)⟩

private theorem third_and_secondLowGapFailure_subset_exceptional
    {t : DominoTiling} {m : ℕ} {a : GapTriple} :
    thirdTransitionEvent t m a ∩ secondLowGapFailureEvent t m a ⊆
      hlozExceptionalEvent t m := by
  intro s hs
  rcases Set.mem_iUnion.mp hs.1 with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
  rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
  rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 ∧
    gapScaleOf m (s n₂) (s n₃) = a.1.2 ∧
    gapScaleOf m (s n₃) (s n₄) = a.2 at hquad
  rcases hquad with
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, _ha₁, _ha₂, _ha₃⟩
  rcases Set.mem_iUnion.mp hs.2 with ⟨q₁, hq₁union⟩
  rcases Set.mem_iUnion.mp hq₁union with ⟨q₂, hq₂union⟩
  rcases Set.mem_iUnion.mp hq₂union with ⟨q₃, htriple, hfail⟩
  change ThresholdCreation s m 1 q₁ ∧ ThresholdCreation s m 2 q₂ ∧
    ThresholdCreation s m 3 q₃ ∧ thresholdCount s q₃ (m + 1) = 0 ∧
    ¬Tilings.sameDomino t (s q₁) (s q₂) ∧
    ¬Tilings.sameDomino t (s q₁) (s q₃) ∧
    ¬Tilings.sameDomino t (s q₂) (s q₃) ∧
    gapScaleOf m (s q₁) (s q₂) = a.1.1 ∧
    gapScaleOf m (s q₂) (s q₃) = a.1.2 at htriple
  rcases htriple with
    ⟨_hq₁, hq₂, hq₃, _hqnext, _hq₁₂, _hq₁₃, _hq₂₃, _hqa₁, _hqa₂⟩
  have hq₂eq : q₂ = n₂ :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hq₂ h₂
  have hq₃eq : q₃ = n₃ :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hq₃ h₃
  change lowGapDeficitFailure s m q₂ q₃ at hfail
  apply gapDeficitExceptionalEvent_subset_hlozExceptionalEvent t m
  exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    Or.inr (Or.inl (by simpa only [hq₂eq, hq₃eq] using hfail))⟩

private theorem thirdLowGapFailureEvent_subset_exceptional
    {t : DominoTiling} {m : ℕ} {a : GapTriple} :
    thirdLowGapFailureEvent t m a ⊆ hlozExceptionalEvent t m := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨n₁, hn₁⟩
  rcases Set.mem_iUnion.mp hn₁ with ⟨n₂, hn₂⟩
  rcases Set.mem_iUnion.mp hn₂ with ⟨n₃, hn₃⟩
  rcases Set.mem_iUnion.mp hn₃ with ⟨n₄, hquad, hfail⟩
  change ThresholdCreation s m 1 n₁ ∧ ThresholdCreation s m 2 n₂ ∧
    ThresholdCreation s m 3 n₃ ∧ ThresholdCreation s m 4 n₄ ∧
    thresholdCount s n₄ (m + 1) = 0 ∧
    fourPointsSeparated t (s n₁) (s n₂) (s n₃) (s n₄) ∧
    gapScaleOf m (s n₁) (s n₂) = a.1.1 ∧
    gapScaleOf m (s n₂) (s n₃) = a.1.2 ∧
    gapScaleOf m (s n₃) (s n₄) = a.2 at hquad
  rcases hquad with
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, _ha₁, _ha₂, _ha₃⟩
  apply gapDeficitExceptionalEvent_subset_hlozExceptionalEvent t m
  exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    Or.inr (Or.inr hfail)⟩

/-- A terminal transition is either already exceptional, belongs to one of
the three staged candidate families, or survives every no-lazy filter. -/
theorem thirdTransitionEvent_subset_exceptional_union_paid_union_filtered
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    thirdTransitionEvent t m a ⊆
      (hlozExceptionalEvent t m ∪
        candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a) ∪
        filteredThirdTransitionEvent stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a := by
  intro s hthird
  by_cases he : s ∈ hlozExceptionalEvent t m
  · exact Or.inl (Or.inl he)
  by_cases hbad : s ∈
      ((firstFactorBadHistory stagedCandidate₁ t m a ∪
        secondFactorBadHistory stagedCandidate₂ t m a) ∪
        thirdFactorBadHistory stagedCandidate₃ t m a)
  · apply Or.inl
    rcases hbad with (hbad₁ | hbad₂) | hbad₃
    · rcases hbad₁ with hgap₁ | hcandidate₁
      · exact (he (third_and_firstLowGapFailure_subset_exceptional
          ⟨hthird, hgap₁⟩)).elim
      · exact Or.inr (Or.inl (Or.inl hcandidate₁))
    · rcases hbad₂ with hgap₂ | hcandidate₂
      · exact (he (third_and_secondLowGapFailure_subset_exceptional
          ⟨hthird, hgap₂⟩)).elim
      · exact Or.inr (Or.inl (Or.inr hcandidate₂))
    · rcases hbad₃ with hgap₃ | hcandidate₃
      · exact (he (thirdLowGapFailureEvent_subset_exceptional hgap₃)).elim
      · exact Or.inr (Or.inr hcandidate₃)
  · exact Or.inr ⟨⟨hthird, he⟩, hbad⟩

/-- Terminal routing consumed by the generic positive-level assembly.  Its
paid family contains candidates only. -/
theorem noLazy_terminalFilteredBadHistoryRouting
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    TerminalFilteredBadHistoryRouting
      (firstFactorBadHistory stagedCandidate₁)
      (secondFactorBadHistory stagedCandidate₂)
      (thirdFactorBadHistory stagedCandidate₃)
      (candidatePaidBadHistoryEvent stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃) := by
  intro t m a _ha s hs
  have hcover :=
    thirdTransitionEvent_subset_exceptional_union_paid_union_filtered
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hs.1.1
  rcases hcover with (he | hpaid) | hfiltered
  · exact Or.inl he
  · exact Or.inr hpaid
  · exact (hfiltered.2 hs.2).elim

end

end Erdos1165.HLOZNoLazyFilteredTransitions
