/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFilteredTransitionAssembly
import ErdosProblems.Erdos1165.HLOZFullBetaRegimeSplit
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Source-correct filtered HLOZ transitions

The transition estimate in HLOZ Proposition 4.7 is a future estimate after
the old favorite clock.  It is valid only after removing three kinds of bad
old histories: a low-gap local-time deficit, a failure of the lazy cap, or a
Proposition 4.8 candidate overflow.  The first kind is paid only when the
terminal four-favorite event occurs, where it is already contained in
`hlozExceptionalEvent`; the latter two are paid additively as genuine
stopped-history exceptions.

This file makes that distinction literal.  It defines the three rank-local
factor filters, the cumulatively filtered transition chain, and a terminal
cover in which only the lazy/candidate histories are added to the existing
exceptional event.  In particular, no prefix-only screen is claimed to
control an unrestricted future transition.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.HLOZSourceCorrectFilteredTransitions

open HLOZFilteredTransitionAssembly HLOZFullBetaRegimeSplit
open HLOZGapEstimate HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates
open HLOZTilingGapRandomClockScreen ScreeningInstantiation
open HLOZStoppedHistoryCandidateFuture

noncomputable section

set_option linter.constructorNameAsVariable false

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := (GapScale × GapScale) × GapScale

/-- The source endpoint bands whose old favorite has the indicated rank. -/
noncomputable def sourceProductEndpointBandsAtRank
    (m cap externalThreshold rank : ℕ) : Finset RandomClockBand :=
  (sourceProductEndpointBands m cap externalThreshold).filter fun band ↦
    band.oldRank = rank

/-- Failure of either phase of the valid lazy cap at one old-favorite rank. -/
def rankLazyCapFailureEvent (t : DominoTiling) (m cap rank : ℕ) : Set WalkPath :=
  tilingStoppedLazyOverflowEvent t .even m rank cap ∪
    tilingStoppedLazyOverflowEvent t .shifted m rank cap

/-- Source-correct Proposition 4.8 overflow at one old-favorite rank. -/
def rankCandidateOverflowEvent (t : DominoTiling)
    (m cutoff cap externalThreshold rank : ℕ) : Set WalkPath :=
  tilingRandomClockCandidateOverflow t m cutoff
    (sourceProductEndpointBandsAtRank m cap externalThreshold rank)

/-- The two stopped-past exceptions which are paid additively. -/
def rankAuxiliaryBadHistoryEvent (t : DominoTiling)
    (m cutoff cap externalThreshold rank : ℕ) : Set WalkPath :=
  rankLazyCapFailureEvent t m cap rank ∪
    rankCandidateOverflowEvent t m cutoff cap externalThreshold rank

/-- Rank-one low-gap failure, restricted to the actual first transition. -/
def firstLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, pairConfiguration t m a.1.1 n₁ n₂ ∩
    {s | lowGapDeficitFailure s m n₁ n₂}

/-- Rank-two low-gap failure, restricted to the actual second transition. -/
def secondLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃,
    tripleConfiguration t m a.1.1 a.1.2 n₁ n₂ n₃ ∩
      {s | lowGapDeficitFailure s m n₂ n₃}

/-- Rank-three low-gap failure, restricted to the terminal transition. -/
def thirdLowGapFailureEvent (t : DominoTiling) (m : ℕ)
    (a : GapTriple) : Set WalkPath :=
  ⋃ n₁, ⋃ n₂, ⋃ n₃, ⋃ n₄,
    quadrupleConfiguration t m a.1.1 a.1.2 a.2 n₁ n₂ n₃ n₄ ∩
      {s | lowGapDeficitFailure s m n₃ n₄}

/-- Complete rank-one filter used by the first future transition estimate.

`stagedCandidate₁` is deliberately an input.  It must be the
source-supported candidate failure on the literal `D_eta ∩ {Theta = ∅}`
history (and the corresponding positive-shell histories), not the
unconditional random-clock candidate overflow. -/
def firstFactorBadHistory (cap : ℕ → ℕ)
    (stagedCandidate₁ : BranchEvent) : BranchEvent := fun t m a ↦
  (firstLowGapFailureEvent t m a ∪
    rankLazyCapFailureEvent t m (cap m) 1) ∪ stagedCandidate₁ t m a

/-- Complete rank-two filter.  The source-supported candidate failure is an
explicit intermediate input for the full-gap product closure. -/
def secondFactorBadHistory (cap : ℕ → ℕ)
    (stagedCandidate₂ : BranchEvent) : BranchEvent := fun t m a ↦
  (secondLowGapFailureEvent t m a ∪
    rankLazyCapFailureEvent t m (cap m) 2) ∪ stagedCandidate₂ t m a

/-- Complete rank-three filter. -/
def thirdFactorBadHistory (cap : ℕ → ℕ)
    (stagedCandidate₃ : BranchEvent) : BranchEvent := fun t m a ↦
  (thirdLowGapFailureEvent t m a ∪
    rankLazyCapFailureEvent t m (cap m) 3) ∪ stagedCandidate₃ t m a

/-- The source-correct first transition: its old history is good and its
future remains unrestricted until the strong-Markov certificate is applied. -/
def filteredFirstTransitionEvent (cap : ℕ → ℕ)
    (stagedCandidate₁ : BranchEvent) : BranchEvent :=
  goodFirstTransitionEvent (firstFactorBadHistory cap stagedCandidate₁)

/-- The source-correct second transition, with both earlier histories good. -/
def filteredSecondTransitionEvent (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent) : BranchEvent :=
  goodSecondTransitionEvent
    (firstFactorBadHistory cap stagedCandidate₁)
    (secondFactorBadHistory cap stagedCandidate₂)

/-- The source-correct terminal transition.  The pre-existing screen removes
all terminal low-gap failures, while the displayed factor filters record the
same good-history conditions used at ranks one through three. -/
def filteredThirdTransitionEvent (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    BranchEvent :=
  goodThirdTransitionEvent
    (firstFactorBadHistory cap stagedCandidate₁)
    (secondFactorBadHistory cap stagedCandidate₂)
    (thirdFactorBadHistory cap stagedCandidate₃)

/-- The global lazy exception is exactly the already constructed valid-cap
overflow family. -/
def sourceCorrectLazyBadHistoryEvent (t : DominoTiling)
    (m cap : ℕ) : Set WalkPath :=
  tilingLazyOverflowExceptionalEvent t m cap

/-- The three source-supported candidate failures supplied by the full-gap
closure.  Their construction must retain the literal `D_eta`/`Theta` source
support; this definition performs no unconditional enlargement. -/
def sourceCorrectStagedCandidateBadHistoryEvent
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    BranchEvent := fun t m a ↦
  (stagedCandidate₁ t m a ∪ stagedCandidate₂ t m a) ∪
    stagedCandidate₃ t m a

/-- The honest paid branch family: the globally controlled valid-lazy
failure, plus only the source-supported candidate failures.  In particular,
the unconditional all-band random-clock overflow is absent. -/
def sourceCorrectPaidBadHistoryEvent (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    BranchEvent := fun t m a ↦
  sourceCorrectLazyBadHistoryEvent t m (cap m) ∪
    sourceCorrectStagedCandidateBadHistoryEvent
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a

theorem measurableSet_rankLazyCapFailureEvent
    (t : DominoTiling) (m cap rank : ℕ) :
    MeasurableSet (rankLazyCapFailureEvent t m cap rank) :=
  (measurableSet_tilingStoppedLazyOverflowEvent t .even m rank cap).union
    (measurableSet_tilingStoppedLazyOverflowEvent t .shifted m rank cap)

/-- Cardinality overflow of one random-clock band is a stopped-prefix
measurable event. -/
theorem measurableSet_tilingRandomClockBandCardOverflow
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand) :
    MeasurableSet {s : WalkPath | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card} := by
  have heq :
      {s : WalkPath | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | candidateBudget48 m band.beta <
              (tilingPrefixBandSites t band.orientation band.vertexPhase
                band.externalThreshold m band.beta (pathPrefix s n)).card} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      refine ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, ?_⟩
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock rfl] using hs
    · rintro ⟨n, hn, hs⟩
      simpa only [tilingRandomClockBandSites_eq_prefix_of_clock hn] using hs
  rw [heq]
  refine MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq m band.oldRank cutoff n).inter ?_
  have hsites := measurable_fixed_tilingPrefixBandSites t n m band
  have hcard : Measurable fun s : WalkPath ↦
      (tilingPrefixBandSites t band.orientation band.vertexPhase
        band.externalThreshold m band.beta (pathPrefix s n)).card :=
    (measurable_of_countable (fun sites : Finset Point ↦ sites.card)).comp hsites
  exact measurableSet_lt measurable_const hcard

theorem measurableSet_tilingRandomClockCandidateOverflow
    (t : DominoTiling) (m cutoff : ℕ) (bands : Finset RandomClockBand) :
    MeasurableSet (tilingRandomClockCandidateOverflow t m cutoff bands) := by
  classical
  induction bands using Finset.induction_on with
  | empty =>
      simp [tilingRandomClockCandidateOverflow, candidateOverflow]
  | @insert band bands hband ih =>
      rw [show tilingRandomClockCandidateOverflow t m cutoff (insert band bands) =
          {s | candidateBudget48 m band.beta <
            (tilingRandomClockBandSites t m cutoff s band).card} ∪
            tilingRandomClockCandidateOverflow t m cutoff bands by
        ext s
        simp [tilingRandomClockCandidateOverflow, candidateOverflow]]
      exact (measurableSet_tilingRandomClockBandCardOverflow t m cutoff band).union ih

theorem measurableSet_rankCandidateOverflowEvent
    (t : DominoTiling) (m cutoff cap externalThreshold rank : ℕ) :
    MeasurableSet
      (rankCandidateOverflowEvent t m cutoff cap externalThreshold rank) :=
  measurableSet_tilingRandomClockCandidateOverflow t m cutoff _

theorem measurableSet_rankAuxiliaryBadHistoryEvent
    (t : DominoTiling) (m cutoff cap externalThreshold rank : ℕ) :
    MeasurableSet
      (rankAuxiliaryBadHistoryEvent t m cutoff cap externalThreshold rank) :=
  (measurableSet_rankLazyCapFailureEvent t m cap rank).union
    (measurableSet_rankCandidateOverflowEvent t m cutoff cap
      externalThreshold rank)

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
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₁ t m a)) :
    MeasurableSet (firstFactorBadHistory cap stagedCandidate₁ t m a) :=
  ((measurableSet_firstLowGapFailureEvent t m a).union
    (measurableSet_rankLazyCapFailureEvent t m (cap m) 1)).union hcandidate

theorem measurableSet_secondFactorBadHistory
    (cap : ℕ → ℕ) (stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₂ t m a)) :
    MeasurableSet (secondFactorBadHistory cap stagedCandidate₂ t m a) :=
  ((measurableSet_secondLowGapFailureEvent t m a).union
    (measurableSet_rankLazyCapFailureEvent t m (cap m) 2)).union hcandidate

theorem measurableSet_thirdFactorBadHistory
    (cap : ℕ → ℕ) (stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet (thirdFactorBadHistory cap stagedCandidate₃ t m a) :=
  ((measurableSet_thirdLowGapFailureEvent t m a).union
    (measurableSet_rankLazyCapFailureEvent t m (cap m) 3)).union hcandidate

theorem measurableSet_sourceCorrectPaidBadHistoryEvent
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (h₁ : MeasurableSet (stagedCandidate₁ t m a))
    (h₂ : MeasurableSet (stagedCandidate₂ t m a))
    (h₃ : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet (sourceCorrectPaidBadHistoryEvent cap
      stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a) :=
  (measurableSet_tilingLazyOverflowExceptionalEvent t m (cap m)).union
    ((h₁.union h₂).union h₃)

theorem measurableSet_filteredFirstTransitionEvent
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate : MeasurableSet (stagedCandidate₁ t m a)) :
    MeasurableSet
      (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) :=
  (measurableSet_firstTransitionEvent t m a).diff
    (measurableSet_firstFactorBadHistory cap stagedCandidate₁ t m a hcandidate)

theorem measurableSet_filteredSecondTransitionEvent
    (cap : ℕ → ℕ) (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a)) :
    MeasurableSet
      (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a) :=
  (measurableSet_secondTransitionEvent t m a).diff
    ((measurableSet_firstFactorBadHistory cap stagedCandidate₁ t m a
        hcandidate₁).union
      (measurableSet_secondFactorBadHistory cap stagedCandidate₂ t m a
        hcandidate₂))

theorem measurableSet_filteredThirdTransitionEvent
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple)
    (hcandidate₁ : MeasurableSet (stagedCandidate₁ t m a))
    (hcandidate₂ : MeasurableSet (stagedCandidate₂ t m a))
    (hcandidate₃ : MeasurableSet (stagedCandidate₃ t m a)) :
    MeasurableSet
      (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a) :=
  (measurableSet_screenedThirdTransitionEvent t m a).diff
    (((measurableSet_firstFactorBadHistory cap stagedCandidate₁ t m a
        hcandidate₁).union
      (measurableSet_secondFactorBadHistory cap stagedCandidate₂ t m a
        hcandidate₂)).union
      (measurableSet_thirdFactorBadHistory cap stagedCandidate₃ t m a
        hcandidate₃))

/-! ## Concrete future-factor packages -/

/-- Literal stopped-coordinate/strong-Markov data for one filtered mesh
branch.  Its sole field is the source-correct high/low factor certificate;
there is no transition probability inequality among its premises. -/
structure FilteredBranchTransitionFactorPackage
    (History Candidate State : Type*)
    [Countable History] [Countable State]
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) where
  stagedCandidate₁_measurable : MeasurableSet (stagedCandidate₁ t m a)
  stagedCandidate₂_measurable : MeasurableSet (stagedCandidate₂ t m a)
  stagedCandidate₃_measurable : MeasurableSet (stagedCandidate₃ t m a)
  factors : ThreeSourceCorrectTransitionFactors History Candidate State
    (filteredFirstTransitionEvent cap stagedCandidate₁ t m a)
    (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂ t m a)
    (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
      stagedCandidate₃ t m a)
    (UpperCanonical.hlozTransitionCost K m)

/-- The three filtered transition inequalities are consequences of the
finite stopped-coordinate and future escape certificates. -/
theorem FilteredBranchTransitionFactorPackage.measure_estimates
    {History Candidate State : Type*}
    [Countable History] [Countable State]
    {cap : ℕ → ℕ}
    {stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent}
    {K : ℝ≥0}
    {t : DominoTiling} {m : ℕ} {a : GapTriple}
    (package : FilteredBranchTransitionFactorPackage
      History Candidate State cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ K t m a) :
    simpleRandomWalk
        (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ≤
        UpperCanonical.hlozTransitionCost K m ∧
      simpleRandomWalk
        (filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredFirstTransitionEvent cap stagedCandidate₁ t m a) ∧
      simpleRandomWalk
        (filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a) ≤
          UpperCanonical.hlozTransitionCost K m *
            simpleRandomWalk
              (filteredSecondTransitionEvent cap stagedCandidate₁
                stagedCandidate₂ t m a) :=
  package.factors.measure_estimates
    (measurableSet_filteredFirstTransitionEvent cap stagedCandidate₁ t m a
      package.stagedCandidate₁_measurable)
    (measurableSet_filteredSecondTransitionEvent cap stagedCandidate₁
      stagedCandidate₂ t m a package.stagedCandidate₁_measurable
      package.stagedCandidate₂_measurable)
    (measurableSet_filteredThirdTransitionEvent cap stagedCandidate₁
      stagedCandidate₂ stagedCandidate₃ t m a
      package.stagedCandidate₁_measurable package.stagedCandidate₂_measurable
      package.stagedCandidate₃_measurable)

/-- Eventual positive-level source-correct transition package.  This is the
replacement for the impossible prefix-only typed package: at every large
level and mesh branch it contains literal coordinate/future certificates,
not assumed transition bounds. -/
structure PositiveLevelFilteredTransitionFactorPackage
    (History Candidate State : Type*)
    [Countable History] [Countable State]
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (K : ℝ≥0) where
  levelStart : ℕ
  levelStart_pos : 0 < levelStart
  branch : ∀ t m, levelStart ≤ m → ∀ a,
    a ∈ UpperAssembly.meshTriples properGapMesh →
      FilteredBranchTransitionFactorPackage History Candidate State
        cap stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ K t m a

theorem rankLazyCapFailureEvent_subset_global
    (t : DominoTiling) (m cap : ℕ) (rank : Fin 3) :
    rankLazyCapFailureEvent t m cap (rank + 1) ⊆
      sourceCorrectLazyBadHistoryEvent t m cap := by
  rintro s (heven | hshifted)
  · exact Or.inl (Set.mem_iUnion.mpr ⟨rank, heven⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨rank, hshifted⟩)

theorem filteredSecondTransitionEvent_subset_filteredFirst
    (cap : ℕ → ℕ) (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂ t m a ⊆
      filteredFirstTransitionEvent cap stagedCandidate₁ t m a :=
  goodSecondTransitionEvent_subset_goodFirst _ _ _ _ _

theorem filteredThirdTransitionEvent_subset_filteredSecond
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        stagedCandidate₃ t m a ⊆
      filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
        t m a :=
  goodThirdTransitionEvent_subset_goodSecond _ _ _ _ _ _

/-- Every raw first transition is either rejected by its literal good-history
filter or belongs to the future-filtered transition. -/
theorem firstTransitionEvent_subset_factorBad_union_filtered
    (cap : ℕ → ℕ) (stagedCandidate₁ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    firstTransitionEvent t m a ⊆
      firstFactorBadHistory cap stagedCandidate₁ t m a ∪
        filteredFirstTransitionEvent cap stagedCandidate₁ t m a := by
  intro s hs
  by_cases hbad : s ∈ firstFactorBadHistory cap stagedCandidate₁ t m a
  · exact Or.inl hbad
  · exact Or.inr ⟨hs, hbad⟩

/-- Every raw second transition is either rejected at rank one or two, or
belongs to the cumulatively filtered second transition. -/
theorem secondTransitionEvent_subset_factorBad_union_filtered
    (cap : ℕ → ℕ) (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    secondTransitionEvent t m a ⊆
      (firstFactorBadHistory cap stagedCandidate₁ t m a ∪
        secondFactorBadHistory cap stagedCandidate₂ t m a) ∪
          filteredSecondTransitionEvent cap stagedCandidate₁ stagedCandidate₂
            t m a := by
  intro s hs
  by_cases hbad : s ∈
      firstFactorBadHistory cap stagedCandidate₁ t m a ∪
        secondFactorBadHistory cap stagedCandidate₂ t m a
  · exact Or.inl hbad
  · exact Or.inr ⟨hs, hbad⟩

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
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, ha₁, ha₂, ha₃⟩
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
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, ha₁, ha₂, ha₃⟩
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
    ⟨h₁, h₂, h₃, h₄, hnext, hsep, ha₁, ha₂, ha₃⟩
  apply gapDeficitExceptionalEvent_subset_hlozExceptionalEvent t m
  exact ⟨n₁, n₂, n₃, n₄, h₁, h₂, h₃, h₄, hnext, hsep,
    Or.inr (Or.inr hfail)⟩

/-- Source-correct terminal split with candidate failures supplied only on
their literal source histories.  Low-gap rejections route to the existing
exceptional event; valid-lazy failures and the three staged candidate
families are the only newly paid histories. -/
theorem thirdTransitionEvent_subset_exceptional_union_paid_union_filtered
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (a : GapTriple) :
    thirdTransitionEvent t m a ⊆
      (hlozExceptionalEvent t m ∪
        sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
          stagedCandidate₂ stagedCandidate₃ t m a) ∪
        filteredThirdTransitionEvent cap stagedCandidate₁ stagedCandidate₂
          stagedCandidate₃ t m a := by
  intro s hthird
  by_cases he : s ∈ hlozExceptionalEvent t m
  · exact Or.inl (Or.inl he)
  by_cases hbad : s ∈
      ((firstFactorBadHistory cap stagedCandidate₁ t m a ∪
        secondFactorBadHistory cap stagedCandidate₂ t m a) ∪
        thirdFactorBadHistory cap stagedCandidate₃ t m a)
  · apply Or.inl
    rcases hbad with (hbad₁ | hbad₂) | hbad₃
    · rcases hbad₁ with (hgap₁ | hlazy₁) | hcandidate₁
      · exact (he (third_and_firstLowGapFailure_subset_exceptional
          ⟨hthird, hgap₁⟩)).elim
      · apply Or.inr
        exact Or.inl (rankLazyCapFailureEvent_subset_global
          t m (cap m) (0 : Fin 3) hlazy₁)
      · apply Or.inr
        exact Or.inr (Or.inl (Or.inl hcandidate₁))
    · rcases hbad₂ with (hgap₂ | hlazy₂) | hcandidate₂
      · exact (he (third_and_secondLowGapFailure_subset_exceptional
          ⟨hthird, hgap₂⟩)).elim
      · apply Or.inr
        exact Or.inl (rankLazyCapFailureEvent_subset_global
          t m (cap m) (1 : Fin 3) hlazy₂)
      · apply Or.inr
        exact Or.inr (Or.inl (Or.inr hcandidate₂))
    · rcases hbad₃ with (hgap₃ | hlazy₃) | hcandidate₃
      · exact (he (thirdLowGapFailureEvent_subset_exceptional hgap₃)).elim
      · apply Or.inr
        exact Or.inl (rankLazyCapFailureEvent_subset_global
          t m (cap m) (2 : Fin 3) hlazy₃)
      · apply Or.inr
        exact Or.inr (Or.inr hcandidate₃)
  · apply Or.inr
    exact ⟨⟨hthird, he⟩, hbad⟩

/-- The concrete terminal-routing interface consumed by the generic filtered
assembly.  The staged-candidate inputs remain visible, so a later full-gap
closure must construct and sum them from literal source atoms. -/
theorem sourceCorrect_terminalFilteredBadHistoryRouting
    (cap : ℕ → ℕ)
    (stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ : BranchEvent) :
    TerminalFilteredBadHistoryRouting
      (firstFactorBadHistory cap stagedCandidate₁)
      (secondFactorBadHistory cap stagedCandidate₂)
      (thirdFactorBadHistory cap stagedCandidate₃)
      (sourceCorrectPaidBadHistoryEvent cap stagedCandidate₁
        stagedCandidate₂ stagedCandidate₃) := by
  intro t m a _ha s hs
  have hcover :=
    thirdTransitionEvent_subset_exceptional_union_paid_union_filtered
      cap stagedCandidate₁ stagedCandidate₂ stagedCandidate₃ t m a hs.1.1
  rcases hcover with (he | hpaid) | hfiltered
  · exact Or.inl he
  · exact Or.inr hpaid
  · exfalso
    exact hfiltered.2 hs.2

end

end Erdos1165.HLOZSourceCorrectFilteredTransitions
