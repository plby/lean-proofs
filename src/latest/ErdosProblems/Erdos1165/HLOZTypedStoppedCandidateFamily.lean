/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture
import ErdosProblems.Erdos1165.TilingTypedFavoriteTrace
import ErdosProblems.Erdos1165.TilingCappedMarginalization
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockScreen

/-!
# A typed stopped-history candidate family

This is the literal countable stopped-history partition needed by the
low-scale branch of HLOZ Proposition 4.9.  A history records

* the valid retained tiling trace, and
* the finite random-clock near-favorite set.

There is one additional `none` atom for paths outside the relevant canonical
stage.  It is part of the exact partition of the preceding event, but has no
candidates.  Histories whose actual near-favorite set exceeds the budget are
also retained, with an empty candidate set.  Thus the partition remains exact
even for `previous = Set.univ`; the no-overflow bound is needed only on the
filtered target event.

The coordinate estimate below is derived from a
`TilingFactoredStoppedCoordinateData` certificate.  In particular, the
constructor of `SourceCorrectTransitionFactor.low` takes no path-level
transition inequality.  Its finite `product_bound` field is the place where
the exact negative-binomial small-window ratio is supplied.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZTypedStoppedCandidateFamily

open HLOZGapCandidateMeasurability HLOZGapRandomClockScreen HLOZPathEvents
open HLOZProposition48Candidates HLOZStoppedHistoryCandidateFuture
open HLOZSourceCorrectFutureTransition HLOZTilingGapRandomClockScreen
open HLOZTraceCappedProductScreening TilingCappedMarginalization
open TilingStoppedProductDisintegration TilingTypedFavoriteTrace
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The stopped history used in the low-scale factor.  The `none` history is
the explicit outside-stage atom, including both noncanonical paths and paths
which have not reached the relevant old-favorite stage.  A `some` history
records the actual candidate Finset even when it overflows; such an atom is
assigned the empty candidate family below. -/
abbrev TypedStoppedCandidateHistory (t : DominoTiling) (budget : ℕ) :=
  Option (TypedFavoriteTilingTraceCode t × Finset Point)

/-- Equality with one concrete random-clock candidate Finset is measurable.
This is stronger than cardinality measurability and is what the history
partition needs. -/
theorem measurableSet_tilingRandomClockBandSites_eq
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    (S : Finset Point) :
    MeasurableSet {s : WalkPath |
      tilingRandomClockBandSites t m cutoff s band = S} := by
  have heq :
      {s : WalkPath |
          tilingRandomClockBandSites t m cutoff s band = S} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | tilingPrefixBandSites t band.orientation band.vertexPhase
              band.externalThreshold m band.beta (pathPrefix s n) = S} := by
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
    (measurableSet_pathTruncatedLevelTime_eq
      m band.oldRank cutoff n).inter ?_
  exact measurableSet_eq_fun
    (measurable_fixed_tilingPrefixBandSites t n m band) measurable_const

/-- Membership in a finite stopped local-time window is measurable. -/
theorem measurableSet_tilingRandomClockTotalLocalTime_mem
    (m cutoff : ℕ) (band : RandomClockBand) (x : Point) (window : Finset ℕ) :
    MeasurableSet {s : WalkPath |
      tilingRandomClockTotalLocalTime m cutoff band s x ∈ window} := by
  have heq :
      {s : WalkPath |
          tilingRandomClockTotalLocalTime m cutoff band s x ∈ window} =
        ⋃ n : ℕ,
          {s | pathTruncatedLevelTime m band.oldRank cutoff s = n} ∩
            {s | localTime s n x ∈ window} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs
      exact ⟨pathTruncatedLevelTime m band.oldRank cutoff s, rfl, hs⟩
    · rintro ⟨n, hn, hs⟩
      simpa only [tilingRandomClockTotalLocalTime, hn] using hs
  rw [heq]
  refine MeasurableSet.iUnion fun n ↦
    (measurableSet_pathTruncatedLevelTime_eq
      m band.oldRank cutoff n).inter ?_
  exact (measurable_localTime_fixed n x)
    (Set.to_countable {q : ℕ | q ∈ window}).measurableSet

/-- The small-window event attached to one exposed stopped history and one
candidate. -/
def stoppedCandidateWindowEvent
    {History : Type*} (m cutoff : ℕ) (band : RandomClockBand)
    (window : History → Point → Finset ℕ) (h : History) (x : Point) :
    Set WalkPath :=
  {s | tilingRandomClockTotalLocalTime m cutoff band s x ∈ window h x}

theorem measurableSet_stoppedCandidateWindowEvent
    {History : Type*} (m cutoff : ℕ) (band : RandomClockBand)
    (window : History → Point → Finset ℕ) (h : History) (x : Point) :
    MeasurableSet (stoppedCandidateWindowEvent m cutoff band window h x) :=
  measurableSet_tilingRandomClockTotalLocalTime_mem
    m cutoff band x (window h x)

/-- The exact history atom.  A valid atom fixes both the typed retained trace
and the random-clock candidate Finset.  The `none` atom is precisely the
part of `previous` outside the relevant canonical stage. -/
def typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand) :
    TypedStoppedCandidateHistory t budget → Set WalkPath
  | none => previous \ (stage ∩ validStepWalk)
  | some (z, S) =>
      (previous ∩ typedFavoriteTilingStagePiece t m k stage z) ∩
        {s | tilingRandomClockBandSites t m cutoff s band = S}

/-- The candidates exposed by a typed history.  The outside-stage atom has
none. -/
def typedStoppedCandidates
    {t : DominoTiling} {budget : ℕ} :
    TypedStoppedCandidateHistory t budget → Finset Point
  | none => ∅
  | some (_, S) => if S.card ≤ budget then S else ∅

@[simp] theorem typedStoppedCandidates_none
    {t : DominoTiling} {budget : ℕ} :
    typedStoppedCandidates (t := t) (budget := budget) none = ∅ := by
  rfl

@[simp] theorem typedStoppedCandidates_some_of_card_le
    {t : DominoTiling} {budget : ℕ}
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point)
    (hS : S.card ≤ budget) :
    typedStoppedCandidates (t := t) (budget := budget) (some (z, S)) = S := by
  simp [typedStoppedCandidates, hS]

@[simp] theorem typedStoppedCandidates_some_of_card_gt
    {t : DominoTiling} {budget : ℕ}
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point)
    (hS : budget < S.card) :
    typedStoppedCandidates (t := t) (budget := budget) (some (z, S)) = ∅ := by
  simp [typedStoppedCandidates, Nat.not_le.mpr hS]

/-- The outside atom contains no path from the relevant canonical stage.
This is the explicit invalid/outside-stage handling used at rank one. -/
theorem mem_typedStoppedCandidatePiece_none_iff
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand) (s : WalkPath) :
    s ∈ typedStoppedCandidatePiece t m k cutoff budget stage previous band none ↔
      s ∈ previous ∧ s ∉ stage ∩ validStepWalk := by
  rfl

/-- A valid history atom fixes the actual random-clock candidate Finset,
not merely its cardinality or a slot enumeration. -/
theorem mem_typedStoppedCandidatePiece_some_iff
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point) (s : WalkPath) :
    s ∈ typedStoppedCandidatePiece t m k cutoff budget stage previous band
        (some (z, S)) ↔
      s ∈ previous ∧
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        tilingRandomClockBandSites t m cutoff s band = S := by
  simp only [typedStoppedCandidatePiece, Set.mem_inter_iff,
    Set.mem_ofPred_eq, and_assoc]

theorem tilingRandomClockBandSites_eq_of_mem_typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point) {s : WalkPath}
    (hs : s ∈ typedStoppedCandidatePiece t m k cutoff budget stage previous band
      (some (z, S))) :
    tilingRandomClockBandSites t m cutoff s band = S :=
  hs.2

/-- Two paths in one valid stopped-history atom have exactly the same actual
candidate Finset.  This is atom invariance; it makes no claim that arbitrary
coordinate replacement preserves the atom. -/
theorem tilingRandomClockBandSites_eq_of_mem_same_typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point)
    {s s' : WalkPath}
    (hs : s ∈ typedStoppedCandidatePiece t m k cutoff budget stage previous band
      (some (z, S)))
    (hs' : s' ∈ typedStoppedCandidatePiece t m k cutoff budget stage previous band
      (some (z, S))) :
    tilingRandomClockBandSites t m cutoff s band =
      tilingRandomClockBandSites t m cutoff s' band :=
  hs.2.trans hs'.2.symm

/-- Every valid history atom is contained in its supplied stage. -/
theorem typedStoppedCandidatePiece_some_subset_stage
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point) :
    typedStoppedCandidatePiece t m k cutoff budget stage previous band
        (some (z, S)) ⊆ stage := by
  intro s hs
  have hz := hs.1.2
  change s ∈ favoriteTilingCreationPiece t m k
      (some (eraseTypedFavoriteTilingTraceCode t z)) ∩ stage at hz
  exact hz.2

/-- Consequently, when the stage has already been intersected with a literal
source-eligibility event, every valid atom inherits that eligibility. -/
theorem typedStoppedCandidatePiece_some_subset_eligible
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous eligible : Set WalkPath) (band : RandomClockBand)
    (hstageEligible : stage ⊆ eligible)
    (z : TypedFavoriteTilingTraceCode t) (S : Finset Point) :
    typedStoppedCandidatePiece t m k cutoff budget stage previous band
        (some (z, S)) ⊆ eligible :=
  (typedStoppedCandidatePiece_some_subset_stage
    t m k cutoff budget stage previous band z S).trans hstageEligible

/-- The history-dependent small window.  Its endpoints may depend on the
retained external trace, exactly as in Proposition 4.9.  The outside-stage
atom has no near event. -/
def typedStoppedCandidateNear
    {t : DominoTiling} {budget : ℕ} (m cutoff : ℕ)
    (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ) :
    TypedStoppedCandidateHistory t budget → Point → Set WalkPath
  | none, _ => ∅
  | some (z, _), x => stoppedCandidateWindowEvent m cutoff band window z x

theorem measurableSet_typedStoppedCandidateNear
    {t : DominoTiling} {budget : ℕ} (m cutoff : ℕ)
    (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (h : TypedStoppedCandidateHistory t budget) (x : Point) :
    MeasurableSet (typedStoppedCandidateNear m cutoff band window h x) := by
  cases h with
  | none => exact MeasurableSet.empty
  | some h =>
      exact measurableSet_stoppedCandidateWindowEvent
        m cutoff band window h.1 x

theorem typedStoppedCandidates_card_le
    {t : DominoTiling} {budget : ℕ}
    (h : TypedStoppedCandidateHistory t budget) :
    (typedStoppedCandidates h).card ≤ budget := by
  cases h with
  | none => simp [typedStoppedCandidates]
  | some h =>
      by_cases hcard : h.2.card ≤ budget
      · simpa [typedStoppedCandidates, hcard] using hcard
      · simp [typedStoppedCandidates, hcard]

/-- Each typed retained-trace atom lies on canonical walk support. -/
theorem typedFavoriteTilingStagePiece_subset_validStepWalk
    (t : DominoTiling) (m k : ℕ) {stage : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (z : TypedFavoriteTilingTraceCode t) :
    typedFavoriteTilingStagePiece t m k stage z ⊆ validStepWalk := by
  intro s hs
  have hu : s ∈ ⋃ w : TypedFavoriteTilingTraceCode t,
      typedFavoriteTilingStagePiece t m k stage w :=
    Set.mem_iUnion.mpr ⟨z, hs⟩
  rw [iUnion_typedFavoriteTilingStagePiece t m k hstage] at hu
  exact hu.2

/-- A typed trace atom lies in the reaching stage as well as on canonical
support. -/
theorem typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
    (t : DominoTiling) (m k : ℕ) {stage : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (z : TypedFavoriteTilingTraceCode t) :
    typedFavoriteTilingStagePiece t m k stage z ⊆
      stage ∩ validStepWalk := by
  intro s hs
  have hu : s ∈ ⋃ w : TypedFavoriteTilingTraceCode t,
      typedFavoriteTilingStagePiece t m k stage w :=
    Set.mem_iUnion.mpr ⟨z, hs⟩
  rw [iUnion_typedFavoriteTilingStagePiece t m k hstage] at hu
  exact hu

theorem measurableSet_typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    {stage previous : Set WalkPath} (hstageMeasurable : MeasurableSet stage)
    (hprevious : MeasurableSet previous) (band : RandomClockBand)
    (h : TypedStoppedCandidateHistory t budget) :
    MeasurableSet
      (typedStoppedCandidatePiece t m k cutoff budget stage previous band h) := by
  cases h with
  | none =>
      exact hprevious.diff
        (hstageMeasurable.inter measurableSet_validStepWalk)
  | some h =>
      exact (hprevious.inter
        (measurableSet_typedFavoriteTilingStagePiece
          t m k hstageMeasurable h.1)).inter
        (measurableSet_tilingRandomClockBandSites_eq
          t m cutoff band h.2)

/-- Distinct typed stopped histories give disjoint atoms. -/
theorem pairwise_disjoint_typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k)
    (previous : Set WalkPath) (band : RandomClockBand) :
    Pairwise fun h h' : TypedStoppedCandidateHistory t budget ↦
      Disjoint
        (typedStoppedCandidatePiece
          t m k cutoff budget stage previous band h)
        (typedStoppedCandidatePiece
          t m k cutoff budget stage previous band h') := by
  classical
  intro h h' hne
  cases h with
  | none =>
      rcases h' with _ | ⟨z, S⟩
      · exact (hne rfl).elim
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs'.1.2)
  | some h =>
      rcases h with ⟨z, S⟩
      rcases h' with _ | ⟨w, T⟩
      · refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
        exact hs'.2
          (typedFavoriteTilingStagePiece_subset_stage_inter_validStepWalk
            t m k hstage z hs.1.2)
      · by_cases hzw : z = w
        · subst w
          have hST : S ≠ T := by
            intro hEq
            apply hne
            simp [hEq]
          refine Set.disjoint_left.2 fun s hs hs' ↦ ?_
          apply hST
          exact hs.2.symm.trans hs'.2
        · have hdisj :=
            disjoint_typedFavoriteTilingStagePiece_of_ne
              t m k stage hzw
          exact hdisj.mono
            (fun _ hs ↦ hs.1.2) (fun _ hs ↦ hs.1.2)

/-- The typed atoms together with the outside-stage atom partition an
arbitrary `previous` exactly, including candidate-overflow histories.  In
particular `previous = Set.univ` is allowed for the rank-one factor. -/
theorem iUnion_typedStoppedCandidatePiece
    (t : DominoTiling) (m k cutoff budget : ℕ)
    {stage previous : Set WalkPath}
    (hstage : stage ⊆ thresholdReachStage m k)
    (band : RandomClockBand) :
    (⋃ h : TypedStoppedCandidateHistory t budget,
      typedStoppedCandidatePiece
        t m k cutoff budget stage previous band h) = previous := by
  classical
  ext s
  constructor
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
    cases h with
    | none => exact hh.1
    | some h => exact hh.1.1
  · intro hs
    by_cases hcanonical : s ∈ stage ∩ validStepWalk
    · have hu : s ∈ ⋃ z : TypedFavoriteTilingTraceCode t,
          typedFavoriteTilingStagePiece t m k stage z := by
        rw [iUnion_typedFavoriteTilingStagePiece t m k hstage]
        exact hcanonical
      rcases Set.mem_iUnion.mp hu with ⟨z, hz⟩
      let S := tilingRandomClockBandSites t m cutoff s band
      exact Set.mem_iUnion.mpr ⟨some (z, S), ⟨⟨hs, hz⟩, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨none, ⟨hs, hcanonical⟩⟩

/-! ## Coordinate-ratio certificate -/

/-- A checked stopped-coordinate product law on one history atom implies the
required conditional coordinate ratio.  The proof builds a singleton trace
screen; hence no path-level probability inequality is an input. -/
theorem coordinate_ratio_of_tilingFactoredStoppedCoordinateData
    {piece near : Set WalkPath} {ratio : ℝ≥0∞}
    (hpiece : MeasurableSet piece) (hnear : MeasurableSet near)
    (hratio : ratio ≠ ∞)
    (data : TilingFactoredStoppedCoordinateData
      (fun _ : Unit ↦ piece) (piece ∩ near) ratio) :
    simpleRandomWalk (piece ∩ near) ≤ ratio * simpleRandomWalk piece := by
  let spec := tilingStoppedCoordinateProductSpecOfFactoredData data
  let screen : @TraceCappedProductScreening Unit inferInstance
      piece (piece ∩ near) ratio :=
    { piece := fun _ ↦ piece
      measurable_piece := fun _ ↦ hpiece
      disjoint_piece := by
        intro a b hab
        cases a
        cases b
        exact (hab rfl).elim
      union_piece := by
        apply Set.Subset.antisymm
        · exact Set.iUnion_subset fun _ ↦ Subset.rfl
        · intro s hs
          exact Set.mem_iUnion_of_mem () hs
      next_subset_stage := inter_subset_left
      certificate :=
        cappedProductScreenCertificateOfTilingStoppedCoordinateProductSpec
          spec }
  exact @transition_measure_le_of_traceCappedProductScreening Unit
    inferInstance piece (piece ∩ near) (hpiece.inter hnear) ratio hratio screen

/-! ## The concrete stopped-history family -/

/-- The literal typed stopped-history candidate family for one tiling, rank,
mesh branch, and random-clock band.

`coordinateData` is the checked all-six stopped-coordinate product law for
one candidate on one exposed history.  Its finite `product_bound` should be
proved with the exact negative-binomial window-ratio theorem. -/
noncomputable def typedStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t budget) (x : Point),
      x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece
            t m k cutoff budget stage previous band h)
          (typedStoppedCandidatePiece
              t m k cutoff budget stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (TypedStoppedCandidateHistory t budget) Point previous budget ratio where
  piece := typedStoppedCandidatePiece
    t m k cutoff budget stage previous band
  candidates := typedStoppedCandidates
  near := typedStoppedCandidateNear m cutoff band window
  piece_pairwise := pairwise_disjoint_typedStoppedCandidatePiece
    t m k cutoff budget hstage previous band
  piece_measurable := measurableSet_typedStoppedCandidatePiece
    t m k cutoff budget hstageMeasurable hpreviousMeasurable band
  piece_union := iUnion_typedStoppedCandidatePiece
    t m k cutoff budget hstage band
  candidate_card := typedStoppedCandidates_card_le
  coordinate_ratio := by
    intro h x hx
    exact coordinate_ratio_of_tilingFactoredStoppedCoordinateData
      (measurableSet_typedStoppedCandidatePiece
        t m k cutoff budget hstageMeasurable hpreviousMeasurable band h)
      (measurableSet_typedStoppedCandidateNear m cutoff band window h x)
      hratio (coordinateData h x hx)

/-- The concrete `someCandidate` event is measurable. -/
theorem measurableSet_typedStoppedHistorySomeCandidate
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t budget) (x : Point),
      x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece
            t m k cutoff budget stage previous band h)
          (typedStoppedCandidatePiece
              t m k cutoff budget stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio) :
    MeasurableSet
      (typedStoppedHistoryCandidateFamily t m k cutoff budget stage previous
        band window ratio hstageMeasurable hpreviousMeasurable hstage
        hratio coordinateData).someCandidate := by
  let family := typedStoppedHistoryCandidateFamily
    t m k cutoff budget stage previous band window ratio hstageMeasurable
      hpreviousMeasurable hstage hratio coordinateData
  exact MeasurableSet.iUnion fun h ↦
    MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun _hx ↦
      (measurableSet_typedStoppedCandidatePiece
        t m k cutoff budget hstageMeasurable hpreviousMeasurable band h).inter
      (measurableSet_typedStoppedCandidateNear m cutoff band window h x)

/-- If every target path has a valid typed trace and one member of its actual
random-clock candidate set in the corresponding small window, then it lies
in the concrete finite-candidate event. -/
theorem next_subset_typedStoppedHistorySomeCandidate
    (t : DominoTiling) (m k cutoff budget : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hnextBudget : ∀ s ∈ next,
      (tilingRandomClockBandSites t m cutoff s band).card ≤ budget)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t budget) (x : Point),
      x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece
            t m k cutoff budget stage previous band h)
          (typedStoppedCandidatePiece
              t m k cutoff budget stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t) (x : Point),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x ∈ tilingRandomClockBandSites t m cutoff s band ∧
        s ∈ stoppedCandidateWindowEvent m cutoff band window z x) :
    next ⊆
      (typedStoppedHistoryCandidateFamily t m k cutoff budget stage previous
        band window ratio hstageMeasurable hpreviousMeasurable hstage
        hratio coordinateData).someCandidate := by
  classical
  intro s hs
  rcases hsmallWindow s hs with ⟨z, x, hz, hx, hwindow⟩
  have hprev := hnextPrevious hs
  let S : Finset Point := tilingRandomClockBandSites t m cutoff s band
  let h : TypedStoppedCandidateHistory t budget := some (z, S)
  refine Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨x, ?_⟩⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · change x ∈ typedStoppedCandidates h
    simpa only [h, typedStoppedCandidates, S,
      if_pos (hnextBudget s hs)] using hx
  · exact ⟨⟨⟨hprev, hz⟩, rfl⟩, hwindow⟩

/-! ## The actual Proposition 4.8 budget and a direct low constructor -/

/-- Excluding the one-band overflow gives exactly the candidate-card bound
used in Proposition 4.9. -/
theorem tilingRandomClockBandSites_card_le_candidateBudget48
    (t : DominoTiling) (m cutoff : ℕ) (band : RandomClockBand)
    {s : WalkPath}
    (hgood : s ∈
      {w : WalkPath | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff w band).card}ᶜ) :
    (tilingRandomClockBandSites t m cutoff s band).card ≤
      candidateBudget48 m band.beta := by
  exact Nat.le_of_not_gt hgood

/-- Specialization of the concrete family to the source-compatible
`candidateBudget48`.  Overflow histories remain in the exact partition and
are assigned no candidates; exclusion of overflow is required only when a
filtered target is shown to lie in `someCandidate`. -/
noncomputable def candidateBudgetTypedStoppedHistoryCandidateFamily
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio) :
    StoppedHistoryCandidateFamily
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point previous (candidateBudget48 m band.beta) ratio :=
  typedStoppedHistoryCandidateFamily t m k cutoff
    (candidateBudget48 m band.beta) stage previous band window ratio
    hstageMeasurable hpreviousMeasurable hstage
    hratio coordinateData

/-- Source-compatible target-containment form: exclusion of the actual
one-band overflow is needed only on `next`, never on the preceding event. -/
theorem next_subset_candidateBudgetTypedStoppedHistorySomeCandidate
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (ratio : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hnextPrevious : next ⊆ previous)
    (hnextNoOverflow : next ⊆
      {s : WalkPath | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card}ᶜ)
    (hratio : ratio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          ratio)
    (hsmallWindow : ∀ s ∈ next,
      ∃ (z : TypedFavoriteTilingTraceCode t) (x : Point),
        s ∈ typedFavoriteTilingStagePiece t m k stage z ∧
        x ∈ tilingRandomClockBandSites t m cutoff s band ∧
        s ∈ stoppedCandidateWindowEvent m cutoff band window z x) :
    next ⊆
      (candidateBudgetTypedStoppedHistoryCandidateFamily t m k cutoff
        stage previous band window ratio hstageMeasurable
        hpreviousMeasurable hstage hratio coordinateData).someCandidate := by
  apply next_subset_typedStoppedHistorySomeCandidate t m k cutoff
    (candidateBudget48 m band.beta) stage previous next band window ratio
    hstageMeasurable hpreviousMeasurable hstage hnextPrevious
    (hratio := hratio) (coordinateData := coordinateData)
    (hsmallWindow := hsmallWindow)
  · intro s hs
    exact tilingRandomClockBandSites_card_le_candidateBudget48
      t m cutoff band (hnextNoOverflow hs)

/-- Direct constructor of the ordinary low-scale source-correct transition
factor.  Its quantitative stopped-history input is the checked coordinate
product data above; its future input is only the strong-Markov boundary
escape certificate. -/
noncomputable def candidateBudgetTypedSourceCorrectTransitionFactorLow
    {State : Type*} [Countable State]
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (candidateRatio escapeCost q : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : candidateRatio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          candidateRatio)
    (escape : BoundaryEscapeFutureFactorCertificate State
      (candidateBudgetTypedStoppedHistoryCandidateFamily t m k cutoff
        stage previous band window candidateRatio hstageMeasurable
        hpreviousMeasurable hstage hratio
        coordinateData).someCandidate
      next escapeCost)
    (cost_le : (candidateBudget48 m band.beta : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point State previous next q := by
  let family := candidateBudgetTypedStoppedHistoryCandidateFamily
    t m k cutoff stage previous band window candidateRatio hstageMeasurable
      hpreviousMeasurable hstage hratio
      coordinateData
  exact .low (candidateBudget48 m band.beta) candidateRatio escapeCost
    { candidate := family, escape := escape }
    (by
      exact MeasurableSet.iUnion fun h ↦
        MeasurableSet.iUnion fun x ↦ MeasurableSet.iUnion fun _hx ↦
          (measurableSet_typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) hstageMeasurable
            hpreviousMeasurable band h).inter
          (measurableSet_typedStoppedCandidateNear
            m cutoff band window h x))
    cost_le

/-- Atomwise strong-Markov variant used when the creation clock is exposed as
a countable family of fixed stopped-clock atoms.  This is the public low
constructor consumed by the current source-correct upper assembly. -/
noncomputable def candidateBudgetTypedSourceCorrectTransitionFactorLowAtomwise
    {Index : Type} {State : Type*} [Countable Index] [Countable State]
    (t : DominoTiling) (m k cutoff : ℕ)
    (stage previous next : Set WalkPath) (band : RandomClockBand)
    (window : TypedFavoriteTilingTraceCode t → Point → Finset ℕ)
    (candidateRatio escapeCost q : ℝ≥0∞)
    (hstageMeasurable : MeasurableSet stage)
    (hpreviousMeasurable : MeasurableSet previous)
    (hstage : stage ⊆ thresholdReachStage m k)
    (hratio : candidateRatio ≠ ∞)
    (coordinateData : ∀
      (h : TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      (x : Point), x ∈ typedStoppedCandidates h →
        TilingFactoredStoppedCoordinateData
          (fun _ : Unit ↦ typedStoppedCandidatePiece t m k cutoff
            (candidateBudget48 m band.beta) stage previous band h)
          (typedStoppedCandidatePiece t m k cutoff
              (candidateBudget48 m band.beta) stage previous band h ∩
            typedStoppedCandidateNear m cutoff band window h x)
          candidateRatio)
    (escape : CountableAtomFutureFactor Index State
      (candidateBudgetTypedStoppedHistoryCandidateFamily t m k cutoff
        stage previous band window candidateRatio hstageMeasurable
        hpreviousMeasurable hstage hratio
        coordinateData).someCandidate
      next escapeCost)
    (cost_le : (candidateBudget48 m band.beta : ℝ≥0∞) *
      candidateRatio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (TypedStoppedCandidateHistory t (candidateBudget48 m band.beta))
      Point State previous next q := by
  let family := candidateBudgetTypedStoppedHistoryCandidateFamily
    t m k cutoff stage previous band window candidateRatio hstageMeasurable
      hpreviousMeasurable hstage hratio
      coordinateData
  exact .lowAtomwise (candidateBudget48 m band.beta) candidateRatio escapeCost
    { candidate := family, escape := escape } cost_le

end

end Erdos1165.HLOZTypedStoppedCandidateFamily
