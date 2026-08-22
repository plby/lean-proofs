/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZEligibleOrientedAllCreationStoppedCandidateFamily

/-!
# Good-history filtered all-creation stopped candidates

Candidate cardinality is not the only source eligibility condition in
Proposition 4.9: the exact atom must also contain the required source
`D_eta`/restricted-Theta history.  This module therefore filters candidates
by an arbitrary deterministic atom predicate while retaining every ambient
history piece in the stopped partition.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZFilteredOrientedAllCreationStoppedCandidateFamily

open CappedCoordinateMassCertificate HLOZPathEvents
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The exact candidate support only on an eligible stopped atom. -/
noncomputable def filteredHistoryCandidates
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (eligible : SupportedIndex t o m k supportAt → Prop) :
    History t o m k supportAt → Finset Point := by
  classical
  intro h
  cases h with
  | none => exact ∅
  | some eta => exact if eligible eta then eta.1.2 else ∅

theorem mem_filteredHistoryCandidates_some_iff
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (eligible : SupportedIndex t o m k supportAt → Prop)
    (eta : SupportedIndex t o m k supportAt) (x : Point) :
    x ∈ filteredHistoryCandidates t o m k supportAt eligible (some eta) ↔
      eligible eta ∧ x ∈ eta.1.2 := by
  classical
  simp only [filteredHistoryCandidates]
  by_cases heligible : eligible eta
  · simp [heligible]
  · simp [heligible]

/-- All structural stopped-history data plus the exact good-history filter.
No probability estimate is a field. -/
structure FilteredOrientedAllCreationLowCoordinateData
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (previous : Set WalkPath) (ratio : ℝ≥0∞) where
  supportAt : WalkPath → ℕ → Finset Point
  supportData : OrientedAllCreationSupportSelectorData t o m k supportAt
  previous_measurable : MeasurableSet previous
  ratio_ne_top : ratio ≠ ∞
  eligible : SupportedIndex t o m k supportAt → Prop
  eligible_card : ∀ eta, eligible eta → eta.1.2.card ≤ budget
  near : SupportedIndex t o m k supportAt → Point → Set WalkPath
  near_measurable : ∀ eta x, MeasurableSet (near eta x)
  refinement : ∀ (eta : SupportedIndex t o m k supportAt) (x : Point),
    eligible eta → x ∈ eta.1.2 →
      OrientedAllCreationConditionalRefinementData
        ((orientedAllCreationConcreteFamily
          t o m k supportAt supportData).fiber eta)
        (historyPiece t o m k supportAt previous (some eta))
        (historyPiece t o m k supportAt previous (some eta) ∩ near eta x)
        ratio

namespace FilteredOrientedAllCreationLowCoordinateData

noncomputable def concreteFamily
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : FilteredOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily
      t o m k data.supportAt :=
  orientedAllCreationConcreteFamily
    t o m k data.supportAt data.supportData

def historyNear
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : FilteredOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    History t o m k data.supportAt → Point → Set WalkPath
  | none, _ => ∅
  | some eta, x => data.near eta x

noncomputable def family
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : FilteredOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    StoppedHistoryCandidateFamily
      (History t o m k data.supportAt) Point previous budget ratio where
  piece := historyPiece t o m k data.supportAt previous
  candidates := filteredHistoryCandidates
    t o m k data.supportAt data.eligible
  near := data.historyNear
  piece_pairwise := historyPiece_pairwise
    t o m k data.supportAt previous
  piece_measurable := measurableSet_historyPiece
    t o m k data.supportAt previous data.previous_measurable data.concreteFamily
  piece_union := iUnion_historyPiece t o m k data.supportAt previous
  candidate_card := by
    intro h
    cases h with
    | none => simp [filteredHistoryCandidates]
    | some eta =>
        classical
        by_cases heligible : data.eligible eta
        · simpa [filteredHistoryCandidates, heligible] using
            data.eligible_card eta heligible
        · simp [filteredHistoryCandidates, heligible]
  coordinate_ratio := by
    intro h x hx
    cases h with
    | none => simp [filteredHistoryCandidates] at hx
    | some eta =>
        have heligible := (mem_filteredHistoryCandidates_some_iff
          t o m k data.supportAt data.eligible eta x).mp hx
        exact coordinate_ratio_of_coordinateMassSpec
          (measurableSet_historyPiece t o m k data.supportAt previous
            data.previous_measurable data.concreteFamily (some eta))
          (data.near_measurable eta x) data.ratio_ne_top
          (coordinateMassSpecOfAllCreation
            (data.concreteFamily.fiber eta)
            (data.refinement eta x heligible.1 heligible.2))

theorem next_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous next : Set WalkPath} {ratio : ℝ≥0∞}
    (data : FilteredOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio)
    (hnext : ∀ s ∈ next,
      ∃ (eta : SupportedIndex t o m k data.supportAt) (x : Point),
        s ∈ historyPiece t o m k data.supportAt previous (some eta) ∧
        data.eligible eta ∧ x ∈ eta.1.2 ∧ s ∈ data.near eta x) :
    next ⊆ data.family.someCandidate := by
  intro s hs
  rcases hnext s hs with ⟨eta, x, hpiece, heligible, hx, hnear⟩
  have hx' : x ∈ filteredHistoryCandidates
      t o m k data.supportAt data.eligible (some eta) :=
    (mem_filteredHistoryCandidates_some_iff
      t o m k data.supportAt data.eligible eta x).2 ⟨heligible, hx⟩
  exact Set.mem_iUnion_of_mem (some eta)
    (Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx' ⟨hpiece, hnear⟩))

end FilteredOrientedAllCreationLowCoordinateData

end

end Erdos1165.HLOZFilteredOrientedAllCreationStoppedCandidateFamily
