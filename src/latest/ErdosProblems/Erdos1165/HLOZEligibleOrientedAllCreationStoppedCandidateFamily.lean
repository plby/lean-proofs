/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZOrientedAllCreationStoppedCandidateFamily

/-!
# Eligible all-creation stopped-candidate families

The Proposition 4.9 candidate-card bound holds only on the good stopped
history.  It is therefore incorrect to require every supported trace atom in
the ambient partition to have at most `budget` candidates.  This module keeps
the exact all-history partition (including the invalid atom and oversized
supported atoms), but assigns an empty candidate set to an oversized atom.

Consequently the coordinate product is requested only on genuinely eligible
`(trace,S)` atoms.  A later staged overflow event proves that the filtered
transition enters one of those eligible atoms; no probability estimate is an
input here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZEligibleOrientedAllCreationStoppedCandidateFamily

open CappedCoordinateMassCertificate HLOZPathEvents
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The actual fixed candidate set on an ambient stopped history.  Invalid
and oversized atoms remain in the partition, but have no candidates. -/
def eligibleHistoryCandidates
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    History t o m k supportAt → Finset Point
  | none => ∅
  | some eta => if eta.1.2.card ≤ budget then eta.1.2 else ∅

@[simp] theorem eligibleHistoryCandidates_none
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    eligibleHistoryCandidates t o m k budget supportAt none = ∅ := rfl

theorem eligibleHistoryCandidates_some_of_card_le
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (eta : SupportedIndex t o m k supportAt)
    (hcard : eta.1.2.card ≤ budget) :
    eligibleHistoryCandidates t o m k budget supportAt (some eta) =
      eta.1.2 := by
  simp [eligibleHistoryCandidates, hcard]

theorem mem_eligibleHistoryCandidates_some_iff
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (eta : SupportedIndex t o m k supportAt) (x : Point) :
    x ∈ eligibleHistoryCandidates t o m k budget supportAt (some eta) ↔
      eta.1.2.card ≤ budget ∧ x ∈ eta.1.2 := by
  simp only [eligibleHistoryCandidates]
  by_cases hcard : eta.1.2.card ≤ budget
  · simp [hcard]
  · simp [hcard]

/-- Honest low-coordinate data: refinements are needed only when the exact
candidate support obeys the fixed budget. -/
structure EligibleOrientedAllCreationLowCoordinateData
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (previous : Set WalkPath) (ratio : ℝ≥0∞) where
  supportAt : WalkPath → ℕ → Finset Point
  supportData : OrientedAllCreationSupportSelectorData t o m k supportAt
  previous_measurable : MeasurableSet previous
  ratio_ne_top : ratio ≠ ∞
  near : SupportedIndex t o m k supportAt → Point → Set WalkPath
  near_measurable : ∀ eta x, MeasurableSet (near eta x)
  refinement : ∀ (eta : SupportedIndex t o m k supportAt) (x : Point),
    eta.1.2.card ≤ budget → x ∈ eta.1.2 →
      OrientedAllCreationConditionalRefinementData
        ((orientedAllCreationConcreteFamily
          t o m k supportAt supportData).fiber eta)
        (historyPiece t o m k supportAt previous (some eta))
        (historyPiece t o m k supportAt previous (some eta) ∩ near eta x)
        ratio

namespace EligibleOrientedAllCreationLowCoordinateData

noncomputable def concreteFamily
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : EligibleOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily
      t o m k data.supportAt :=
  orientedAllCreationConcreteFamily
    t o m k data.supportAt data.supportData

def historyNear
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : EligibleOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    History t o m k data.supportAt → Point → Set WalkPath
  | none, _ => ∅
  | some eta, x => data.near eta x

/-- The source-correct all-history candidate family.  Ineligible histories
are present as pieces and hence do not create a false partition gap. -/
noncomputable def family
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : EligibleOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    StoppedHistoryCandidateFamily
      (History t o m k data.supportAt) Point previous budget ratio where
  piece := historyPiece t o m k data.supportAt previous
  candidates := eligibleHistoryCandidates
    t o m k budget data.supportAt
  near := data.historyNear
  piece_pairwise := historyPiece_pairwise
    t o m k data.supportAt previous
  piece_measurable := measurableSet_historyPiece
    t o m k data.supportAt previous data.previous_measurable data.concreteFamily
  piece_union := iUnion_historyPiece t o m k data.supportAt previous
  candidate_card := by
    intro h
    cases h with
    | none => simp [eligibleHistoryCandidates]
    | some eta =>
        by_cases hcard : eta.1.2.card ≤ budget
        · simp [eligibleHistoryCandidates, hcard]
        · simp [eligibleHistoryCandidates, hcard]
  coordinate_ratio := by
    intro h x hx
    cases h with
    | none => simp [eligibleHistoryCandidates] at hx
    | some eta =>
        have heligible := (mem_eligibleHistoryCandidates_some_iff
          t o m k budget data.supportAt eta x).mp hx
        exact coordinate_ratio_of_coordinateMassSpec
          (measurableSet_historyPiece t o m k data.supportAt previous
            data.previous_measurable data.concreteFamily (some eta))
          (data.near_measurable eta x) data.ratio_ne_top
          (coordinateMassSpecOfAllCreation
            (data.concreteFamily.fiber eta)
            (data.refinement eta x heligible.1 heligible.2))

/-- Exact deterministic containment in the eligible candidate union. -/
theorem next_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous next : Set WalkPath} {ratio : ℝ≥0∞}
    (data : EligibleOrientedAllCreationLowCoordinateData
      t o m k budget previous ratio)
    (hnext : ∀ s ∈ next,
      ∃ (eta : SupportedIndex t o m k data.supportAt) (x : Point),
        s ∈ historyPiece t o m k data.supportAt previous (some eta) ∧
        eta.1.2.card ≤ budget ∧ x ∈ eta.1.2 ∧ s ∈ data.near eta x) :
    next ⊆ data.family.someCandidate := by
  intro s hs
  rcases hnext s hs with ⟨eta, x, hpiece, hcard, hx, hnear⟩
  have hx' : x ∈ eligibleHistoryCandidates
      t o m k budget data.supportAt (some eta) :=
    (mem_eligibleHistoryCandidates_some_iff
      t o m k budget data.supportAt eta x).2 ⟨hcard, hx⟩
  exact Set.mem_iUnion_of_mem (some eta)
    (Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx' ⟨hpiece, hnear⟩))

end EligibleOrientedAllCreationLowCoordinateData

end

end Erdos1165.HLOZEligibleOrientedAllCreationStoppedCandidateFamily
