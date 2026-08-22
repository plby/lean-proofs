/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily
import ErdosProblems.Erdos1165.HLOZAllCreationCanonicalDominantWindows
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateConditionalProduct

/-!
# A stopped-candidate family from the literal all-creation fibres

This file turns the concrete physical-prefix `(trace,S)` disintegration into
the exact stopped-history object used by Proposition 4.9.  The history type
contains one explicit null/invalid atom and every nonempty supported
all-creation atom.  On a supported atom the candidate Finset is literally
the fixed `S`; hence its cardinality estimate is deterministic.

Each candidate ratio is obtained from an
`OrientedAllCreationConditionalRefinementData` on the concrete prefixed
fibre.  In particular, the refinement may use the strengthened honest
denominator from `HLOZAllCreationCanonicalDominantWindows`.  The final
constructor below adds only the separate atomwise future escape factor; no
transition inequality is an input.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZOrientedAllCreationStoppedCandidateFamily

open CappedCoordinateMassCertificate HLOZPathEvents
open HLOZSourceCorrectFutureTransition HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev SupportedIndex (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :=
  OrientedAllCreationSupportedAtomIndex t o m k supportAt

/-- The invalid/non-reaching history is `none`; every supported exact atom
is a `some` history. -/
abbrev History (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :=
  Option (SupportedIndex t o m k supportAt)

/-- Literal history piece, including the null/invalid complement required
when the preceding event is `Set.univ`. -/
def historyPiece (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (previous : Set WalkPath) :
    History t o m k supportAt → Set WalkPath
  | none => previous \ (thresholdReachStage m k ∩ validStepWalk)
  | some eta => previous ∩ orientedAllCreationSupportTraceAtom
      t o m k supportAt eta.1.1 eta.1.2

/-- The candidate set is exactly `S` on a supported history and empty on the
null history. -/
def historyCandidates (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point) :
    History t o m k supportAt → Finset Point
  | none => ∅
  | some eta => eta.1.2

theorem historyPiece_pairwise
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (previous : Set WalkPath) :
    Pairwise fun h h' : History t o m k supportAt ↦
      Disjoint (historyPiece t o m k supportAt previous h)
        (historyPiece t o m k supportAt previous h') := by
  intro h h' hne
  cases h with
  | none =>
      cases h' with
      | none => exact (hne rfl).elim
      | some eta =>
          rw [Set.disjoint_left]
          intro s hs hs'
          exact hs.2 ⟨hs'.2.1.2.1, hs'.2.1.1⟩
  | some eta =>
      cases h' with
      | none =>
          rw [Set.disjoint_left]
          intro s hs hs'
          exact hs'.2 ⟨hs.2.1.2.1, hs.2.1.1⟩
      | some eta' =>
          have hval : eta.1 ≠ eta'.1 := by
            intro heq
            apply hne
            exact congrArg some (Subtype.ext heq)
          have hdisjoint :=
            pairwise_disjoint_orientedAllCreationSupportTraceAtom
              t o m k supportAt hval
          exact Disjoint.mono inter_subset_right inter_subset_right hdisjoint

theorem measurableSet_historyPiece
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (family : OrientedAllCreationPrefixedStoppedCoordinateFamily
      t o m k supportAt)
    (h : History t o m k supportAt) :
    MeasurableSet (historyPiece t o m k supportAt previous h) := by
  cases h with
  | none =>
      exact hprevious.diff
        ((measurableSet_thresholdReachStage m k).inter
          measurableSet_validStepWalk)
  | some eta => exact hprevious.inter (family.fiber eta).atom_measurable

theorem iUnion_historyPiece
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (supportAt : WalkPath → ℕ → Finset Point)
    (previous : Set WalkPath) :
    (⋃ h : History t o m k supportAt,
      historyPiece t o m k supportAt previous h) = previous := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun h ↦ by
      cases h <;> exact inter_subset_left
  · intro s hs
    by_cases hgood : s ∈ thresholdReachStage m k ∩ validStepWalk
    · have hall := Set.ext_iff.mp
        (iUnion_supported_orientedAllCreationSupportTraceAtom
          t o m k supportAt) s
      have hu : s ∈ ⋃ eta : SupportedIndex t o m k supportAt,
          orientedAllCreationSupportTraceAtom
            t o m k supportAt eta.1.1 eta.1.2 := hall.mpr hgood
      rcases Set.mem_iUnion.mp hu with ⟨eta, heta⟩
      exact Set.mem_iUnion_of_mem (some eta) ⟨hs, heta⟩
    · exact Set.mem_iUnion_of_mem none ⟨hs, hgood⟩

/-- Concrete deterministic coordinate data for one normalized oriented
source.  Its only non-structural input is the honest per-candidate
broad/narrow refinement on the already constructed physical fibre. -/
structure OrientedAllCreationLowCoordinateData
    (t : DominoTiling) (o : Orientation) (m k budget : ℕ)
    (previous : Set WalkPath) (ratio : ℝ≥0∞) where
  supportAt : WalkPath → ℕ → Finset Point
  supportData : OrientedAllCreationSupportSelectorData t o m k supportAt
  previous_measurable : MeasurableSet previous
  ratio_ne_top : ratio ≠ ∞
  candidate_card : ∀ eta : SupportedIndex t o m k supportAt,
    eta.1.2.card ≤ budget
  near : SupportedIndex t o m k supportAt → Point → Set WalkPath
  near_measurable : ∀ eta x, MeasurableSet (near eta x)
  refinement : ∀ (eta : SupportedIndex t o m k supportAt) (x : Point),
    x ∈ eta.1.2 →
      OrientedAllCreationConditionalRefinementData
        ((orientedAllCreationConcreteFamily
          t o m k supportAt supportData).fiber eta)
        (historyPiece t o m k supportAt previous (some eta))
        (historyPiece t o m k supportAt previous (some eta) ∩ near eta x)
        ratio

namespace OrientedAllCreationLowCoordinateData

noncomputable def concreteFamily
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : OrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily
      t o m k data.supportAt :=
  orientedAllCreationConcreteFamily
    t o m k data.supportAt data.supportData

def historyNear
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : OrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    History t o m k data.supportAt → Point → Set WalkPath
  | none, _ => ∅
  | some eta, x => data.near eta x

/-- The literal all-creation stopped-history candidate family. -/
noncomputable def family
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous : Set WalkPath} {ratio : ℝ≥0∞}
    (data : OrientedAllCreationLowCoordinateData
      t o m k budget previous ratio) :
    StoppedHistoryCandidateFamily
      (History t o m k data.supportAt) Point previous budget ratio where
  piece := historyPiece t o m k data.supportAt previous
  candidates := historyCandidates t o m k data.supportAt
  near := data.historyNear
  piece_pairwise := historyPiece_pairwise
    t o m k data.supportAt previous
  piece_measurable := measurableSet_historyPiece
    t o m k data.supportAt previous data.previous_measurable data.concreteFamily
  piece_union := iUnion_historyPiece t o m k data.supportAt previous
  candidate_card := by
    intro h
    cases h with
    | none => simp [historyCandidates]
    | some eta => exact data.candidate_card eta
  coordinate_ratio := by
    intro h x hx
    cases h with
    | none => simp [historyCandidates] at hx
    | some eta =>
        exact coordinate_ratio_of_coordinateMassSpec
          (measurableSet_historyPiece t o m k data.supportAt previous
            data.previous_measurable data.concreteFamily (some eta))
          (data.near_measurable eta x) data.ratio_ne_top
          (coordinateMassSpecOfAllCreation
            (data.concreteFamily.fiber eta) (data.refinement eta x hx))

/-- A pathwise target witness enters the exact union of stopped candidates.
This is the deterministic `someCandidate` seam used before the future
strong-Markov factor. -/
theorem next_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous next : Set WalkPath} {ratio : ℝ≥0∞}
    (data : OrientedAllCreationLowCoordinateData
      t o m k budget previous ratio)
    (hnext : ∀ s ∈ next,
      ∃ (eta : SupportedIndex t o m k data.supportAt) (x : Point),
        s ∈ historyPiece t o m k data.supportAt previous (some eta) ∧
        x ∈ eta.1.2 ∧ s ∈ data.near eta x) :
    next ⊆ data.family.someCandidate := by
  intro s hs
  rcases hnext s hs with ⟨eta, x, hpiece, hx, hnear⟩
  exact Set.mem_iUnion_of_mem (some eta)
    (Set.mem_iUnion_of_mem x (Set.mem_iUnion_of_mem hx ⟨hpiece, hnear⟩))

/-- Add only the atomwise future escape and the numerical cost comparison to
the completed oriented conditional coordinate family. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {t : DominoTiling} {o : Orientation} {m k budget : ℕ}
    {previous next : Set WalkPath}
    {ratio escapeCost q : ℝ≥0∞}
    (data : OrientedAllCreationLowCoordinateData
      t o m k budget previous ratio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : (budget : ℝ≥0∞) * ratio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor
      (History t o m k data.supportAt) Point State previous next q :=
  .lowAtomwise budget ratio escapeCost
    { candidate := data.family, escape := escape } cost_le

end OrientedAllCreationLowCoordinateData

end

end Erdos1165.HLOZOrientedAllCreationStoppedCandidateFamily
