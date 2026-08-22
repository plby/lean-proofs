/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZOrientedAllCreationStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZSourceTransportCoordinateMass

/-!
# Transport and disjoint recombination of stopped-candidate families

The opposite dominant source is a complete-path pullback through checker
recentering or column reflection.  It is not an identification of retained
words on the original path.  This file transports an already constructed
physical-prefix stopped-candidate family by that literal pullback.  The
simple-random-walk law of the source table transports every coordinate ratio
exactly.

The second construction recombines countably many source rows whose past
events are disjoint.  Since each history belongs to exactly one row, the
per-history candidate budget is unchanged; there is no extra union-bound
factor for the number of source normalizations.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceTransportStoppedCandidateFamily

open HLOZSourceCorrectFutureTransition
open HLOZSourceEndpointTransportTable HLOZSourceTransportCoordinateMass
open HLOZStoppedHistoryCandidateFuture

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Literal pullback of a stopped-history candidate family through one row
of the normalized endpoint transport table.  Measurability of the narrow
events is explicit because it is exactly what the source-law pullback needs;
the older abstract candidate-family record only stores their measure bound. -/
noncomputable def stoppedHistoryCandidateFamilySourceTransport
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (family : StoppedHistoryCandidateFamily
      History Candidate previous budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    StoppedHistoryCandidateFamily History Candidate
      (sourceTransportPreimage t cls previous) budget ratio where
  piece := fun h ↦ sourceTransportPreimage t cls (family.piece h)
  candidates := family.candidates
  near := fun h x ↦ sourceTransportPreimage t cls (family.near h x)
  piece_pairwise := by
    intro h h' hne
    rw [Set.disjoint_left]
    intro s hs hs'
    exact Set.disjoint_left.mp (family.piece_pairwise hne)
      hs hs'
  piece_measurable := fun h ↦
    (family.piece_measurable h).preimage
      (measurable_sourceTransportPath t cls)
  piece_union := by
    ext s
    simp only [sourceTransportPreimage, Set.mem_iUnion,
      Set.mem_preimage]
    simpa only [Set.mem_iUnion] using
      Set.ext_iff.mp family.piece_union
        (sourceTransportPath t cls s)
  candidate_card := family.candidate_card
  coordinate_ratio := by
    intro h x hx
    have hpieceNear : MeasurableSet
        (family.piece h ∩ family.near h x) :=
      (family.piece_measurable h).inter (near_measurable h x)
    have hleft := simpleRandomWalk_preimage_sourceTransportPath
      t cls hpieceNear
    have hright := simpleRandomWalk_preimage_sourceTransportPath
      t cls (family.piece_measurable h)
    change simpleRandomWalk
        (sourceTransportPath t cls ⁻¹'
          (family.piece h ∩ family.near h x)) ≤
      ratio * simpleRandomWalk
        (sourceTransportPath t cls ⁻¹' family.piece h)
    rw [hleft, hright]
    exact family.coordinate_ratio h x hx

namespace StoppedHistoryCandidateFamily

/-- The some-candidate event commutes exactly with a complete-path source
pullback. -/
theorem someCandidate_sourceTransport
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (family : StoppedHistoryCandidateFamily
      History Candidate previous budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    (stoppedHistoryCandidateFamilySourceTransport
      t cls family near_measurable).someCandidate =
      sourceTransportPreimage t cls family.someCandidate := by
  ext s
  simp only [StoppedHistoryCandidateFamily.someCandidate,
    stoppedHistoryCandidateFamilySourceTransport,
    sourceTransportPreimage, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_preimage]

end StoppedHistoryCandidateFamily

/-! ## Disjoint recombination of normalized source rows -/

/-- Every history piece lies in the past event partitioned by its family. -/
theorem piece_subset_previous
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily
      History Candidate previous budget ratio) (h : History) :
    family.piece h ⊆ previous := by
  intro s hs
  apply (Set.ext_iff.mp family.piece_union s).mp
  exact Set.mem_iUnion_of_mem h hs

/-- Data for a disjoint collection of source-normalized candidate rows.
The history carrier may depend on the row (canonical, checker-recentered, or
column-reflected). -/
structure DisjointSourceCandidateRows
    (Source : Type*) [Countable Source]
    (History : Source → Type*) [∀ source, Countable (History source)]
    (Candidate : Type*) (previous : Set WalkPath)
    (budget : ℕ) (ratio : ℝ≥0∞) where
  rowPrevious : Source → Set WalkPath
  row : ∀ source, StoppedHistoryCandidateFamily
    (History source) Candidate (rowPrevious source) budget ratio
  previous_pairwise : Pairwise fun source source' ↦
    Disjoint (rowPrevious source) (rowPrevious source')
  previous_union : (⋃ source, rowPrevious source) = previous

namespace DisjointSourceCandidateRows

/-- Recombine genuinely disjoint normalized source rows into one candidate
family on the original past.  The dependent sum records which complete-path
normalization produced the stopped history. -/
noncomputable def family
    {Source : Type*} [Countable Source]
    {History : Source → Type*} [∀ source, Countable (History source)]
    {Candidate : Type*} {previous : Set WalkPath}
    {budget : ℕ} {ratio : ℝ≥0∞}
    (data : DisjointSourceCandidateRows
      Source History Candidate previous budget ratio) :
    StoppedHistoryCandidateFamily (Σ source, History source) Candidate
      previous budget ratio where
  piece := fun h ↦ (data.row h.1).piece h.2
  candidates := fun h ↦ (data.row h.1).candidates h.2
  near := fun h x ↦ (data.row h.1).near h.2 x
  piece_pairwise := by
    intro h h' hne
    rcases h with ⟨source, h⟩
    rcases h' with ⟨source', h'⟩
    by_cases hs : source = source'
    · cases hs
      have htail : h ≠ h' := by
        intro heq
        subst h'
        apply hne
        rfl
      exact (data.row source).piece_pairwise htail
    · exact Disjoint.mono
        (piece_subset_previous (data.row source) h)
        (piece_subset_previous (data.row source') h')
        (data.previous_pairwise hs)
  piece_measurable := fun h ↦ (data.row h.1).piece_measurable h.2
  piece_union := by
    apply Set.Subset.antisymm
    · intro s hs
      rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
      apply (Set.ext_iff.mp data.previous_union s).mp
      exact Set.mem_iUnion_of_mem h.1
        (piece_subset_previous (data.row h.1) h.2 hh)
    · intro s hs
      have hs' := (Set.ext_iff.mp data.previous_union s).mpr hs
      rcases Set.mem_iUnion.mp hs' with ⟨source, hsSource⟩
      have hsRow := (Set.ext_iff.mp
        (data.row source).piece_union s).mpr hsSource
      rcases Set.mem_iUnion.mp hsRow with ⟨h, hh⟩
      exact Set.mem_iUnion_of_mem ⟨source, h⟩ hh
  candidate_card := fun h ↦ (data.row h.1).candidate_card h.2
  coordinate_ratio := fun h x hx ↦
    (data.row h.1).coordinate_ratio h.2 x hx

/-- Recombination changes only the stopped-history tag: its some-candidate
event is the union of the rowwise some-candidate events. -/
theorem someCandidate_family
    {Source : Type*} [Countable Source]
    {History : Source → Type*} [∀ source, Countable (History source)]
    {Candidate : Type*} {previous : Set WalkPath}
    {budget : ℕ} {ratio : ℝ≥0∞}
    (data : DisjointSourceCandidateRows
      Source History Candidate previous budget ratio) :
    data.family.someCandidate = ⋃ source, (data.row source).someCandidate := by
  ext s
  simp only [StoppedHistoryCandidateFamily.someCandidate, family,
    Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨h, x, hx, hs⟩
    exact ⟨h.1, h.2, x, hx, hs⟩
  · rintro ⟨source, h, x, hx, hs⟩
    exact ⟨⟨source, h⟩, x, hx, hs⟩

/-- Add the one later atomwise escape factor only after all normalized source
rows have been pulled back and recombined. -/
noncomputable def factor
    {Index State : Type} [Countable Index] [Countable State]
    {Source : Type*} [Countable Source]
    {History : Source → Type*} [∀ source, Countable (History source)]
    {Candidate : Type*} {previous next : Set WalkPath}
    {budget : ℕ} {ratio escapeCost q : ℝ≥0∞}
    (data : DisjointSourceCandidateRows
      Source History Candidate previous budget ratio)
    (escape : CountableAtomFutureFactor Index State
      data.family.someCandidate next escapeCost)
    (cost_le : (budget : ℝ≥0∞) * ratio * escapeCost ≤ q) :
    SourceCorrectTransitionFactor (Σ source, History source)
      Candidate State previous next q :=
  .lowAtomwise budget ratio escapeCost
    { candidate := data.family, escape := escape } cost_le

end DisjointSourceCandidateRows

end

end Erdos1165.HLOZSourceTransportStoppedCandidateFamily
