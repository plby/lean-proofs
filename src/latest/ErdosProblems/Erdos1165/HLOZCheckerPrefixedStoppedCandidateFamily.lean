/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerPrefixedCylinderTransport
import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Fixed-prefix checker transport of stopped-candidate families

Deleting and recentering the first checker step preserves the walk law only
after summing over its four possible directions.  At the stopped-fibre level
the physical direction must remain part of the history.  Each fixed-prefix
cylinder contributes the same factor `1 / 4`, which cancels exactly in the
conditional coordinate ratio.  A null history covers non-walk-path prefixes.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerPrefixedStoppedCandidateFamily

open HLOZCheckerPrefixedCylinderTransport HLOZPathEvents
open HLOZStoppedHistoryCandidateFuture

noncomputable section

/-- Histories after checker recentering, retaining the deleted physical
direction.  `none` is the invalid-first-step complement. -/
abbrev CheckerPrefixedHistory (History : Type*) :=
  Option (Direction × History)

private def validFirstDirectionWalk : Set WalkPath :=
  ⋃ d : Direction, firstDirectionWalk d

private theorem measurableSet_validFirstDirectionWalk :
    MeasurableSet validFirstDirectionWalk := by
  exact MeasurableSet.iUnion measurableSet_firstDirectionWalk

private theorem firstDirectionWalk_disjoint
    {d d' : Direction} (hne : d ≠ d') :
    Disjoint (firstDirectionWalk d) (firstDirectionWalk d') := by
  rw [Set.disjoint_left]
  intro s hs hs'
  apply hne
  apply directionVector_injective
  exact hs.symm.trans hs'

/-- Prefix-sensitive transport of an ambient all-path candidate family. -/
noncomputable def checkerPrefixedFamily
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    StoppedHistoryCandidateFamily (CheckerPrefixedHistory History) Candidate
      Set.univ budget ratio where
  piece
    | none => validFirstDirectionWalkᶜ
    | some (d, h) => checkerPrefixedPreimage d (family.piece h)
  candidates
    | none => ∅
    | some (_, h) => family.candidates h
  near
    | none, _ => ∅
    | some (d, h), x => checkerPrefixedPreimage d (family.near h x)
  piece_pairwise := by
    intro h h' hne
    cases h with
    | none =>
        cases h' with
        | none => exact (hne rfl).elim
        | some dh =>
            exact Set.disjoint_left.mpr fun _ hs hs' ↦
              hs (Set.mem_iUnion_of_mem dh.1 hs'.1)
    | some dh =>
        cases h' with
        | none =>
            exact Set.disjoint_left.mpr fun _ hs hs' ↦
              hs' (Set.mem_iUnion_of_mem dh.1 hs.1)
        | some dh' =>
            rcases dh with ⟨d, h⟩
            rcases dh' with ⟨d', h'⟩
            by_cases hd : d = d'
            · subst d'
              have hh : h ≠ h' := by
                intro heq
                apply hne
                subst h'
                rfl
              exact Set.disjoint_left.mpr fun _ hs hs' ↦
                Set.disjoint_left.mp (family.piece_pairwise hh)
                  hs.2 hs'.2
            · exact Set.disjoint_left.mpr fun _ hs hs' ↦
                Set.disjoint_left.mp (firstDirectionWalk_disjoint (by
                  exact hd))
                  hs.1 hs'.1
  piece_measurable := by
    intro h
    cases h with
    | none => exact measurableSet_validFirstDirectionWalk.compl
    | some dh =>
        exact measurableSet_checkerPrefixedPreimage
          (family.piece_measurable dh.2) dh.1
  piece_union := by
    ext s
    constructor
    · intro _
      exact Set.mem_univ s
    · intro _
      by_cases hvalid : s ∈ validFirstDirectionWalk
      · rcases Set.mem_iUnion.mp hvalid with ⟨d, hd⟩
        have hall : oneStepRecenter s ∈ (Set.univ : Set WalkPath) :=
          Set.mem_univ _
        have hunion := (Set.ext_iff.mp family.piece_union
          (oneStepRecenter s)).mpr hall
        rcases Set.mem_iUnion.mp hunion with ⟨h, hh⟩
        exact Set.mem_iUnion_of_mem (some (d, h)) ⟨hd, hh⟩
      · exact Set.mem_iUnion_of_mem none hvalid
  candidate_card := by
    intro h
    cases h with
    | none => simp
    | some dh => exact family.candidate_card dh.2
  coordinate_ratio := by
    intro h x hx
    cases h with
    | none => simp at hx
    | some dh =>
        have hpieceNear : MeasurableSet
            (family.piece dh.2 ∩ family.near dh.2 x) :=
          (family.piece_measurable dh.2).inter
            (near_measurable dh.2 x)
        have hn := simpleRandomWalk_checkerPrefixedPreimage dh.1 hpieceNear
        have hd := simpleRandomWalk_checkerPrefixedPreimage dh.1
          (family.piece_measurable dh.2)
        have hset : checkerPrefixedPreimage dh.1 (family.piece dh.2) ∩
              checkerPrefixedPreimage dh.1 (family.near dh.2 x) =
            checkerPrefixedPreimage dh.1
              (family.piece dh.2 ∩ family.near dh.2 x) := by
          ext s
          simp only [checkerPrefixedPreimage, Set.mem_inter_iff,
            Set.mem_preimage]
          tauto
        rw [hset, hn, hd]
        calc
          (1 / 4 : ℝ≥0∞) *
                simpleRandomWalk (family.piece dh.2 ∩ family.near dh.2 x) ≤
              (1 / 4 : ℝ≥0∞) *
                (ratio * simpleRandomWalk (family.piece dh.2)) := by
            gcongr
            exact family.coordinate_ratio dh.2 x hx
          _ = ratio * ((1 / 4 : ℝ≥0∞) *
                simpleRandomWalk (family.piece dh.2)) := by ac_rfl

namespace StoppedHistoryCandidateFamily

/-- The some-candidate event is the finite-prefix pullback of the target
candidate event, with the invalid-prefix history contributing nothing. -/
theorem someCandidate_checkerPrefixedFamily
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (near_measurable : ∀ h x, MeasurableSet (family.near h x)) :
    (checkerPrefixedFamily family near_measurable).someCandidate =
      ⋃ d : Direction, checkerPrefixedPreimage d family.someCandidate := by
  ext s
  simp only [StoppedHistoryCandidateFamily.someCandidate,
    checkerPrefixedFamily, Set.mem_iUnion, Set.mem_inter_iff,
    checkerPrefixedPreimage, Set.mem_preimage]
  constructor
  · rintro ⟨h, x, hx, hpiece, hnear⟩
    cases h with
    | none => simp at hx
    | some dh =>
        exact ⟨dh.1, hpiece.1, dh.2, x, hx, hpiece.2, hnear.2⟩
  · rintro ⟨d, hd, h, x, hx, hpiece, hnear⟩
    exact ⟨some (d, h), x, hx, ⟨hd, hpiece⟩, hd, hnear⟩

end StoppedHistoryCandidateFamily

end

end Erdos1165.HLOZCheckerPrefixedStoppedCandidateFamily
