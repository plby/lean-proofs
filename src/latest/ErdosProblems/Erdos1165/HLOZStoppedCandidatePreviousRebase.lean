/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Rebasing a stopped candidate family to a larger ambient past

A source-normalized family may naturally partition a proper good-history
event, while the strong-Markov transition factor must start from the complete
rankwise past.  This module adds one null history for the complement and keeps
the candidates of a source atom only when that entire atom is absorbed by the
new past.  Thus no conditional ratio is asserted on a partially cut atom.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZStoppedCandidatePreviousRebase

open HLOZStoppedHistoryCandidateFuture

noncomputable section

theorem piece_subset_previous
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio) (h : History) :
    family.piece h ⊆ oldPrevious := by
  intro s hs
  apply (Set.ext_iff.mp family.piece_union s).mp
  exact Set.mem_iUnion_of_mem h hs

/-- Candidate set retained on an old atom precisely when that entire atom is
contained in the new past. -/
noncomputable def rebasedCandidates
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio) (previous : Set WalkPath) :
    Option History → Finset Candidate := by
  classical
  intro h
  cases h with
  | none => exact ∅
  | some h =>
      exact if family.piece h ⊆ previous then family.candidates h else ∅

theorem mem_rebasedCandidates_some_iff
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio) (previous : Set WalkPath) (h : History) (x : Candidate) :
    x ∈ rebasedCandidates family previous (some h) ↔
      family.piece h ⊆ previous ∧ x ∈ family.candidates h := by
  classical
  unfold rebasedCandidates
  by_cases hpiece : family.piece h ⊆ previous
  · simp [hpiece]
  · simp [hpiece]

/-- Rebase a source family to `previous`.  The `none` history covers the
part of `previous` outside the old source past. -/
noncomputable def rebaseToPrevious
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous) :
    StoppedHistoryCandidateFamily (Option History) Candidate previous
      budget ratio where
  piece
    | none => previous \ oldPrevious
    | some h => previous ∩ family.piece h
  candidates := rebasedCandidates family previous
  near
    | none, _ => ∅
    | some h, x => family.near h x
  piece_pairwise := by
    intro h h' hne
    cases h with
    | none =>
        cases h' with
        | none => exact (hne rfl).elim
        | some h' =>
            rw [Set.disjoint_left]
            intro s hs hs'
            exact hs.2 (piece_subset_previous family h' hs'.2)
    | some h =>
        cases h' with
        | none =>
            rw [Set.disjoint_left]
            intro s hs hs'
            exact hs'.2 (piece_subset_previous family h hs.2)
        | some h' =>
            have hhh : h ≠ h' := by
              intro heq
              subst h'
              exact hne rfl
            exact (family.piece_pairwise hhh).mono inter_subset_right
              inter_subset_right
  piece_measurable := by
    intro h
    cases h with
    | none =>
        have hold : MeasurableSet oldPrevious := by
          rw [← family.piece_union]
          exact MeasurableSet.iUnion family.piece_measurable
        exact hprevious.diff hold
    | some h => exact hprevious.inter (family.piece_measurable h)
  piece_union := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
      cases h with
      | none => exact hh.1
      | some _h => exact hh.1
    · intro hs
      by_cases hold : s ∈ oldPrevious
      · have hunion := (Set.ext_iff.mp family.piece_union s).mpr hold
        rcases Set.mem_iUnion.mp hunion with ⟨h, hh⟩
        exact Set.mem_iUnion_of_mem (some h) ⟨hs, hh⟩
      · exact Set.mem_iUnion_of_mem none ⟨hs, hold⟩
  candidate_card := by
    intro h
    cases h with
    | none => simp [rebasedCandidates]
    | some h =>
        classical
        by_cases hpiece : family.piece h ⊆ previous
        · simpa [rebasedCandidates, hpiece] using family.candidate_card h
        · simp [rebasedCandidates, hpiece]
  coordinate_ratio := by
    intro h x hx
    cases h with
    | none => simp [rebasedCandidates] at hx
    | some h =>
        have heligible :=
          (mem_rebasedCandidates_some_iff family previous h x).mp hx
        have hpiece : previous ∩ family.piece h = family.piece h :=
          inter_eq_right.mpr heligible.1
        change simpleRandomWalk
            ((previous ∩ family.piece h) ∩ family.near h x) ≤
          ratio * simpleRandomWalk (previous ∩ family.piece h)
        rw [hpiece]
        exact family.coordinate_ratio h x heligible.2

namespace StoppedHistoryCandidateFamily

/-- Every rebased candidate witness still lies in the original source past. -/
theorem someCandidate_rebaseToPrevious_subset_oldPrevious
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous) :
    (rebaseToPrevious family previous hprevious).someCandidate ⊆
      oldPrevious := by
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨x, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hx, hs⟩
  cases h with
  | none =>
      change x ∈ (∅ : Finset Candidate) at hx
      simp at hx
  | some h => exact piece_subset_previous family h hs.1.2

/-- A concrete old-family candidate witness enters the rebased family once
its entire stopped atom lies in the new past. -/
theorem mem_someCandidate_rebaseToPrevious
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (h : History) (x : Candidate)
    (hpiece : family.piece h ⊆ previous)
    {s : WalkPath} (hsPiece : s ∈ family.piece h)
    (hx : x ∈ family.candidates h) (hsNear : s ∈ family.near h x) :
    s ∈ (rebaseToPrevious family previous hprevious).someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate
  exact Set.mem_iUnion_of_mem (some h) <| Set.mem_iUnion_of_mem x <|
    Set.mem_iUnion_of_mem
      ((mem_rebasedCandidates_some_iff family previous h x).2
        ⟨hpiece, hx⟩)
      ⟨⟨hpiece hsPiece, hsPiece⟩, hsNear⟩

/-- If the whole old source past lies in the new past, every old candidate
witness survives rebasing. -/
theorem someCandidate_subset_rebaseToPrevious_of_subset
    {History Candidate : Type*} [Countable History]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hold : oldPrevious ⊆ previous) :
    family.someCandidate ⊆
      (rebaseToPrevious family previous hprevious).someCandidate := by
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨x, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hx, hs⟩
  exact mem_someCandidate_rebaseToPrevious family previous hprevious h x
    ((piece_subset_previous family h).trans hold) hs.1 hx hs.2

/-- The rebased some-candidate event is measurable whenever the old narrow
events are measurable. -/
theorem measurableSet_someCandidate_rebaseToPrevious
    {History Candidate : Type*} [Countable History] [Countable Candidate]
    {oldPrevious : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate oldPrevious
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hnear : ∀ h x, MeasurableSet (family.near h x)) :
    MeasurableSet
      (rebaseToPrevious family previous hprevious).someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate
  apply MeasurableSet.iUnion
  intro h
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro _hx
  apply (rebaseToPrevious family previous hprevious).piece_measurable h |>.inter
  cases h with
  | none => exact MeasurableSet.empty
  | some h => exact hnear h x

end StoppedHistoryCandidateFamily

end

end Erdos1165.HLOZStoppedCandidatePreviousRebase
