/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZStoppedHistoryCandidateFuture

/-!
# Restricting a stopped-candidate partition to an actual past event

A transported source row naturally partitions all paths.  Its conditional
coordinate estimate remains valid after restricting to a spatial past only
on atoms which are wholly contained in that past.  This module implements
that exact operation.  Other atoms remain in the stopped partition but are
assigned the empty candidate set.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZStoppedCandidatePreviousRestriction

open HLOZPathEvents HLOZStoppedHistoryCandidateFuture

noncomputable section

/-- Keep the candidates of an ambient stopped history precisely when the
whole history piece lies in `previous`. -/
noncomputable def candidatesInPrevious
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (ambient : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (previous : Set WalkPath) (h : History) : Finset Candidate := by
  classical
  exact if ambient.piece h ⊆ previous then ambient.candidates h else ∅

theorem mem_candidatesInPrevious_iff
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (ambient : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (previous : Set WalkPath) (h : History) (x : Candidate) :
    x ∈ candidatesInPrevious ambient previous h ↔
      ambient.piece h ⊆ previous ∧ x ∈ ambient.candidates h := by
  classical
  unfold candidatesInPrevious
  by_cases hpiece : ambient.piece h ⊆ previous
  · simp [hpiece]
  · simp [hpiece]

/-- Restrict an ambient all-path stopped partition to `previous`.  The
coordinate law is used only on atoms absorbed by `previous`; this is the
source-correct replacement for an invariance assumption on the whole past. -/
noncomputable def restrictToPrevious
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (ambient : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous) :
    StoppedHistoryCandidateFamily History Candidate previous budget ratio where
  piece := fun h ↦ previous ∩ ambient.piece h
  candidates := candidatesInPrevious ambient previous
  near := ambient.near
  piece_pairwise := by
    intro h h' hne
    exact (ambient.piece_pairwise hne).mono inter_subset_right
      inter_subset_right
  piece_measurable := fun h ↦ hprevious.inter (ambient.piece_measurable h)
  piece_union := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨h, hh⟩
      exact hh.1
    · intro hs
      have hall : s ∈ (Set.univ : Set WalkPath) := Set.mem_univ s
      have hambient := (Set.ext_iff.mp ambient.piece_union s).mpr hall
      rcases Set.mem_iUnion.mp hambient with ⟨h, hh⟩
      exact Set.mem_iUnion.mpr ⟨h, hs, hh⟩
  candidate_card := by
    intro h
    classical
    by_cases hpiece : ambient.piece h ⊆ previous
    · simpa [candidatesInPrevious, hpiece] using ambient.candidate_card h
    · simp [candidatesInPrevious, hpiece]
  coordinate_ratio := by
    intro h x hx
    have heligible :=
      (mem_candidatesInPrevious_iff ambient previous h x).mp hx
    have hpiece : previous ∩ ambient.piece h = ambient.piece h := by
      exact inter_eq_right.mpr heligible.1
    rw [hpiece]
    exact ambient.coordinate_ratio h x heligible.2

namespace StoppedHistoryCandidateFamily

/-- A concrete ambient candidate witness enters the restricted family once
its entire stopped atom is known to lie in the actual past. -/
theorem mem_someCandidate_restrictToPrevious
    {History Candidate : Type*} [Countable History]
    {budget : ℕ} {ratio : ℝ≥0∞}
    (ambient : StoppedHistoryCandidateFamily History Candidate Set.univ
      budget ratio)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (h : History) (x : Candidate)
    (hpiece : ambient.piece h ⊆ previous)
    {s : WalkPath} (hsPiece : s ∈ ambient.piece h)
    (hx : x ∈ ambient.candidates h) (hsNear : s ∈ ambient.near h x) :
    s ∈ (restrictToPrevious ambient previous hprevious).someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate
  exact Set.mem_iUnion_of_mem h <| Set.mem_iUnion_of_mem x <|
    Set.mem_iUnion_of_mem
      ((mem_candidatesInPrevious_iff ambient previous h x).2 ⟨hpiece, hx⟩)
      ⟨⟨hpiece hsPiece, hsPiece⟩, hsNear⟩

end StoppedHistoryCandidateFamily

end

end Erdos1165.HLOZStoppedCandidatePreviousRestriction
