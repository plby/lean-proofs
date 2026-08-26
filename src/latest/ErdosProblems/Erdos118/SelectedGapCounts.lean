import ErdosProblems.Erdos118.GapPrefixes
import ErdosProblems.Erdos118.ProjectionBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
An explicit finite bijection between occupied ordinary gaps and the exact
selected body/entry indices. Representatives come from the proved unique
interior-prefix parsing theorem, not from an assumed counting formula.
-/

namespace Erdos118.SelectedGapCounts

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices GapCounts GapPrefixes

def selected (S : Stem) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range S.bodyLabels.length).sigma fun i ↦ (S.bodyLabels.getD i []).toFinset

theorem mem_selected (S : Stem) (i j : ℕ) :
    ⟨i, j⟩ ∈ selected S ↔ ∃ hi : i < S.bodyLabels.length, j ∈ S.bodyLabels[i] := by
  simp only [selected, Finset.mem_sigma, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨hi, hj⟩
    exact ⟨hi, by simpa only [List.getD_eq_getElem _ _ hi] using hj⟩
  · rintro ⟨hi, hj⟩
    exact ⟨hi, by simpa only [List.getD_eq_getElem _ _ hi] using hj⟩

theorem interior_prefix_root {P : InteriorWords.Position} {S : Stem}
    (hp : P.word <+: S.ordinary) : P.root = S.root := by
  exact (List.cons_prefix_cons.mp hp).1

theorem interior_prefix_body_bound {P : InteriorWords.Position} {S : Stem}
    (hfull : S.done.length = S.root) (hp : P.word <+: S.ordinary) :
    P.done.length < S.bodyLabels.length := by
  have hroom := P.room
  rw [interior_prefix_root hp, ← hfull] at hroom
  simpa only [Stem.bodyLabels, List.length_map] using
    Nat.lt_trans (Nat.lt_succ_self P.done.length) hroom

private theorem interior_word_length_pos (P : InteriorWords.Position) : 0 < P.word.length := by
  simp only [InteriorWords.Position.word, PartialWordResponses.partialWord, List.length_cons]
  omega

theorem gaps_card_eq_selected (S T : Stem) (hfull : S.done.length = S.root)
    (hd : S.ordinary.Disjoint T.ordinary) (hinterior : InteriorCuts S T)
    (hexact : ExactAnnotations S T) : (gaps S.ordinary T.ordinary).card = (selected S).card := by
  classical
  have exists_parse : ∀ k, k ∈ gaps S.ordinary T.ordinary → ∃ P : InteriorWords.Position,
      P.word <+: S.ordinary ∧ P.word.length = k + 1 ∧
        Cut S T P.done.length P.entries.length := by
    intro k hk
    exact (gap_iff_cut_length S T hd hinterior k).mp ((mem_gaps _ _ _).mp hk)
  let parse := fun k hk ↦ (exists_parse k hk).choose
  have spec : ∀ k hk, (parse k hk).word <+: S.ordinary ∧ (parse k hk).word.length = k + 1 ∧
      Cut S T (parse k hk).done.length (parse k hk).entries.length := by
    intro k hk
    exact (exists_parse k hk).choose_spec
  apply Finset.card_bij (fun k hk ↦ ⟨(parse k hk).done.length, (parse k hk).entries.length⟩)
  · intro k hk
    apply (mem_selected _ _ _).mpr
    have hi := interior_prefix_body_bound hfull (spec k hk).1
    exact ⟨hi, (hexact.body _ hi _).mpr (spec k hk).2.2⟩
  · intro k hk l hl he
    have hi := congrArg Sigma.fst he
    have hj := congrArg (fun x : Σ _ : ℕ, ℕ ↦ x.2) he
    have hP := SkippedCuts.interior_common_prefix_same_indices
      (spec k hk).1 (spec l hl).1 hi hj
    have hlen := congrArg (fun P : InteriorWords.Position ↦ P.word.length) hP
    rw [(spec k hk).2.1, (spec l hl).2.1] at hlen
    omega
  · intro a ha
    obtain ⟨hi, hj⟩ := (mem_selected S a.1 a.2).mp ha
    obtain ⟨y, hy, hproper, P, hP, hpi, hpj⟩ := (hexact.body _ hi _).mp hj
    have hp : P.word <+: S.ordinary := by
      rw [hP]
      exact List.takeWhile_prefix _
    have hpos := interior_word_length_pos P
    let k := P.word.length - 1
    have hlen : P.word.length = k + 1 := by dsimp [k]; omega
    have hcut : Cut S T P.done.length P.entries.length :=
      ⟨y, hy, hproper, P, hP, rfl, rfl⟩
    have hk : k ∈ gaps S.ordinary T.ordinary :=
      (mem_gaps _ _ _).mpr ((gap_iff_cut_length S T hd hinterior k).mpr ⟨P, hp, hlen, hcut⟩)
    refine ⟨k, hk, ?_⟩
    have he := interior_prefix_length_injective (spec k hk).1 hp
      ((spec k hk).2.1.trans hlen.symm)
    change (⟨(parse k hk).done.length, (parse k hk).entries.length⟩ : Σ _ : ℕ, ℕ) = a
    rw [he, hpi, hpj]

theorem selected_card (S : Stem) :
    (selected S).card = ∑ i ∈ Finset.range S.bodyLabels.length,
      (S.bodyLabels.getD i []).length := by
  rw [selected, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  have hilt := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ hilt]
  exact List.toFinset_card_of_nodup (ProjectionBounds.body_label_pairwise S i hilt).nodup

end Erdos118.SelectedGapCounts
