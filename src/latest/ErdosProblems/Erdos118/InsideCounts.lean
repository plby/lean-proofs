import ErdosProblems.Erdos118.SelectedGapCounts
import ErdosProblems.Erdos118.LastMarkerRefinement

/-!
Actual inside clear pairs have one more selected entry on the left.
Partitioning the selected pairs at the last selected body gives the
before-last/last-body count identity. The marker-order endgame remains
a separate game-theoretic obligation.
-/

namespace Erdos118.InsideCounts

open Negative Negative.Exact LabelledExtensions DecisionStates ClearPairs CutIndices
open GapCounts SelectedGapCounts LastBodyRefinement LastMarkerRefinement

def beforeLast (S : Completed) : ℕ :=
  ((selected S.stem).filter (fun a ↦ a.1 < lastIndex S)).card

theorem ordinary_disjoint {S T : Stem} (h : ClearPair S T) : S.ordinary.Disjoint T.ordinary := by
  intro x hx hy
  exact Finset.disjoint_left.mp h.disjoint
    (List.mem_toFinset.mpr (S.ordinary_sublist.subset hx))
    (List.mem_toFinset.mpr (T.ordinary_sublist.subset hy))

theorem selected_index_le_last (S : Completed) (T : Stem) (hexact : ExactAnnotations S.stem T)
    (hne : S.stem.rootLabel ≠ []) (a : Σ _ : ℕ, ℕ) (ha : a ∈ selected S.stem) :
    a.1 ≤ lastIndex S := by
  obtain ⟨hi, hj⟩ := (mem_selected _ _ _).mp ha
  have hcut := (hexact.body _ hi _).mp hj
  have hm := (hexact.root (a.1 + 1)).mpr ⟨a.1, a.2, hcut, rfl⟩
  have hle := (S.stem.label_pairwise.imp Nat.le_of_lt).rel_getLast hm
  have he : S.stem.rootLabel.getLastD 0 = S.stem.rootLabel.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  unfold lastIndex
  rw [he]
  omega

theorem selected_card_decomposition (S : Completed) (T : Stem)
    (hexact : ExactAnnotations S.stem T) (hne : S.stem.rootLabel ≠ []) :
    (selected S.stem).card = beforeLast S + (lastLabel S).length := by
  have hi : lastIndex S < S.stem.bodyLabels.length := by
    simpa only [Stem.bodyLabels, List.length_map] using lastIndex_lt S hne
  have hlabel : lastLabel S = S.stem.bodyLabels[lastIndex S] := by
    simp only [lastLabel, List.getElem?_eq_getElem hi, Option.getD_some]
  have hfiber : ((selected S.stem).filter (fun a ↦ ¬ a.1 < lastIndex S)).card =
      (lastLabel S).toFinset.card := by
    apply Finset.card_bij (fun a _ ↦ a.2)
    · intro a ha
      obtain ⟨ha, hnot⟩ := Finset.mem_filter.mp ha
      have he : a.1 = lastIndex S := by
        have hle := selected_index_le_last S T hexact hne a ha
        omega
      obtain ⟨hai, haj⟩ := (mem_selected _ _ _).mp ha
      apply List.mem_toFinset.mpr
      rw [hlabel]
      simpa only [he] using haj
    · intro a ha b hb he
      obtain ⟨ha, hna⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hnb⟩ := Finset.mem_filter.mp hb
      have hia : a.1 = lastIndex S := by
        have hle := selected_index_le_last S T hexact hne a ha
        omega
      have hib : b.1 = lastIndex S := by
        have hle := selected_index_le_last S T hexact hne b hb
        omega
      cases a
      cases b
      simp_all
    · intro j hj
      refine ⟨⟨lastIndex S, j⟩, Finset.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
      apply (mem_selected _ _ _).mpr
      exact ⟨hi, by simpa only [hlabel] using List.mem_toFinset.mp hj⟩
  have hn : (lastLabel S).Nodup := by
    rw [hlabel]
    exact (ProjectionBounds.body_label_pairwise S.stem _ hi).nodup
  rw [List.toFinset_card_of_nodup hn] at hfiber
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := selected S.stem) (fun a ↦ a.1 < lastIndex S)
  rw [hfiber] at hsplit
  exact hsplit.symm

theorem selected_inside (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hroot : S.stem.root < T.stem.root) (horient : GraphPayoff.Oriented .inside S.stem T.stem) :
    (selected S.stem).card = (selected T.stem).card + 1 := by
  have hS : S.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  have hT : T.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  have hlast : T.stem.ordinary.getLastD 0 < S.stem.ordinary.getLastD 0 := by
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hS,
      List.getLast?_eq_some_getLast hT, Option.getD_some, GraphPayoff.Oriented,
      GraphPayoff.endpoint] using horient
  have hd := ordinary_disjoint hclear
  rw [← gaps_card_eq_selected S.stem T.stem S.full hd hclear.interiorLeft hclear.exactLeft,
    ← gaps_card_eq_selected T.stem S.stem T.full hd.symm hclear.interiorRight hclear.exactRight]
  exact count_inside (S.stem.increasing.sublist S.stem.ordinary_sublist)
    (T.stem.increasing.sublist T.stem.ordinary_sublist) hd hS hT hroot hlast

theorem inside_decomposition (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hroot : S.stem.root < T.stem.root) (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ []) :
    beforeLast S + (lastLabel S).length = beforeLast T + (lastLabel T).length + 1 := by
  rw [← selected_card_decomposition S T.stem hclear.exactLeft hS,
    ← selected_card_decomposition T S.stem hclear.exactRight hT]
  exact selected_inside S T hclear hroot horient

theorem last_counts_of_before_eq (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hroot : S.stem.root < T.stem.root) (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ [])
    (heq : beforeLast S = beforeLast T) : (lastLabel S).length = (lastLabel T).length + 1 := by
  have h := inside_decomposition S T hclear hroot horient hS hT
  omega

theorem last_counts_of_before_lt (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hroot : S.stem.root < T.stem.root) (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ [])
    (hlt : beforeLast S < beforeLast T) : (lastLabel T).length + 2 ≤ (lastLabel S).length := by
  have h := inside_decomposition S T hclear hroot horient hS hT
  omega

end Erdos118.InsideCounts
