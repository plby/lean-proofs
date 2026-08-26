import ErdosProblems.Erdos118.Reused591.BodyMarkerPositions
import ErdosProblems.Erdos118.Reused591.CutSuffixCounts
import ErdosProblems.Erdos118.Reused591.DecodedBodyMarkers

namespace Erdos118.Reused591

/-!
# Exact cut count of the suffix beginning at the last selected body

Every retained cut is in that selected body. Earlier body leaves precede
its marker, and a selected later body would contradict maximality of
the selected root index. The finite cut bijection is explicit.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem ClearSide.last_body_suffix_card {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    (cutIndices ((word s.val).drop (bodyMarkerPosition s.val (w.lastSelectedBody - 1)))
      (word t.val)).card = w.lastSelectedLabel.card := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hmBounds := h.root_bounds _ hm
  have hi : w.lastSelectedBody - 1 < s.val.length := by omega
  rw [cutIndices_drop_card]
  symm
  apply Finset.card_bij
    (fun j _ => leafPosition s.val (w.lastSelectedBody - 1) (j - 1))
  · intro j hj
    have hcut := h.selected_pair_cut hm hj
    exact Finset.mem_filter.mpr ⟨(mem_cutIndices _ _ _).mpr hcut.2.2,
      (marker_le_leafPosition_iff s.val hcut.1 hcut.2.1).mpr le_rfl⟩
  · intro j hj k hk heq
    have hcutj := h.selected_pair_cut hm hj
    have hcutk := h.selected_pair_cut hm hk
    have he := (LabeledCode.leafPosition_injective s.val hcutj.1 hcutj.2.1
      hcutk.1 hcutk.2.1 heq).2
    have hjpos := (h.body_bounds _ hi j hj).1
    have hkpos := (h.body_bounds _ hi k hk).1
    omega
  · intro k hk
    obtain ⟨hcut, hpos⟩ := Finset.mem_filter.mp hk
    obtain ⟨i, j, hij, hkEq⟩ := h.all_cuts_leaves k ((mem_cutIndices _ _ _).mp hcut)
    have himem : i + 1 ∈ w.rootLabel := (h.root_exact i).mpr ⟨j, hij⟩
    have hibound : i + 1 ≤ w.lastSelectedBody := Finset.le_sup (f := id) himem
    have hile : w.lastSelectedBody - 1 ≤ i :=
      (marker_le_leafPosition_iff s.val hij.1 hij.2.1).mp (hkEq ▸ hpos)
    have hiEq : i = w.lastSelectedBody - 1 := by omega
    refine ⟨j + 1, ?_, ?_⟩
    · change j + 1 ∈ w.bodyLabels.getD (w.lastSelectedBody - 1) ∅
      rw [← hiEq]
      exact (h.body_exact i hij.1 j).mpr hij
    · simpa only [Nat.add_sub_cancel, ← hiEq] using hkEq.symm

theorem ClearSide.last_body_suffix_head {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    ((word s.val).drop (bodyMarkerPosition s.val (w.lastSelectedBody - 1))).headD 0 =
      w.lastSelectedMarker := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hb := h.root_bounds _ hm
  rw [head_drop_bodyMarkerPosition s.val (by omega)]
  simp only [LabeledWord.lastSelectedMarker, LabeledWord.decodedBodies_eq h.coordinates]

theorem ClearSide.last_body_suffix_nonempty {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    (word s.val).drop (bodyMarkerPosition s.val (w.lastSelectedBody - 1)) ≠ [] := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hb := h.root_bounds _ hm
  rw [drop_bodyMarkerPosition s.val (by omega)]
  simp [levelWord]

theorem ClearSide.last_body_suffix_last {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    ((word s.val).drop (bodyMarkerPosition s.val (w.lastSelectedBody - 1))).getLastD 0 =
      (word s.val).getLastD 0 := by
  have hm : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hb := h.root_bounds _ hm
  have hi := bodyMarkerPosition_lt_length s.val (by omega : w.lastSelectedBody - 1 < s.val.length)
  simp only [List.getLastD_eq_getLast?, List.getLast?_drop, if_neg (not_le_of_gt hi)]

#print axioms ClearSide.last_body_suffix_card
#print axioms ClearSide.last_body_suffix_head
#print axioms ClearSide.last_body_suffix_last

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
