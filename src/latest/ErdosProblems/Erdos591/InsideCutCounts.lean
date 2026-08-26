import ErdosProblems.Erdos591.CoordinateCutCounts

/-!
# Exact total and last-body label counts of an inside clear pair

The root coordinate order is explicit. It will be recovered from actual
opening histories when these finite geometric lemmas are applied there.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem Clear.inside_selectedLeafCount {board : Board} {s t : G} (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board) :
    board.left.selectedLeafCount = board.right.selectedLeafCount + 1 := by
  have hd : (word s.val).Disjoint (word t.val) := by
    intro x hx ht
    exact Finset.disjoint_left.mp h.2.2 (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr ht)
  have hc := cut_count_inside s.property t.property hd (word_ne_nil s.val) (word_ne_nil t.val)
    (by simpa only [h.1.coordinates, h.2.1.coordinates] using hfirst)
    (by simpa only [h.1.coordinates, h.2.1.coordinates, MaxOrder, Bool.true_eq, ↓reduceIte]
      using hlast)
  simpa only [h.1.cutIndices_card, h.2.1.cutIndices_card] using hc

theorem Clear.inside_last_body_count {board : Board} {s t : G} (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty) :
    board.left.beforeLastLeafCount + board.left.lastSelectedLabel.card =
      board.right.beforeLastLeafCount + board.right.lastSelectedLabel.card + 1 := by
  simpa only [LabeledWord.selectedLeafCount_decomposition hl,
    LabeledWord.selectedLeafCount_decomposition hr] using h.inside_selectedLeafCount hfirst hlast

theorem Clear.aligned_last_body_count {board : Board} {s t : G} (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty)
    (haligned : board.left.beforeLastLeafCount = board.right.beforeLastLeafCount) :
    board.left.lastSelectedLabel.card = board.right.lastSelectedLabel.card + 1 := by
  have hc := h.inside_last_body_count hfirst hlast hl hr
  omega

theorem Clear.strict_last_body_count {board : Board} {s t : G} (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty)
    (hstrict : board.left.beforeLastLeafCount < board.right.beforeLastLeafCount) :
    board.right.lastSelectedLabel.card + 2 ≤ board.left.lastSelectedLabel.card := by
  have hc := h.inside_last_body_count hfirst hlast hl hr
  omega

theorem ClearSide.beforeLastLeafCount_pos_iff {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    0 < w.beforeLastLeafCount ↔ 2 ≤ w.rootLabel.card := by
  constructor
  · intro hpos
    by_contra hn
    have hm : w.lastSelectedBody ∈ w.rootLabel := by
      simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
    have hcard : (w.rootLabel.erase w.lastSelectedBody).card = 0 := by
      rw [Finset.card_erase_of_mem hm]
      omega
    have hempty := Finset.card_eq_zero.mp hcard
    simp [LabeledWord.beforeLastLeafCount, hempty] at hpos
  · intro hcard
    have hle := h.root_card_sub_one_le_beforeLastLeafCount hne
    omega

theorem Clear.inside_roots_nonempty {board : Board} {s t : G} (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board) (hcard : 2 ≤ board.left.rootLabel.card) :
    board.left.rootLabel.Nonempty ∧ board.right.rootLabel.Nonempty ∧
      0 < board.left.beforeLastLeafCount := by
  have hl : board.left.rootLabel.Nonempty := Finset.card_pos.mp (by omega)
  have hr : board.right.rootLabel.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hc := h.inside_selectedLeafCount hfirst hlast
    have hbound := h.1.root_card_le_selectedLeafCount
    have hz : board.right.selectedLeafCount = 0 := by
      simp only [LabeledWord.selectedLeafCount, he, Finset.sum_empty]
    rw [hz] at hc
    omega
  exact ⟨hl, hr, (h.1.beforeLastLeafCount_pos_iff hl).mpr hcard⟩

#print axioms Clear.inside_selectedLeafCount
#print axioms Clear.inside_last_body_count
#print axioms Clear.aligned_last_body_count
#print axioms Clear.strict_last_body_count
#print axioms ClearSide.beforeLastLeafCount_pos_iff
#print axioms Clear.inside_roots_nonempty

end Erdos591.Positive.Game.Payoff
