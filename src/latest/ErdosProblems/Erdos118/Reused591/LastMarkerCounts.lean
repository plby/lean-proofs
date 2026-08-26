import ErdosProblems.Erdos118.Reused591.LastBodySuffixCuts
import ErdosProblems.Erdos118.Reused591.InsideCutCounts

namespace Erdos118.Reused591

/-! # Exact equivalence between last-marker order and pre-last cut counts -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem Clear.last_body_count_comparison {board : Board} {s t : G} (h : Clear board s t)
    (hlast : MaxOrder true board)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty) :
    (board.left.lastSelectedMarker < board.right.lastSelectedMarker →
      board.right.lastSelectedLabel.card + 1 ≤ board.left.lastSelectedLabel.card) ∧
    (board.right.lastSelectedMarker < board.left.lastSelectedMarker →
      board.left.lastSelectedLabel.card ≤ board.right.lastSelectedLabel.card) := by
  let k := bodyMarkerPosition s.val (board.left.lastSelectedBody - 1)
  let l := bodyMarkerPosition t.val (board.right.lastSelectedBody - 1)
  let xs := (word s.val).drop k
  let ys := (word t.val).drop l
  let pre := (word s.val).take k
  let before := (word t.val).take l
  have hs : pre ++ xs = word s.val := List.take_append_drop _ _
  have ht : before ++ ys = word t.val := List.take_append_drop _ _
  have hxs : xs ≠ [] := h.1.last_body_suffix_nonempty hl
  have hys : ys ≠ [] := h.2.1.last_body_suffix_nonempty hr
  have hx : (pre ++ xs).Pairwise (· < ·) := hs.symm ▸ s.property
  have hy : (before ++ ys).Pairwise (· < ·) := ht.symm ▸ t.property
  have hd : (pre ++ xs).Disjoint (before ++ ys) := by
    rw [hs, ht]
    intro x hxs hys
    exact Finset.disjoint_left.mp h.2.2 (List.mem_toFinset.mpr hxs) (List.mem_toFinset.mpr hys)
  have hxhead : xs.headD 0 = board.left.lastSelectedMarker := h.1.last_body_suffix_head hl
  have hyhead : ys.headD 0 = board.right.lastSelectedMarker := h.2.1.last_body_suffix_head hr
  have hxlast : xs.getLastD 0 = (word s.val).getLastD 0 := h.1.last_body_suffix_last hl
  have hylast : ys.getLastD 0 = (word t.val).getLastD 0 := h.2.1.last_body_suffix_last hr
  have hmax : ys.getLastD 0 < xs.getLastD 0 := by
    rw [hxlast, hylast, h.1.coordinates, h.2.1.coordinates]
    exact hlast
  have hxcount : (cutIndices xs (before ++ ys)).card = board.left.lastSelectedLabel.card := by
    rw [ht]
    exact h.1.last_body_suffix_card hl
  have hycount : (cutIndices ys (pre ++ xs)).card = board.right.lastSelectedLabel.card := by
    rw [hs]
    exact h.2.1.last_body_suffix_card hr
  constructor
  · intro hmarker
    have hhead : xs.headD 0 < ys.headD 0 := by simpa only [hxhead, hyhead] using hmarker
    simpa only [hxcount, hycount] using suffix_counts_of_head_lt hx hy hd hxs hys hhead hmax
  · intro hmarker
    have hhead : ys.headD 0 < xs.headD 0 := by simpa only [hxhead, hyhead] using hmarker
    simpa only [hxcount, hycount] using suffix_counts_of_head_gt hx hy hd hxs hys hhead hmax

theorem Clear.last_marker_lt_iff_beforeLastLeafCount_le {board : Board} {s t : G}
    (h : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hlast : MaxOrder true board)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty) :
    board.left.lastSelectedMarker < board.right.lastSelectedMarker ↔
      board.left.beforeLastLeafCount ≤ board.right.beforeLastLeafCount := by
  have hcount := h.inside_last_body_count hfirst hlast hl hr
  have hcompare := h.last_body_count_comparison hlast hl hr
  have hne := h.lastSelectedMarker_ne hl hr
  constructor
  · intro hmarker
    have hle := hcompare.1 hmarker
    omega
  · intro hle
    by_contra hn
    have hmarker : board.right.lastSelectedMarker < board.left.lastSelectedMarker := by omega
    have hsize := hcompare.2 hmarker
    omega

#print axioms Clear.last_body_count_comparison
#print axioms Clear.last_marker_lt_iff_beforeLastLeafCount_le

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
