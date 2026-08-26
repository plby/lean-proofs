import ErdosProblems.Erdos118.BodySuffixCounts
import ErdosProblems.Erdos118.InsideCounts

/-!
The suffix at the last selected body has exactly that body's selected-gap
count. For actual clear inside pairs, last-marker order is equivalent to
the comparison of the before-last selected counts.
-/

namespace Erdos118.LastSuffixCounts

open Negative Negative.Exact LabelledExtensions DecisionStates ClearPairs CutIndices
open GapCounts SelectedGapCounts LastBodyRefinement LastMarkerRefinement
open InsideCounts BodySuffixCounts

def preword (S : Completed) : List ℕ :=
  S.stem.root :: (S.stem.done.take (lastIndex S)).flatMap Body.ordinary

def suffix (S : Completed) : List ℕ :=
  (S.stem.done.drop (lastIndex S)).flatMap Body.ordinary

theorem ordinary_split (S : Completed) : S.stem.ordinary = preword S ++ suffix S := by
  simp only [preword, suffix, Stem.ordinary, List.cons_append, ← List.flatMap_append,
    List.take_append_drop]

theorem suffix_eq_drop (S : Completed) :
    suffix S = S.stem.ordinary.drop (offset S.stem (lastIndex S)) := by
  have hlen : (preword S).length = offset S.stem (lastIndex S) := by
    simp only [preword, offset, List.length_cons, Nat.add_comm]
  rw [ordinary_split, ← hlen, List.drop_left]

theorem suffix_ne_nil (S : Completed) (hne : S.stem.rootLabel ≠ []) : suffix S ≠ [] := by
  unfold suffix
  rw [List.drop_eq_getElem_cons (lastIndex_lt S hne)]
  simp only [List.flatMap_cons, Body.ordinary, Negative.Exact.levelWord,
    List.cons_append]
  exact List.cons_ne_nil _ _

theorem suffix_head (S : Completed) (hne : S.stem.rootLabel ≠ []) :
    (suffix S).headD 0 = lastMarker S := by
  unfold suffix lastMarker
  rw [List.drop_eq_getElem_cons (lastIndex_lt S hne),
    List.getElem?_eq_getElem (lastIndex_lt S hne)]
  rfl

theorem suffix_last (S : Completed) (hne : S.stem.rootLabel ≠ []) :
    (suffix S).getLastD 0 = S.stem.ordinary.getLastD 0 := by
  rw [ordinary_split]
  simp only [List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ (suffix_ne_nil S hne)]

theorem suffix_count (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hne : S.stem.rootLabel ≠ []) :
    (gaps (suffix S) T.stem.ordinary).card = (lastLabel S).length := by
  rw [suffix_eq_drop, suffix_gaps_card S.stem T.stem S.full (ordinary_disjoint hclear)
    hclear.interiorLeft hclear.exactLeft]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := selected S.stem) (fun a ↦ a.1 < lastIndex S)
  simp only [Nat.not_lt] at hsplit
  have hdecomp := selected_card_decomposition S T.stem hclear.exactLeft hne
  unfold beforeLast at hdecomp
  omega

private theorem last_order (S T : Completed)
    (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ []) :
    (suffix T).getLastD 0 < (suffix S).getLastD 0 := by
  rw [suffix_last T hT, suffix_last S hS]
  have hs : S.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  have ht : T.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hs,
    List.getLast?_eq_some_getLast ht, Option.getD_some, GraphPayoff.Oriented,
    GraphPayoff.endpoint] using horient

theorem last_counts_of_marker_lt (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ [])
    (hlt : lastMarker S < lastMarker T) : (lastLabel T).length + 1 ≤ (lastLabel S).length := by
  have hx : (preword S ++ suffix S).Pairwise (· < ·) :=
    ordinary_split S ▸ S.stem.increasing.sublist S.stem.ordinary_sublist
  have hy : (preword T ++ suffix T).Pairwise (· < ·) :=
    ordinary_split T ▸ T.stem.increasing.sublist T.stem.ordinary_sublist
  have hd : (preword S ++ suffix S).Disjoint (preword T ++ suffix T) := by
    rw [← ordinary_split, ← ordinary_split]
    exact ordinary_disjoint hclear
  have hhead : (suffix S).headD 0 < (suffix T).headD 0 := by
    rw [suffix_head S hS, suffix_head T hT]
    exact hlt
  have h := suffix_counts_of_head_lt hx hy hd (suffix_ne_nil S hS) (suffix_ne_nil T hT)
    hhead (last_order S T horient hS hT)
  rw [← ordinary_split, ← ordinary_split, suffix_count T S hclear.symm hT,
    suffix_count S T hclear hS] at h
  exact h

theorem last_counts_of_marker_gt (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ [])
    (hlt : lastMarker T < lastMarker S) : (lastLabel S).length ≤ (lastLabel T).length := by
  have hx : (preword S ++ suffix S).Pairwise (· < ·) :=
    ordinary_split S ▸ S.stem.increasing.sublist S.stem.ordinary_sublist
  have hy : (preword T ++ suffix T).Pairwise (· < ·) :=
    ordinary_split T ▸ T.stem.increasing.sublist T.stem.ordinary_sublist
  have hd : (preword S ++ suffix S).Disjoint (preword T ++ suffix T) := by
    rw [← ordinary_split, ← ordinary_split]
    exact ordinary_disjoint hclear
  have hhead : (suffix T).headD 0 < (suffix S).headD 0 := by
    rw [suffix_head S hS, suffix_head T hT]
    exact hlt
  have h := suffix_counts_of_head_gt hx hy hd (suffix_ne_nil S hS) (suffix_ne_nil T hT)
    hhead (last_order S T horient hS hT)
  rw [← ordinary_split, ← ordinary_split, suffix_count T S hclear.symm hT,
    suffix_count S T hclear hS] at h
  exact h

theorem marker_lt_iff_before_le (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (hroot : S.stem.root < T.stem.root) (horient : GraphPayoff.Oriented .inside S.stem T.stem)
    (hS : S.stem.rootLabel ≠ []) (hT : T.stem.rootLabel ≠ []) :
    lastMarker S < lastMarker T ↔ beforeLast S ≤ beforeLast T := by
  have hc := inside_decomposition S T hclear hroot horient hS hT
  constructor
  · intro hlt
    have h := last_counts_of_marker_lt S T hclear horient hS hT hlt
    omega
  · intro hle
    by_contra hn
    have hne := lastMarkers_ne S T hclear hS hT
    have hlt : lastMarker T < lastMarker S := by omega
    have h := last_counts_of_marker_gt S T hclear horient hS hT hlt
    omega

end Erdos118.LastSuffixCounts
