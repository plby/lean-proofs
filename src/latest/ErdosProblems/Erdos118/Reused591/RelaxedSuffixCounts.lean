import ErdosProblems.Erdos118.Reused591.ConsecutiveSuffixCounts
import ErdosProblems.Erdos118.Reused591.CutPersistence

namespace Erdos118.Reused591

/-!
# Remaining selected-leaf counts at actual relaxed history prefixes

The final cut suffix is identified using the counters recovered from
the actual prefix run. The exact count balance uses only the history's
freshness invariant and the inside endpoint order of the clear pair.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact

theorem LabeledWord.LegalRun.relaxed_leaf_position
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (hinit : LabeledWord.LegalRun LabeledWord.initial xs v)
    (htail : LabeledWord.LegalRun v ys last)
    (s : List (List ℕ)) (hs : word s = last.coordinates) (hr : v.relaxed = true) :
    v.bodyLabels.length - 1 < s.length ∧
      v.leafIndex - 1 < (s.getD (v.bodyLabels.length - 1) []).length ∧
      Payoff.leafPosition s (v.bodyLabels.length - 1) (v.leafIndex - 1) =
        v.coordinates.length - 1 := by
  have hpos := hinit.relaxed_coordinates_pos hr
  have hpref : List.IsPrefix v.coordinates (word s) := hs ▸ htail.coordinates_prefix
  have hlen := hpref.length_le
  have heq : v.coordinates = (word s).take (v.coordinates.length - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact List.prefix_iff_eq_take.mp hpref
  obtain ⟨i, j, hi, hj, hbody, hleaf, _hroot, _hmarker, hposition⟩ :=
    LabeledCode.relaxed_prefix_indices hinit s (v.coordinates.length - 1) heq (by omega) hr
  simpa only [hbody, hleaf, Nat.add_sub_cancel] using ⟨hi, hj, hposition.symm⟩

namespace Payoff

theorem ClearSide.relaxed_suffix_card {v last : LabeledWord} {s t : G}
    {xs ys : List (Finset ℕ × ℕ)} (h : ClearSide last s t)
    (hinit : LabeledWord.LegalRun LabeledWord.initial xs v)
    (htail : LabeledWord.LegalRun v ys last) (hr : v.relaxed = true) :
    (cutIndices ((word s.val).drop (v.coordinates.length - 1)) (word t.val)).card =
      (last.selectedLeafPairsFrom (v.bodyLabels.length - 1) (v.leafIndex - 1)).card := by
  obtain ⟨hi, hj, hpos⟩ := hinit.relaxed_leaf_position htail s.val h.coordinates hr
  rw [← hpos]
  exact h.leaf_suffix_card hi hj

theorem history_inside_relaxed_suffix_balance {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0) :
    (q.position.board.left.selectedLeafPairsFrom
      (p.position.board.left.bodyLabels.length - 1) (p.position.board.left.leafIndex - 1)).card =
      (q.position.board.right.selectedLeafPairsFrom
        (p.position.board.right.bodyLabels.length - 1)
          (p.position.board.right.leafIndex - 1)).card + 1 := by
  obtain ⟨as, ha⟩ := History.word_run p false
  obtain ⟨bs, hb⟩ := History.word_run p true
  obtain ⟨cs, hcs, hcf⟩ := (History.reachable_word_extension hpath).2 false
  obtain ⟨ds, hds, _hdf⟩ := (History.reachable_word_extension hpath).2 true
  change LabeledWord.LegalRun LabeledWord.initial as p.position.board.left at ha
  change LabeledWord.LegalRun LabeledWord.initial bs p.position.board.right at hb
  change LabeledWord.LegalRun p.position.board.left cs q.position.board.left at hcs
  change LabeledWord.LegalRun p.position.board.right ds q.position.board.right at hds
  change q.position.board.right.coordinates.getLastD 0 <
    q.position.board.left.coordinates.getLastD 0 at hmax
  have hlpos := ha.relaxed_coordinates_pos hl
  have hrpos := hb.relaxed_coordinates_pos hr
  have hlne : p.position.board.left.coordinates ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlpos
    omega
  have hrne : p.position.board.right.coordinates ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hrpos
    omega
  let x := p.position.board.left.coordinates.getLastD 0
  let y := p.position.board.right.coordinates.getLastD 0
  let pre := p.position.board.left.coordinates.dropLast
  let before := p.position.board.right.coordinates.dropLast
  let xs := cs.map Prod.snd
  let ys := ds.map Prod.snd
  have hxsplit : pre ++ [x] = p.position.board.left.coordinates := by
    simpa only [pre, x, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hlne,
      Option.getD_some] using List.dropLast_concat_getLast hlne
  have hysplit : before ++ [y] = p.position.board.right.coordinates := by
    simpa only [before, y, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hrne,
      Option.getD_some] using List.dropLast_concat_getLast hrne
  have hs : pre ++ x :: xs = word s.val := by
    rw [hc.1.coordinates, LabeledWord.runAtoms_coordinates hcs.run, ← hxsplit]
    simp only [xs, List.append_assoc, List.singleton_append]
  have ht : before ++ y :: ys = word t.val := by
    rw [hc.2.1.coordinates, LabeledWord.runAtoms_coordinates hds.run, ← hysplit]
    simp only [ys, List.append_assoc, List.singleton_append]
  have hxdrop : (word s.val).drop (p.position.board.left.coordinates.length - 1) = x :: xs := by
    rw [hc.1.coordinates, LabeledWord.runAtoms_coordinates hcs.run,
      List.drop_append_of_le_length (Nat.sub_le _ _), List.drop_length_sub_one hlne]
    simp only [x, xs, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hlne,
      Option.getD_some, List.singleton_append]
  have hydrop : (word t.val).drop (p.position.board.right.coordinates.length - 1) = y :: ys := by
    rw [hc.2.1.coordinates, LabeledWord.runAtoms_coordinates hds.run,
      List.drop_append_of_le_length (Nat.sub_le _ _), List.drop_length_sub_one hrne]
    simp only [y, ys, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hrne,
      Option.getD_some, List.singleton_append]
  have hd : (pre ++ x :: xs).Disjoint (before ++ y :: ys) := by
    rw [hs, ht]
    intro z hzs hzt
    exact Finset.disjoint_left.mp hc.2.2 (List.mem_toFinset.mpr hzs) (List.mem_toFinset.mpr hzt)
  have hfresh : ∀ z ∈ xs, y < z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact (Position.history_last_bound p true).trans_lt (hcf a ha)
  have hlast : (y :: ys).getLastD 0 < (x :: xs).getLastD 0 := by
    have hsl : p.position.board.left.coordinates.length - 1 < (word s.val).length := by
      have hlen := hcs.coordinates_prefix.length_le
      rw [hc.1.coordinates]
      omega
    have htl : p.position.board.right.coordinates.length - 1 < (word t.val).length := by
      have hlen := hds.coordinates_prefix.length_le
      rw [hc.2.1.coordinates]
      omega
    rw [← hxdrop, ← hydrop]
    simp only [List.getLastD_eq_getLast?, List.getLast?_drop,
      if_neg (not_le_of_gt hsl), if_neg (not_le_of_gt htl)]
    simpa only [hc.1.coordinates, hc.2.1.coordinates, List.getLastD_eq_getLast?] using hmax
  have hbalance := consecutive_suffix_cut_balance
    (hs.symm ▸ s.property) (ht.symm ▸ t.property) hd horder hfresh hlast
  have hleft := hc.1.relaxed_suffix_card ha hcs hl
  have hright := hc.2.1.relaxed_suffix_card hb hds hr
  rw [hxdrop] at hleft
  rw [hydrop] at hright
  simpa only [hs, ht, hleft, hright] using hbalance

#print axioms LabeledWord.LegalRun.relaxed_leaf_position
#print axioms ClearSide.relaxed_suffix_card
#print axioms history_inside_relaxed_suffix_balance

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
