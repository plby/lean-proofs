import ErdosProblems.Erdos118.Reused591.ManagedHandoff
import ErdosProblems.Erdos118.Reused591.NextLeafAcceptance

namespace Erdos118.Reused591

/-!
# An actual response stops exactly at the next selected leaf

The target-leaf invariant bounds the endpoint and preserves its body.
The response reads at least one coordinate, so its leaf counter grows
strictly. First-event stopping and the least-next-index hypothesis then
identify the endpoint with the prescribed selected index.
-/

namespace Erdos591.Positive.Game

theorem Reply.next_leaf_endpoint {board next : Board} {side : Bool} {d j : ℕ}
    {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u next)
    (hw : (board.get side).CursorInvariant)
    (hwNext : (next.get side).CursorInvariant)
    (hpos : ∀ x ∈ u, 0 < x)
    (htarget : LabeledWord.UpToLeaf j (board.get side))
    (hstrict : (board.get side).leafIndex < j)
    (hnext : ∀ k ∈ (board.get side).currentLabel,
      (board.get side).leafIndex < k → j ≤ k) :
    (next.get side).relaxed = true ∧ (next.get side).leafIndex = j ∧
      (next.get side).bodyLabels = (board.get side).bodyLabels ∧
      (next.get side).bodyMarker = (board.get side).bodyMarker := by
  obtain ⟨hup, hlabels, hmarker⟩ := hr.advance_up_to_leaf hw htarget hstrict
  have hrel := hup.at_event hwNext hr.end_event
  obtain ⟨as, has, _⟩ := hr.legal_run hpos side
  obtain ⟨n, xs, hcoords⟩ := hr.coordinates_extend
  have hlen := congrArg List.length hcoords
  have hlen' := congrArg List.length (LabeledWord.runAtoms_coordinates has.run)
  simp only [List.length_append, List.length_cons, List.length_map] at hlen hlen'
  have haspos : 0 < as.length := by omega
  obtain ⟨r, k, hparse⟩ := htarget.parser_leaves hw
  have hstart : (board.get side).parser ≠ .start := by simp [hparse]
  have hleaf := has.leafIndex_of_body_length hstart (congrArg List.length hlabels)
  have hlt : (board.get side).leafIndex < (next.get side).leafIndex := by omega
  have hmem : (next.get side).leafIndex ∈ (board.get side).currentLabel := by
    have hm := (of_decide_eq_true hrel).2.2
    simpa [LabeledWord.currentLabel, hlabels] using hm
  exact ⟨hrel, le_antisymm hup.before (hnext _ hmem hlt), hlabels, hmarker⟩

#print axioms Reply.next_leaf_endpoint

end Erdos591.Positive.Game

end Erdos118.Reused591
