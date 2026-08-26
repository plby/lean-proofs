import ErdosProblems.Erdos591.NextLeafAcceptance
import ErdosProblems.Erdos591.RootGluing

/-!
# An actual zero-label advance to the next selected leaf

The current cursor may itself be relaxed. The advance prelude first
consumes a new coordinate; the remainder then stops at the next selected
index, with all old labels retained. This is not a finish response.
-/

namespace Erdos591.Positive.Game

namespace Advance

theorem zero_to_next_leaf (w : Unfinished) (hw : w.val.CursorInvariant)
    {v : LabeledWord} {xs : List ℕ} {j : ℕ}
    (hs : LabeledWord.UpToLeaf j w.val) (hlt : w.val.leafIndex < j)
    (hnext : ∀ k ∈ w.val.currentLabel, w.val.leafIndex < k → j ≤ k)
    (hraw : w.val.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hvs : LabeledWord.UpToLeaf j v) (hvleaf : v.leafIndex = j)
    (hlabels : v.bodyLabels = w.val.bodyLabels) (hbody : v.bodyMarker = w.val.bodyMarker) :
    parser.run (.prelude w 0 []) xs = some (.remainder v) := by
  cases xs with
  | nil =>
      have heq : w.val = v := Option.some.inj hraw
      rw [heq, hvleaf] at hlt
      exact (Nat.lt_irrefl _ hlt).elim
  | cons n xs =>
      cases hread : w.val.read ∅ n with
      | none => simp [LabeledWord.runAtoms, hread] at hraw
      | some first =>
          have htail : first.runAtoms (xs.map fun n => (∅, n)) = some v := by
            simpa [LabeledWord.runAtoms, hread] using hraw
          have hfirst := hs.read_before hw hlt hread
          have hcorrect := hw.read (LabeledWord.allowed_empty w.property n) hread
          obtain ⟨r, k, hp⟩ := hs.parser_leaves hw
          have heq : w.val.record ∅ n (Parser.normalize r k) = first := by
            simpa [LabeledWord.read, hp, Parser.step] using hread
          have hleaf : first.leafIndex = w.val.leafIndex + 1 := by
            simp [← heq, LabeledWord.record, hp]
          have hafter : w.val.leafIndex < first.leafIndex := by omega
          have hrest := LabeledWord.advanceRemainder_to_next_leaf hcorrect hfirst.1 hafter
            (fun k hk hki => hnext k (by
              simpa [LabeledWord.currentLabel, hfirst.2.1] using hk) hki)
            htail hvs hvleaf (hlabels.trans hfirst.2.1.symm) (hbody.trans hfirst.2.2.symm)
          simpa using run_prelude_build w [] [] n xs first v (by simpa using hread) hrest

end Advance

theorem Reply.next_leaf_of_list (board : Board) (side : Bool) {v : LabeledWord}
    {xs : List ℕ} {j : ℕ} (hw : (board.get side).CursorInvariant)
    (hs : LabeledWord.UpToLeaf j (board.get side)) (hlt : (board.get side).leafIndex < j)
    (hnext : ∀ k ∈ (board.get side).currentLabel, (board.get side).leafIndex < k → j ≤ k)
    (hraw : (board.get side).runAtoms (xs.map fun n => (∅, n)) = some v)
    (hvs : LabeledWord.UpToLeaf j v) (hvleaf : v.leafIndex = j)
    (hlabels : v.bodyLabels = (board.get side).bodyLabels)
    (hbody : v.bodyMarker = (board.get side).bodyMarker)
    (hinc : xs.Pairwise (· < ·)) :
    Reply board ⟨side, .advance 0⟩ xs.toFinset (board.update side v) := by
  have hlive : (board.get side).terminal = false := by
    obtain ⟨r, k, hp⟩ := hs.parser_leaves hw
    simp [LabeledWord.terminal, hp]
  apply Reply.advance side 0 xs.toFinset v ⟨hlive, Or.inl rfl⟩
  rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc]
  exact Advance.zero_to_next_leaf ⟨board.get side, hlive⟩ hw hs hlt hnext hraw hvs hvleaf
    hlabels hbody

#print axioms Reply.next_leaf_of_list

end Erdos591.Positive.Game
