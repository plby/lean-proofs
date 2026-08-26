import ErdosProblems.Erdos591.InitialRequestSelection

/-! # The root-label cardinality in an actual initial advance response -/

namespace Erdos591.Positive.Game

theorem Advance.initial_root_card (d : ℕ) (xs : List ℕ) (v : LabeledWord)
    (hinc : xs.Pairwise (· < ·))
    (hrun : parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d []) xs = some (.remainder v)) :
    v.rootLabel.card = d := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude ⟨LabeledWord.initial, rfl⟩ d [] xs (.remainder v) hrun
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hcard : labels.toFinset.card = d :=
    (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
  have hread : LabeledWord.initial.read labels.toFinset n = some first := by simpa using hf
  have hfirst : first = LabeledCode.rootCursor labels.toFinset n :=
    Option.some.inj (hread.symm.trans (LabeledCode.read_root labels.toFinset n))
  have hlegal := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hl
  have hroot : v.rootLabel = labels.toFinset := by
    simpa [hfirst, LabeledCode.rootCursor] using
      hlegal.rootLabel_eq (LabeledWord.read_parser_ne_start hread)
  exact hroot ▸ hcard

theorem Reply.initial_root_card {board last : Board} {side : Bool} {d : ℕ}
    {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u last)
    (hinit : board.get side = LabeledWord.initial) : (last.get side).rootLabel.card = d := by
  cases hr with
  | advance side d u w hlegal hrun =>
      have hrun' : Advance.parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d [])
          (u.sort (· ≤ ·)) = some (.remainder w) := by simpa only [hinit] using hrun
      simpa using Advance.initial_root_card d (u.sort (· ≤ ·)) w
        (Finset.sortedLT_sort u).pairwise hrun'

#print axioms Reply.initial_root_card

end Erdos591.Positive.Game
