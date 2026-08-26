import ErdosProblems.Erdos591.InsideLastBodySize

/-!
# Before a singleton last first-word body, the other selections are exhausted

Submit one singleton response only to test the winning boundary. The
first word then has no unread selection. The inside endpoint rule forces
the unchanged second word to have none already at the original history.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_singleton_last_other_exhausted {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hp : p.position.pending = some ⟨false, .advance 1⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hstartT : p.position.board.right.parser ≠ .start) :
    ¬ Macro.Pending p.position.board.right := by
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 1 (by omega) (by omega)
  obtain ⟨q, _v, hs, _hv, _hn, _hvn, _hshape, hrel, _hvrel, hidx, _hvIdx,
      hlabels, _hvLabels, hother, _hvOther⟩ := first_leaf_gluing hHN hH blue σ p p false false
    L L rfl rfl hp hp hm hm (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hpath := Relation.ReflTransGen.single hs
  have hwinq := hwin.of_reachable (exactGame N blue) hpath
  have hw := ((Position.history_dataInvariant q).2.1 false).1
  have hstart := LabeledWord.relaxed_ne_start hw hrel
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  obtain ⟨as, has, _hpool⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) false
  have hroots := has.rootLabel_eq (by simp [Board.get, hparse])
  have hlast : ¬ Macro.Pending q.position.board.left := by
    have hcurrent : q.position.board.left.currentLabel = L.upper := by
      simp [LabeledWord.currentLabel, show q.position.board.left.bodyLabels =
        p.position.board.left.bodyLabels ++ [L.upper] from hlabels]
    intro hpending
    rcases hpending with ⟨i, himem, hilt⟩ | ⟨_, j, hjmem, hjlt⟩
    · have hi' := hrootLast i (hroots ▸ himem)
      have hlen : q.position.board.left.bodyLabels.length =
          p.position.board.left.bodyLabels.length + 1 := by
        simpa only [List.length_append, List.length_singleton, Board.get] using
          congrArg List.length hlabels
      omega
    · have heq : j = L.pivot := Finset.card_le_one.mp L.upper_card.le j
        (hcurrent ▸ hjmem) L.pivot L.pivot_upper
      have hi' : q.position.board.left.leafIndex = L.pivot := hidx
      omega
  have hother' : q.position.board.right = p.position.board.right := hother
  have hlastT := winning_no_pending_smaller hHN hH blue hwinq (follow_mode_some hpath hmode)
    (by simpa [Board.get, hother'] using hstartT) hstart hlast
  simpa [Board.get, hother'] using hlastT

#print axioms winning_singleton_last_other_exhausted

end Erdos591.Positive.Game.Payoff
