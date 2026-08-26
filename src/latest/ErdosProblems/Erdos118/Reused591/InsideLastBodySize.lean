import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.PositiveSecondRequest

namespace Erdos118.Reused591

/-!
# A sole remaining selected body cannot receive only one leaf

If the right word is still initial in an inside winning play and
the left marker is its last selected body, a singleton body label
would exhaust all left selections at the first leaf. The next right
opening would have to be both positive and zero under triangle-freeness.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_inside_last_body_size {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) (hi : p.position.board.right = LabeledWord.initial)
    {d : ℕ} (hd : 0 < d) (hp : p.position.pending = some ⟨false, .advance d⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1) : 2 ≤ d := by
  by_contra hn
  have he : d = 1 := by omega
  subst d
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 1 (by omega) (by omega)
  obtain ⟨q, _v, hs, _hv, hnone, _hvn, _hshape, hrel, _hvrel, hidx, _hvIdx,
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
    · have heq : j = L.pivot := Finset.card_le_one.mp (L.upper_card.le) j
        (hcurrent ▸ hjmem) L.pivot L.pivot_upper
      have hi' : q.position.board.left.leafIndex = L.pivot := hidx
      omega
  obtain ⟨q', e, hrequest, hboard, hpend, hepos⟩ := winning_initial_right_request hHN hH blue
    htri hroot hwinq hnone (by simpa [Board.get, hi] using hother) hrel
  have hwinq' := hwinq.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hrequest)
  have hz := winning_initial_smaller_zero_of_other_last hHN hH blue hwinq'
    (follow_mode_some (hpath.tail hrequest) hmode) hpend rfl
    (by simpa [hboard, Board.get, hi] using hother)
    (by simpa [hboard, Board.get] using hstart) (by simpa [hboard, Board.get] using hlast)
  have hezero : e = 0 := hz
  omega

#print axioms winning_inside_last_body_size

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
