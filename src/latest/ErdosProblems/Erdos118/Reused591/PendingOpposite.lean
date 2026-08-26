import ErdosProblems.Erdos118.Reused591.OutsideBoundary
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.LastLastLabels

namespace Erdos118.Reused591

/-!
# An unread opposite selection after a fresh nonlast selected leaf

The compulsory switch cannot finish the opposite word while a selection
remains in the first one. A nonsingleton selected-body request admits a
test first-leaf response with such a remaining selection.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_fresh_nonlast_other_pending {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hnone : p.position.pending = none)
    (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hremain : Macro.Pending (p.position.board.get side))
    (hstart : (p.position.board.get (!side)).parser ≠ .start) :
    Macro.Pending (p.position.board.get (!side)) := by
  by_contra hn
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  have hk : (exactGame N blue).kind p = .architect :=
    (Concrete.kind_architect_iff (payoff blue) p).mpr
      ⟨hnone, Board.not_done_of_live hlive⟩
  obtain ⟨flag, r, hnext, heq⟩ := Concrete.architect_choice (payoff blue) σ p hk
  let q := p.append (p.position.request flag r) hnext
  have hs : (exactGame N blue).FollowStep σ H b p q := by
    simpa only [heq] using FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hboard : q.position.board = p.position.board := by simp [q, Position.request]
  have hp : q.position.pending = some r := by simp [q, Position.request]
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  have hside := winning_pending_switch hHN hH blue hwinq hp side
    (by simpa [hboard] using hrel) (by simpa [hboard] using hsep)
  have hkind : (exactGame N blue).kind q = .builder :=
    (Concrete.kind_builder_iff (payoff blue) q).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH q hkind (b q)
  have ht := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ q u hkind hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hf := (Reply.not_pending_iff_finish q.position.board r u _
    ((Position.history_controlInvariant q).2 r hp)
    (by simpa [hside, hboard] using hstart) (by simpa [hside, hboard] using hn)).mp hr
  have hcomplete : ((Concrete.response q u).position.board.get (!side)).terminal = true := by
    simpa [hside] using hf.finish_terminal
  have hno := winning_not_pending_of_other_complete hHN hH blue
    (hwinq.of_reachable (exactGame N blue) (Relation.ReflTransGen.single ht)) side hcomplete
  have hother : (Concrete.response q u).position.board.get side = p.position.board.get side := by
    simpa [hside, hboard] using hr.other_eq
  change ¬ Macro.Pending ((Concrete.response q u).position.board.get side) at hno
  rw [hother] at hno
  exact hno hremain

theorem winning_large_body_other_pending {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) {d : ℕ} (hd : 2 ≤ d)
    (hp : p.position.pending = some ⟨side, .advance d⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hstart : (p.position.board.get (!side)).parser ≠ .start) :
    Macro.Pending (p.position.board.get (!side)) := by
  let B := max p.position.bound (b p)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 d (by omega) (by omega)
  obtain ⟨q, _v, hs, _hv, hn, _hvn, _hshape, hrel, _hvr, hidx, _hvi,
      hlabels, _hvl, hother, _hvo⟩ := first_leaf_gluing hHN hH blue σ p p side side
    L L rfl rfl hp hp hm hm (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  have hcurrent : (q.position.board.get side).currentLabel = L.upper := by
    simp [LabeledWord.currentLabel, hlabels]
  have hselected : (q.position.board.get side).bodyLabels.length ∈
      (q.position.board.get side).rootLabel := (of_decide_eq_true hrel).2.1
  have hmem : L.upper.sup id ∈ L.upper := by
    simpa using Finset.sup_mem_of_nonempty (f := id) ⟨L.pivot, L.pivot_upper⟩
  have hremain : Macro.Pending (q.position.board.get side) :=
    Or.inr ⟨hselected, L.upper.sup id, hcurrent ▸ hmem, hidx ▸ L.pivot_lt_upper_sup hd⟩
  have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation hp
  have hnext := winning_fresh_nonlast_other_pending hHN hH blue
    (hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)) side hn hrel hsep
    hremain (by rw [hother]; exact hstart)
  simpa only [hother] using hnext

#print axioms winning_fresh_nonlast_other_pending
#print axioms winning_large_body_other_pending

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
