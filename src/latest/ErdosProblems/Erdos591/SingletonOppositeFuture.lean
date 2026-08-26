import ErdosProblems.Erdos591.PendingOpposite
import ErdosProblems.Erdos591.NextMarkerReplayHistory
import ErdosProblems.Erdos591.BoundaryRequests

/-!
# A singleton opposite leaf still has a future selected body

At a fresh first-body leaf, a root label of size at least two leaves a
future selection. Switching forces an opposite selection too. If that
opposite current label is singleton, only a future root index remains.
This locates the pending size-zero response without a cut-count formula.
-/

namespace Erdos591.Positive.Game

theorem LabeledWord.future_root_of_first_body {w : LabeledWord}
    (hcard : 2 ≤ w.rootLabel.card)
    (hfirst : ∀ i ∈ w.rootLabel, w.bodyLabels.length ≤ i) :
    ∃ i ∈ w.rootLabel, w.bodyLabels.length < i := by
  by_contra hn
  have hall : ∀ i ∈ w.rootLabel, i = w.bodyLabels.length := by
    intro i hi
    exact le_antisymm (le_of_not_gt (fun hlt => hn ⟨i, hi, hlt⟩)) (hfirst i hi)
  have hc : w.rootLabel.card ≤ 1 := Finset.card_le_one.mpr
    (fun i hi j hj => (hall i hi).trans (hall j hj).symm)
  omega

theorem LabeledWord.singleton_relaxed_no_leaf_pending {w : LabeledWord}
    (hrel : w.relaxed = true) (hcard : w.currentLabel.card = 1) : w.NoLeafPending := by
  intro i hi
  exact (Finset.card_le_one.mp hcard.le i hi w.leafIndex (of_decide_eq_true hrel).2.2).le

theorem LabeledWord.BeforeBody.least_future {w : LabeledWord} {i : ℕ}
    (h : LabeledWord.BeforeBody i w) :
    ∃ j, LabeledWord.BeforeBody j w ∧
      ∀ k ∈ w.rootLabel, w.bodyLabels.length < k → j ≤ k := by
  classical
  let F := w.rootLabel.filter (fun k => w.bodyLabels.length < k)
  have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr h⟩
  have hj := Finset.mem_filter.mp (Finset.min'_mem F hF)
  exact ⟨F.min' hF, hj, fun k hk hlt => Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hk, hlt⟩)⟩

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_singleton_other_future_request {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hnone : p.position.pending = none)
    (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hcard : 2 ≤ (p.position.board.get side).rootLabel.card)
    (hfirst : ∀ i ∈ (p.position.board.get side).rootLabel,
      (p.position.board.get side).bodyLabels.length ≤ i)
    (hrelOther : (p.position.board.get (!side)).relaxed = true)
    (hcardOther : (p.position.board.get (!side)).currentLabel.card = 1) :
    ∃ i, LabeledWord.BeforeBody i (p.position.board.get (!side)) ∧
      ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
        q.position.board = p.position.board ∧
        q.position.pending = some ⟨!side, .advance 0⟩ := by
  obtain ⟨j, hj, hjlt⟩ := LabeledWord.future_root_of_first_body hcard hfirst
  have hstartOther := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 (!side)).1 hrelOther
  have hotherPending := winning_fresh_nonlast_other_pending hHN hH blue hwin side hnone
    hrel hsep (Or.inl ⟨j, hj, hjlt⟩) hstartOther
  have hno := LabeledWord.singleton_relaxed_no_leaf_pending hrelOther hcardOther
  have hfuture : ∃ i, LabeledWord.BeforeBody i (p.position.board.get (!side)) := by
    rcases hotherPending with ⟨i, hi, hlt⟩ | ⟨_, i, hi, hlt⟩
    · exact ⟨i, hi, hlt⟩
    · exact (not_lt_of_ge (hno i hi) hlt).elim
  obtain ⟨i, hi⟩ := hfuture
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  obtain ⟨q, req, hpath, hboard, hp⟩ := request_on_live_board σ p (Board.not_done_of_live hlive)
  have hwinq := hwin.of_reachable (exactGame N blue) hpath
  have hside := winning_pending_switch hHN hH blue hwinq hp side
    (by simpa only [hboard] using hrel) (by simpa only [hboard] using hsep)
  have hreq := winning_pending_root_advance_zero hHN hH blue hwinq hp (!side) hside
    (by simpa only [hboard] using hrelOther) (by simpa only [hboard] using hi)
  exact ⟨i, hi, q, hpath, hboard, by simpa only [hreq] using hp⟩

#print axioms winning_singleton_other_future_request

end Payoff
end Erdos591.Positive.Game
