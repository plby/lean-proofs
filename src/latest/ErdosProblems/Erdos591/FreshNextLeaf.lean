import ErdosProblems.Erdos591.NextLeafEndpoint
import ErdosProblems.Erdos591.PendingNextLeaf

/-! # The next selected leaf with the fresh opposite word unchanged -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_next_leaf_after_other {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) {j : ℕ} (hup : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hstrict : (p.position.board.get side).leafIndex < j)
    (hnext : ∀ x ∈ (p.position.board.get side).currentLabel,
      (p.position.board.get side).leafIndex < x → j ≤ x)
    (hother : (p.position.board.get (!side)).relaxed = true)
    (hsep : ∀ x ∈ (p.position.board.get side).coordinates,
      x ≤ (p.position.board.get (!side)).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  obtain ⟨v, hpv, hboard, hp⟩ :=
    winning_next_leaf_request_after_other hHN hH blue hwin side hup hstrict hother hsep
  have hk : (exactGame N blue).kind v = .builder :=
    (Concrete.kind_builder_iff (payoff blue) v).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH v hk (b v)
  let q := Concrete.response v u
  have hs : (exactGame N blue).FollowStep σ H b v q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ v u hk hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  obtain ⟨hqr, hqi, hqb, hqm⟩ := hr.next_leaf_endpoint
    ((Position.history_dataInvariant v).2.1 side).1
    ((Position.history_dataInvariant q).2.1 side).1
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
    (by simpa only [hboard] using hup) (by simpa only [hboard] using hstrict)
    (by simpa only [hboard] using hnext)
  have hn := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)).no_pending_after_reply hp
  exact ⟨q, hpv.tail hs, hn, hqr, hqi,
    by simpa only [hboard] using hqb, by simpa only [hboard] using hqm,
    by simpa only [hboard] using hr.other_eq,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation hp⟩

#print axioms winning_next_leaf_after_other

end Erdos591.Positive.Game.Payoff
