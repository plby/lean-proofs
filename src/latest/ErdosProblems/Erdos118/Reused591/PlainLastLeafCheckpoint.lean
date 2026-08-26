import ErdosProblems.Erdos118.Reused591.InsideLastLeafBoundary
import ErdosProblems.Erdos118.Reused591.FreshOppositeLeaf
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-!
# The ordinary opposite endpoint before the sole remaining first-word leaf

No delayed root plan is required. The fresh nonlast first-word leaf
forces an ordinary opposite selected leaf. Leaving the next first-word
reply pending and testing its endpoint proves that all opposite selected
indices are exhausted, including indices in later selected bodies.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem plain_last_leaf_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hrel : p.position.board.left.relaxed = true)
    (hsep : ∀ x ∈ p.position.board.right.coordinates,
      x ≤ p.position.board.left.coordinates.getLastD 0)
    {j : ℕ} (hup : LabeledWord.UpToLeaf j p.position.board.left)
    (hstrict : p.position.board.left.leafIndex < j)
    (hnext : ∀ x ∈ p.position.board.left.currentLabel,
      p.position.board.left.leafIndex < x → j ≤ x)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hlast : ∀ x ∈ p.position.board.left.currentLabel, x ≤ j) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left = p.position.board.left ∧ q.position.board.right.relaxed = true ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ¬ Macro.Pending q.position.board.right := by
  obtain ⟨v, hpv, _hvn, hvr, hvo, hvsep⟩ := winning_next_opposite_leaf hHN hH blue
    hwin false hrel hsep (Or.inr ⟨hup.selected, j, hup.mem, hstrict⟩)
  change v.position.board.left = p.position.board.left at hvo
  obtain ⟨q, hvq, hboard, hp⟩ := winning_next_leaf_request_after_other hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpv) false
    (by simpa only [Board.get, hvo] using hup)
    (by simpa only [Board.get, hvo] using hstrict) hvr hvsep
  have hpq := hpv.trans hvq
  have hqLeft : q.position.board.left = p.position.board.left := by
    simpa only [hboard] using hvo
  have hqRight : q.position.board.right.relaxed = true := by
    simpa only [Board.get, Bool.not_false, hboard] using hvr
  have hqSep : ∀ x ∈ q.position.board.left.coordinates,
      x ≤ q.position.board.right.coordinates.getLastD 0 := by
    simpa only [Board.get, Bool.not_false, hboard] using hvsep
  have hno := winning_before_last_leaf_other_exhausted hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpq) (follow_mode_some hpq hmode) hp
    (by simpa only [hqLeft] using hup) (by simpa only [hqLeft] using hstrict)
    (by simpa only [hqLeft] using hnext) (by simpa only [hqLeft] using hroot)
    (by simpa only [hqLeft] using hlast)
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant q).2.1 true).1 hqRight)
  exact ⟨q, hpq, hp, hqLeft, hqRight, hqSep, hno⟩

#print axioms plain_last_leaf_checkpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
