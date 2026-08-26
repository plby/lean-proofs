import ErdosProblems.Erdos118.Reused591.ManagedCriticalOpening
import ErdosProblems.Erdos118.Reused591.LateMarkerCritical

namespace Erdos118.Reused591

/-!
# The actual managed critical checkpoint in the late-marker case

Reuse the common managed opposite-leaf opening. The terminal marker
comparison and nonsingleton last-body requests identify the unchanged
opposite word's current body as last, but its current leaf as nonlast.
The saved upper origin is still retained for deferred firing.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_late_critical_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hrel : p.position.board.left.relaxed = true)
    (hsep : ∀ y ∈ p.position.board.right.coordinates,
      y ≤ p.position.board.left.coordinates.getLastD 0)
    (hn : p.position.board.left.NoLeafPending) {i : ℕ}
    (hi : LabeledWord.BeforeBody i p.position.board.left)
    (hnext : ∀ k ∈ p.position.board.left.rootLabel,
      p.position.board.left.bodyLabels.length < k → i ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel, k ≤ i)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left = p.position.board.left ∧ q.position.board.right.relaxed = true ∧
      (∀ y ∈ q.position.board.left.coordinates,
        y ≤ q.position.board.right.coordinates.getLastD 0) ∧
      q.position.board.right.lastSelectedBody = q.position.board.right.bodyLabels.length ∧
      (∃ j ∈ q.position.board.right.currentLabel, q.position.board.right.leafIndex < j) ∧
      2 ≤ q.position.board.right.currentLabel.card ∧
      ∃ M : Managed N H blue b σ t mode other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
  obtain ⟨q, hpq, hpzero, hleft, hqr, hqsep, Mq, hMqfrom⟩ :=
    managed_critical_opening hHN hH blue hwin hrel hsep hi upperOrigin hmanaged
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  obtain ⟨hlastBody, hlater, hcard⟩ := winning_before_late_last_other_nonlast hHN hH blue origin
    hwinq (hfrom.trans hpq) hall hlarge hpzero
    (by simpa only [hleft] using hrel) (by simpa only [hleft] using hn)
    (by simpa only [hleft] using hi) (by simpa only [hleft] using hnext)
    (by simpa only [hleft] using hrootLast) hqr
  exact ⟨q, hpq, hpzero, hleft, hqr, hqsep, hlastBody, hlater, hcard, Mq, hMqfrom⟩

#print axioms inside_late_critical_checkpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
