import ErdosProblems.Erdos591.ManagedCriticalOpening
import ErdosProblems.Erdos591.InsideSingletonCritical

/-!
# The critical last opposite leaf before a singleton last first-word body

From the last selected leaf of the penultimate first-word body, advance
the managed second word to its next selected leaf. Its next request is
the first word's still-unsubmitted size-zero advance. Uniform singleton
terminal data prove that this second-word leaf is already its last.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_singleton_critical_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true)
    (hmode : p.position.mode = some true)
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
      ¬ Macro.Pending q.position.board.right ∧
      ∃ M : Managed N H blue b σ t mode other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
  obtain ⟨q, hpq, hpzero, hleft, hqr, hqsep, Mq, hMqfrom⟩ :=
    managed_critical_opening hHN hH blue hwin hrel hsep hi upperOrigin hmanaged
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  have hlast := winning_before_singleton_last_other_exhausted hHN hH blue origin hwinq
    (hfrom.trans hpq) hall (follow_mode_some hpq hmode) hpzero
    (by simpa only [hleft] using hrel) (by simpa only [hleft] using hn)
    (by simpa only [hleft] using hi) (by simpa only [hleft] using hnext)
    (by simpa only [hleft] using hrootLast)
    (Mq.not_start ((Position.history_dataInvariant q).2.1 true).1)
  exact ⟨q, hpq, hpzero, hleft, hqr, hqsep, hlast, Mq, hMqfrom⟩

#print axioms inside_singleton_critical_checkpoint

end Erdos591.Positive.Game.Payoff
