import ErdosProblems.Erdos591.ManagedCheckpoint
import ErdosProblems.Erdos591.PrepareRootHistory

/-!
# Entering the managed two-word construction

A managed selected-body marker is advanced to its first leaf using one
actual strategy request and one managed response. When its opposite
word is still initial in an outside play, the next strategy request
must be a positive initial advance on that opposite word.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem Position.Next.reply_of_pending_fresh {N : Set ℕ} {p q : Position}
    (h : Position.Next N q p) {r : Request} (hp : p.pending = some r) :
    ∃ u, Reply p.board r u q.board ∧ ∀ x ∈ u, p.bound < x := by
  cases h with
  | request p mode s ht _ _ _ => simp [hp] at ht
  | reply p s u board hs hr _ hf =>
      have heq : s = r := Option.some.inj (hs.symm.trans hp)
      exact ⟨u, heq ▸ hr, hf⟩

namespace Relay.Managed

theorem first_body {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (s : Bool)
    (hp : p.position.pending = none) (hm : (p.position.board.get s).markerEvent = true)
    {t mode : Bool} {other : LabeledWord}
    (M : Managed N H blue b σ t mode other (p.position.board.get s)) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get s).relaxed = true ∧
      q.position.board.get (!s) = p.position.board.get (!s) ∧
      Nonempty (Managed N H blue b σ t mode other (q.position.board.get s)) := by
  obtain ⟨p', d, hrequest, hboard, hpend, hd⟩ :=
    winning_request_at_marker hHN hH blue hwin s hp hm
  have hwin' := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hrequest)
  have M' : Managed N H blue b σ t mode other (p'.position.board.get s) := by
    rw [hboard]
    exact M
  have hm' : (p'.position.board.get s).markerEvent = true := by simpa [hboard] using hm
  have hnot : ¬ BothLast p'.position.board := fun hl => hl s (Macro.marker_pending hm')
  obtain ⟨q, hs, hn, ho, hM⟩ := M'.respond hHN hH blue hwin' hpend hnot
  have hnext := History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs)
  obtain ⟨u, hr, hf⟩ := hnext.reply_of_pending_fresh hpend
  have hrel := hr.advance_selected_leaf ((Position.history_dataInvariant p').2.1 s).1
    hm' hd (fun x hx => (Nat.zero_le p'.position.bound).trans_lt (hf x hx))
  exact ⟨q, (Relation.ReflTransGen.single hrequest).tail hs, hn, hrel,
    by simpa [hboard] using ho, hM⟩

end Relay.Managed

namespace Payoff

theorem outside_initial_right_request {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some false) (hp : p.position.pending = none)
    (hi : p.position.board.get true = LabeledWord.initial)
    (hr : (p.position.board.get false).relaxed = true)
    (hlive : (p.position.board.get false).terminal = false) :
    ∃ q d, (exactGame N blue).FollowStep σ H b p q ∧ q.position.board = p.position.board ∧
      q.position.pending = some ⟨true, .advance d⟩ ∧ 0 < d := by
  have hk : (exactGame N blue).kind p = .architect :=
    (Concrete.kind_architect_iff (payoff blue) p).mpr
      ⟨hp, Board.not_done_of_live hlive⟩
  obtain ⟨mode, r, hnext, heq⟩ := Concrete.architect_choice (payoff blue) σ p hk
  let q := p.append (p.position.request mode r) hnext
  have hs : (exactGame N blue).FollowStep σ H b p q := by
    simpa only [heq] using FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hboard : q.position.board = p.position.board := by simp [q, Position.request]
  have hpend : q.position.pending = some r := by simp [q, Position.request]
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  have hside : r.side = true := winning_pending_switch hHN hH blue hwinq hpend false
    (by simpa [hboard] using hr) (by simp [hboard, hi, LabeledWord.initial])
  obtain ⟨d, hd, he⟩ := winning_initial_larger_request_positive hHN hH blue hwinq
    (follow_mode_some (Relation.ReflTransGen.single hs) hmode) hpend hside
    (by simpa [hboard, hside] using hi) (by simpa [hboard] using hlive)
  exact ⟨q, d, hs, hboard, by simpa [he] using hpend, hd⟩

end Payoff

#print axioms Relay.Managed.first_body
#print axioms Payoff.outside_initial_right_request

end Erdos591.Positive.Game
