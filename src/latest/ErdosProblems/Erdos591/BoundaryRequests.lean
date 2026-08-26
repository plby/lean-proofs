import ErdosProblems.Erdos591.OutsideBoundary

/-!
# Obtaining the actual pending completion requests

A live history has a pending request after at most one architect move,
without changing its board. At the exhausted larger-word boundary the
request selects the unfinished smaller word. Once one word completes,
every legal request necessarily selects the other word.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem Request.Legal.selected_unfinished {board : Board} {r : Request}
    (h : r.Legal board) : (board.get r.side).terminal = false := by
  cases hc : r.command with
  | finish => simpa [Request.Legal, hc] using h
  | advance d =>
      exact (show (board.get r.side).AllowedSize d from by
        simpa [Request.Legal, hc] using h).1

namespace Payoff

theorem request_on_live_board {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (p : Concrete.Hist N) (hlive : Concrete.done p.position.board = false) :
    ∃ q r, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧ q.position.pending = some r := by
  cases hp : p.position.pending with
  | some r => exact ⟨p, r, .refl, rfl, hp⟩
  | none =>
      have hk : (exactGame N blue).kind p = .architect :=
        (Concrete.kind_architect_iff (payoff blue) p).mpr ⟨hp, hlive⟩
      obtain ⟨flag, r, hnext, heq⟩ := Concrete.architect_choice (payoff blue) σ p hk
      let q := p.append (p.position.request flag r) hnext
      have hs : (exactGame N blue).FollowStep σ H b p q := by
        simpa only [heq] using FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
      exact ⟨q, r, Relation.ReflTransGen.single hs, by simp [q, Position.request],
        by simp [q, Position.request]⟩

theorem request_smaller_at_boundary {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N} {mode : Bool}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some mode)
    (hlive : (p.position.board.get mode).terminal = false)
    (hstart : (p.position.board.get (!mode)).parser ≠ .start)
    (hn : ¬ Macro.Pending (p.position.board.get (!mode))) :
    ∃ q r, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧ q.position.pending = some r ∧ r.side = mode := by
  obtain ⟨q, r, hpath, hboard, hp⟩ := request_on_live_board σ p (Board.not_done_of_live hlive)
  refine ⟨q, r, hpath, hboard, hp, ?_⟩
  by_contra heq
  have hside : r.side = !mode := Bool.eq_not_of_ne heq
  have ht := winning_pending_larger_no_selection hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode) hp hside
    (by simpa [hboard, hside] using hstart) (by simpa [hboard, hside] using hn)
  rw [hboard, hlive] at ht
  cases ht

theorem request_opposite_complete {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (p : Concrete.Hist N) (side : Bool)
    (hcomplete : (p.position.board.get side).terminal = true)
    (hlive : (p.position.board.get (!side)).terminal = false) :
    ∃ q r, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧ q.position.pending = some r ∧ r.side = !side := by
  obtain ⟨q, r, hpath, hboard, hp⟩ := request_on_live_board σ p (Board.not_done_of_live hlive)
  refine ⟨q, r, hpath, hboard, hp, Bool.eq_not_of_ne ?_⟩
  intro heq
  have ht := ((Position.history_controlInvariant q).2 r hp).selected_unfinished
  rw [hboard, heq, hcomplete] at ht
  cases ht

#print axioms request_smaller_at_boundary
#print axioms request_opposite_complete

end Payoff

end Erdos591.Positive.Game
