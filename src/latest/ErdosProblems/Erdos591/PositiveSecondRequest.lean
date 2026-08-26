import ErdosProblems.Erdos591.SecondZeroTriangle
import ErdosProblems.Erdos591.InitialRequestSelection

/-!
# Every second-word opening in a triangle-free winning play is positive

After a selected first-word leaf with the second word still initial,
the strategy must switch to the second word. The uniform zero-second
triangle excludes a size-zero request in either orientation.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_initial_right_request {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hp : p.position.pending = none) (hi : p.position.board.right = LabeledWord.initial)
    (hr : p.position.board.left.relaxed = true) :
    ∃ q d, (exactGame N blue).FollowStep σ H b p q ∧ q.position.board = p.position.board ∧
      q.position.pending = some ⟨true, .advance d⟩ ∧ 0 < d := by
  have hw := ((Position.history_dataInvariant p).2.1 false).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hr
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
    (by simpa [hboard, Board.get] using hr) (by simp [hboard, Board.get, hi, LabeledWord.initial])
  have hpos := winning_second_request_positive hHN hH blue htri hroot hwinq hpend hside
    (by simpa [hboard] using hi) (by simpa [hboard] using hr)
  obtain ⟨d, hd, he⟩ : ∃ d, 0 < d ∧ r = ⟨true, .advance d⟩ := by
    cases r with
    | mk side command =>
        cases command with
        | finish => simp [Request.size] at hpos
        | advance d =>
            exact ⟨d, hpos, by simpa using congrArg (fun s => Request.mk s (.advance d)) hside⟩
  exact ⟨q, d, hs, hboard, by simpa [he] using hpend, hd⟩

#print axioms winning_initial_right_request

end Erdos591.Positive.Game.Payoff
