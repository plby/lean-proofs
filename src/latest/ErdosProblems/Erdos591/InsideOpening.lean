import ErdosProblems.Erdos591.ArchitectOpening
import ErdosProblems.Erdos591.OutsideTriangle

/-!
# A triangle-free winning architect must choose the inside orientation

The zero-opening and positive outside constructions have both been
proved for actual conservative histories. Thus any remaining winning
architect strategy opens with a positive root request in inside mode.
This reduction does not assert the still-required inside construction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_opening_inside {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy)
    (hwin : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial)) :
    ∃ d, 0 < d ∧
      ∃ hreq : Position.Next N (Position.initial.request true ⟨false, .advance d⟩) Position.initial,
        σ.move (History.initial (Position.Next N) Position.initial) (initial_architect N blue) =
          (History.initial (Position.Next N) Position.initial).append
            (Position.initial.request true ⟨false, .advance d⟩) hreq := by
  obtain ⟨mode, d, hd, hreq, hchoice⟩ := winning_opening_positive hHN hH blue htri σ hwin
  cases mode with
  | true => exact ⟨d, hd, hreq, hchoice⟩
  | false =>
      let p := History.initial (Position.Next N) Position.initial
      let q := p.append (Position.initial.request false ⟨false, .advance d⟩) hreq
      have hs : (exactGame N blue).FollowStep σ H b p q := by
        dsimp only [q, p]
        rw [← hchoice]
        exact FiniteResponseGame.FollowStep.architect (exactGame N blue) σ
          _ (initial_architect N blue)
      have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
      exact (outside_positive_opening_triangle hHN hH blue hwinq hd
        rfl rfl rfl htri).elim

#print axioms winning_opening_inside

end Erdos591.Positive.Game.Payoff
