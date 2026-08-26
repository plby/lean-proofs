import ErdosProblems.Erdos591.InsideNonlastReduction
import ErdosProblems.Erdos591.InsideStrictNonlast
import ErdosProblems.Erdos591.InsideOpening

/-! # Every conservative winning architect yields a blue triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_positive_opening_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true) :
    ¬ blue.CliqueFree 3 := by
  intro htri
  obtain ⟨haLarge, L, hLH, hL, c, hbc, hfirst, _hlarge, hall, hlast⟩ :=
    inside_nonlast_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  exact inside_strict_nonlast_triangle (hLH.trans hHN) hL blue
    (hroot.mono (exactGame N blue) hLH hbc) (hwin.mono (exactGame N blue) hLH hbc)
    haLarge hp hboard hmode hfirst hall hlast htri

theorem architect_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hwin : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial)) :
    ¬ blue.CliqueFree 3 := by
  intro htri
  obtain ⟨d, hd, hreq, hchoice⟩ := winning_opening_inside hHN hH blue htri σ hwin
  let p := History.initial (Position.Next N) Position.initial
  let q := p.append (Position.initial.request true ⟨false, .advance d⟩) hreq
  have hs : (exactGame N blue).FollowStep σ H b p q := by
    dsimp only [q, p]
    rw [← hchoice]
    exact FiniteResponseGame.FollowStep.architect (exactGame N blue) σ
      _ (initial_architect N blue)
  exact inside_positive_opening_triangle hHN hH blue hwin
    (hwin.of_reachable (exactGame N blue) (.single hs)) hd rfl rfl rfl htri

#print axioms inside_positive_opening_triangle
#print axioms architect_triangle

end Erdos591.Positive.Game.Payoff
