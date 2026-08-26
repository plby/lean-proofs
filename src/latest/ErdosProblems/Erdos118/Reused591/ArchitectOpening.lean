import ErdosProblems.Erdos118.Reused591.ZeroTriangle

namespace Erdos118.Reused591

/-!
# A triangle-free winning architect opens with a positive advance

The actual initial request selects the first word. The checked
zero-opening triangle excludes both a finish and a zero-size advance,
leaving exactly a positive root-label request for the remaining cases.
-/

namespace Erdos591.Positive.Game

theorem Position.Next.opening_side {N : Set ℕ} {p q : Position}
    (h : Position.Next N q p) {r : Request} (hp : p.mode = none)
    (hq : q.pending = some r) : r.side = false := by
  cases h with
  | request p mode s _ _ _ hfirst =>
      have heq : s = r := Option.some.inj hq
      subst s
      exact hfirst hp
  | reply p s u board _ _ _ _ => simp [Position.reply] at hq

namespace Payoff

open Erdos591.Negative.Exact

theorem initial_architect (N : Set ℕ) (blue : SimpleGraph G) :
    (exactGame N blue).kind (History.initial (Position.Next N) Position.initial) =
      .architect := rfl

theorem winning_opening_positive {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy)
    (hwin : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial)) :
    ∃ mode d, 0 < d ∧
      ∃ hreq : Position.Next N (Position.initial.request mode ⟨false, .advance d⟩) Position.initial,
        σ.move (History.initial (Position.Next N) Position.initial) (initial_architect N blue) =
          (History.initial (Position.Next N) Position.initial).append
            (Position.initial.request mode ⟨false, .advance d⟩) hreq := by
  let p := History.initial (Position.Next N) Position.initial
  have hk : (exactGame N blue).kind p = .architect := initial_architect N blue
  obtain ⟨mode, r, hreq, hchoice⟩ := Concrete.architect_choice (payoff blue) σ p hk
  have hside : r.side = false := hreq.opening_side rfl rfl
  let q := p.append (p.position.request mode r) hreq
  have hfollow : (exactGame N blue).FollowStep σ H b p q := by
    dsimp only [q]
    rw [← hchoice]
    exact FiniteResponseGame.FollowStep.architect (exactGame N blue) σ p hk
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hfollow)
  have hpending : q.position.pending = some r := by simp [q, Position.request]
  have hboard : q.position.board = Board.initial := by
    dsimp only [q]
    rw [History.position_append]
    rfl
  have hpos : 0 < r.size := by
    by_contra hn
    have hz : r.size = 0 := by omega
    exact pending_initial_zero_triangle hHN hH blue hqwin hpending hboard hside hz htri
  have hex : ∃ d, 0 < d ∧ r.command = .advance d := by
    cases hc : r.command with
    | finish => simp [Request.size, hc] at hpos
    | advance d => exact ⟨d, by simpa [Request.size, hc] using hpos, rfl⟩
  obtain ⟨d, hd, hc⟩ := hex
  have hr : r = ⟨false, .advance d⟩ := by
    have heq : r = ⟨r.side, r.command⟩ := rfl
    simpa only [hside, hc] using heq
  subst r
  exact ⟨mode, d, hd, hreq, hchoice⟩

#print axioms winning_opening_positive

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
