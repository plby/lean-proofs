import ErdosProblems.Erdos118.Reused591.InsideFirstSingleton
import ErdosProblems.Erdos118.Reused591.InsideOneBody

namespace Erdos118.Reused591

/-! # Reduction to multiple selected bodies and uniformly nonsingleton first bodies -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_large_first_body_reduction {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true) :
    2 ≤ a ∧ ∃ L, L ⊆ H ∧ L.Infinite ∧
      ∀ q v d, (exactGame N blue).FollowStep σ L b p q →
        (exactGame N blue).FollowStep σ L b q v →
        v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d := by
  have ha₂ : 2 ≤ a := by
    by_contra hn
    have he : a = 1 := by omega
    subst a
    exact inside_one_body_triangle hHN hH blue hroot hwin hp hboard hmode htri
  refine ⟨ha₂, ?_⟩
  obtain ⟨L, hLH, hL, single, hfirst⟩ := first_body_history_dichotomy hHN hH blue hwin ha hp
    (by simp [hboard, Board.initial])
  cases single with
  | false =>
      refine ⟨L, hLH, hL, ?_⟩
      intro q v d hq hv hpv
      have hd := hfirst q v d hq hv hpv
      have hne : d ≠ 1 := fun he => Bool.false_ne_true (hd.2.mp he)
      omega
  | true =>
      exact (inside_first_singleton_triangle (hLH.trans hHN) hL blue
        (hroot.mono (exactGame N blue) hLH (fun _ => le_rfl))
        (hwin.mono (exactGame N blue) hLH (fun _ => le_rfl)) ha₂ hp hboard hmode
        (fun q v d hq hv hpv => (hfirst q v d hq hv hpv).2.mpr rfl) htri).elim

#print axioms inside_large_first_body_reduction

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
