import ErdosProblems.Erdos118.Reused591.InsideLastSingleton

namespace Erdos118.Reused591

/-!
# Reduction to nonsingleton first and last selected bodies

First thin the initial body requests using the first-singleton theorem.
Then stabilize the terminal last-body singleton test by the fixed-strategy
game. Its true value is excluded by the complete last-singleton theorem.
The false value recovers a size at least two at each actual last request.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_large_endpoint_reduction {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true) :
    2 ≤ a ∧ ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      (∀ q v d, (exactGame N blue).FollowStep σ L c p q →
        (exactGame N blue).FollowStep σ L c q v →
        v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d) ∧
      (∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
        q.position.pending = some ⟨false, .advance d⟩ →
        q.position.board.left.markerEvent = true →
        (∀ k ∈ q.position.board.left.rootLabel,
          k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d) ∧
      ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = false := by
  obtain ⟨haLarge, I, hIH, hI, hfirst⟩ :=
    inside_large_first_body_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  obtain ⟨L, hLI, hL, c, hbc, value, hvalue⟩ :=
    (exactGame N blue).terminal_bool_uniformization (hIH.trans hHN) hI b σ
      (lastBodySingletonColor false)
  have hLH := hLI.trans hIH
  have hLN := hLH.trans hHN
  have hwinL := hwin.mono (exactGame N blue) hLH hbc
  have hrootL := hroot.mono (exactGame N blue) hLH hbc
  cases hv : value p with
  | true =>
      exact (inside_last_singleton_triangle hLN hL blue hrootL hwinL ha hp hboard hmode
        (fun z w hpath hz => by simpa only [hv] using hvalue p z w hpath hz) htri).elim
  | false =>
      have hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
          (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = false :=
        fun z w hpath hz => by simpa only [hv] using hvalue p z w hpath hz
      refine ⟨haLarge, L, hLH, hL, c, hbc, ?_, ?_, hall⟩
      · intro q v d hpq hqv hpv
        exact hfirst q v d
          (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hbc hpq)
          (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hbc hqv) hpv
      · intro q d hpath hpend hm hlast
        have hd := winning_pending_marker_size_pos hLN hL blue
          (hwinL.of_reachable (exactGame N blue) hpath) hpend hm
        change 0 < d at hd
        have hobs := pending_last_body_observable hLN hL blue p q false false
          hpath hall hpend rfl hm hlast
        have hne : d ≠ 1 := of_decide_eq_false hobs
        omega

#print axioms inside_large_endpoint_reduction

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
