import ErdosProblems.Erdos118.Reused591.InsideCountAlternative
import ErdosProblems.Erdos118.Reused591.InsideAligned

namespace Erdos118.Reused591

/-!
# Only the strict pre-last count alternative remains

The complete aligned triangle theorem now excludes the equality color.
This reduction preserves the actual strategy, opening history, first
body bound, and last-body bound on an infinite conservative input pool.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_reduction {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G) (htri : blue.CliqueFree 3)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
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
        (exactGame N blue).kind z = .terminal w →
          z.position.board.left.beforeLastLeafCount <
            z.position.board.right.beforeLastLeafCount := by
  obtain ⟨haLarge, L, hLH, hL, c, hbc, hfirst, hlarge, aligned, hcolors⟩ :=
    inside_count_alternative hHN hH blue htri hroot hwin ha hp hboard hmode
  cases aligned with
  | false =>
      refine ⟨haLarge, L, hLH, hL, c, hbc, hfirst, hlarge, ?_⟩
      intro z w hpath hz
      simpa only [Bool.false_eq_true, ↓reduceIte] using (hcolors z w hpath hz).2.2.2
  | true =>
      exact ((inside_aligned_triangle (hLH.trans hHN) hL blue
        (hroot.mono (exactGame N blue) hLH hbc) (hwin.mono (exactGame N blue) hLH hbc)
        haLarge hp hboard hmode hlarge (fun z w hpath hz => (hcolors z w hpath hz).2.2.1))
          htri).elim

#print axioms inside_strict_reduction

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
