import ErdosProblems.Erdos118.Reused591.InsideStrictReduction
import ErdosProblems.Erdos118.Reused591.InsideStrictLast
import ErdosProblems.Erdos118.Reused591.FixedBoundThinning

namespace Erdos118.Reused591

/-!
# Only the nonlast critical-leaf alternative remains

Keep the original continuation bound during the final Boolean thinning.
The complete last-critical triangle excludes the true color, leaving
the strict count inequality, both body-size bounds, and false critical
last-leaf color on a single infinite future pool.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_nonlast_reduction {N H : Set ℕ}
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
        (∀ i ∈ q.position.board.left.rootLabel,
          i ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d) ∧
      (∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w →
          z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) ∧
      ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w → criticalLastColor z = false := by
  obtain ⟨haLarge, K, hKH, hK, c, hbc, hfirst, hlarge, hall⟩ :=
    inside_strict_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  obtain ⟨L, hLK, hL, value, hvalue⟩ :=
    Concrete.terminal_finite_uniformization_fixed_bound (hKH.trans hHN) hK c σ criticalLastColor p
  have steps {q v : Concrete.Hist N}
      (hs : (exactGame N blue).FollowStep σ L c q v) :
      (exactGame N blue).FollowStep σ K c q v :=
    FiniteResponseGame.FollowStep.mono (exactGame N blue) hLK (fun _ => le_rfl) hs
  have paths {q v : Concrete.Hist N}
      (hs : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) q v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K c) q v :=
    Relation.ReflTransGen.mono (fun _ _ hs => steps hs) _ _ hs
  have hFirstL : ∀ q v d, (exactGame N blue).FollowStep σ L c p q →
      (exactGame N blue).FollowStep σ L c q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d :=
    fun q v d hpq hqv hv => hfirst q v d (steps hpq) (steps hqv) hv
  have hLargeL : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ i ∈ q.position.board.left.rootLabel, i ≤ q.position.board.left.bodyLabels.length + 1) →
      2 ≤ d := fun q d hpq hp hm hr => hlarge q d (paths hpq) hp hm hr
  have hAllL : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
      (exactGame N blue).kind z = .terminal w →
      z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount :=
    fun z w hpz hz => hall z w (paths hpz) hz
  cases value with
  | false => exact ⟨haLarge, L, hLK.trans hKH, hL, c, hbc, hFirstL, hLargeL, hAllL, hvalue⟩
  | true =>
      exact ((inside_strict_last_triangle ((hLK.trans hKH).trans hHN) hL blue
        (hroot.mono (exactGame N blue) (hLK.trans hKH) hbc)
        (hwin.mono (exactGame N blue) (hLK.trans hKH) hbc) haLarge hp hboard hmode
        hFirstL hLargeL hAllL hvalue) htri).elim

#print axioms inside_nonlast_reduction

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
