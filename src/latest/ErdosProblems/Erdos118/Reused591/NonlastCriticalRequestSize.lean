import ErdosProblems.Erdos118.Reused591.LocalCriticalUniformization

namespace Erdos118.Reused591

/-!
# A nonlast critical body request has at least two label entries

At an actual selected marker whose rank is the terminal critical rank,
localization recovers a positive leaf rank not equal to the requested
cardinality. This works for the right word of any saved history, not
only the initial left word's first body request.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem nonlast_critical_request_two {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a d j : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hcolor : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hpRank : (p.position.board.right.rootLabel.filter
      (fun i => i ≤ p.position.board.right.bodyLabels.length + 1)).card = j)
    (hfixed : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card = j) :
    2 ≤ d := by
  obtain ⟨L, hLK, hL, s, hs, hsd, hleaf⟩ := strict_critical_leaf_local_of_rank
    hHN hKH hK blue origin p ha hop hboard hmode hwin hfrom hp hm hall hpRank hfixed
  obtain ⟨q, w, hpq, hq⟩ := (exactGame N blue).terminal_reachable_of_infinite
    ((hLK.trans hKH).trans hHN) hL b σ p
  have hpqH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ h => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) (hLK.trans hKH) (fun _ => le_rfl) h) _ _ hpq
  have hfalse := hcolor q w (hfrom.trans hpqH) hq
  have hne : s ≠ d := fun heq => by
    simpa only [hfalse, Bool.false_eq_true] using (hleaf q w hpq hq).2.mpr heq
  omega

#print axioms nonlast_critical_request_two

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
