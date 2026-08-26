import ErdosProblems.Erdos118.Reused591.CriticalReverseEndpoint

namespace Erdos118.Reused591

/-! # Recover the critical checkpoint using only a localized future tail -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_strict_reverse_endpoint_on_subset {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.left.beforeLastLeafCount < q.position.board.right.beforeLastLeafCount)
    (hfixed : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
          (p.position.board.right.rootLabel.filter
            (fun i => i ≤ p.position.board.right.bodyLabels.length)).card ∧
        q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card =
          (p.position.board.right.currentLabel.filter
            (fun j => j ≤ p.position.board.right.leafIndex)).card)
    (hr : p.position.board.right.relaxed = true)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0) : CriticalCheckpoint p := by
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hKH (fun _ => le_rfl)
  obtain ⟨hl, horder⟩ := winning_left_relaxed_of_right_separation
    (hKH.trans hHN) hK blue hwinP hr hpos hsep
  obtain ⟨q, hpq, hq⟩ := hwinP.exists_terminal (exactGame N blue) (hKH.trans hHN) hK
  have hpathH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpq
  have hfull := hfrom.trans hpathH
  obtain ⟨s, t, hc, hmax, hfirst, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hfull hq
  have hspec := (hc.strict_critical_data hfirst hmax (by simpa only [hcard] using ha)
    (hall q true hfull hq)).2.1
  have hvalues := hfixed q true hpq hq
  exact history_critical_reverse_endpoint (follow_history_path hpq) hc hmax hl hr horder hspec
    hvalues.1 hvalues.2

#print axioms winning_strict_reverse_endpoint_on_subset

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
