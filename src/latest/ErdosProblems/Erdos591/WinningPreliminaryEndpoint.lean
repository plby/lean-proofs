import ErdosProblems.Erdos591.PreliminaryEndpointRank
import ErdosProblems.Erdos591.StrictCriticalData
import ErdosProblems.Erdos591.LocalCriticalEndpoint

/-! # The preliminary endpoint rank from the original winning opening -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_preliminary_last_rank {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hOld : CriticalCheckpoint old)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hSlast : p.position.board.left.bodyLabels.length = p.position.board.left.lastSelectedBody)
    (hTbody : p.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hTno : p.position.board.right.NoLeafPending)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    (p.position.board.left.currentLabel.filter
      (fun x => x ≤ p.position.board.left.leafIndex)).card =
        old.position.board.right.currentLabel.card -
          (old.position.board.right.currentLabel.filter
            (fun x => x ≤ old.position.board.right.leafIndex)).card := by
  obtain ⟨q, w, hpq, hq⟩ := (exactGame N blue).terminal_reachable_of_infinite
    (hKH.trans hHN) hK b σ p
  have hpqH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpq
  have hfull := hfrom.trans (holdp.trans hpqH)
  obtain ⟨s, t, hc, hmax, hfirst, hcardRoot⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hfull hq
  have hspec := (hc.strict_critical_data hfirst hmax
    (by simpa only [hcardRoot] using ha) (hall q w hfull hq)).2.1
  exact history_preliminary_last_rank (follow_history_path holdp) (follow_history_path hpq)
    hOld hc hmax hl hr horder hSlast hTbody hTno hspec

#print axioms winning_preliminary_last_rank

end Erdos591.Positive.Game.Payoff
