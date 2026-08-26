import ErdosProblems.Erdos118.Reused591.TerminalMarkerCounts

namespace Erdos118.Reused591

/-! # The aligned terminal condition bounds an actual pending second root -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem aligned_pending_right_root_large {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a e : ℕ} (ha : 2 ≤ a) (he : 0 < e)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨true, .advance e⟩)
    (hinit : p.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) : 2 ≤ e := by
  obtain ⟨q, hpq, hq⟩ := (hwin.of_reachable (exactGame N blue) hfrom).exists_terminal
    (exactGame N blue) hHN hH
  have hpath := hfrom.trans hpq
  have hlarge := terminal_aligned_right_root_large blue origin q ha hop hboard hmode hwin
    hpath hq (hall q true hpath hq)
  have hd := ((Concrete.kind_terminal_iff (payoff blue) q true).mp hq).2.1
  have hterm := Board.terminal_of_done hd true
  have hcard := reachable_opening_root_card blue p q true he hp hinit hpq
    (by intro hs; simp [LabeledWord.terminal, hs] at hterm)
  change q.position.board.right.rootLabel.card = e at hcard
  simpa only [hcard] using hlarge

#print axioms aligned_pending_right_root_large

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
