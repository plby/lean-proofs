import ErdosProblems.Erdos118.Reused591.OpeningCoordinateOrder
import ErdosProblems.Erdos118.Reused591.InsideCutCounts

namespace Erdos118.Reused591

/-! # Selected-leaf count identities at actual winning inside terminals -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem terminal_inside_selectedLeafCount {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value) :
    q.position.board.left.selectedLeafCount = q.position.board.right.selectedLeafCount + 1 := by
  have hv := hwin q value hpath hq
  have hpay := ((Concrete.kind_terminal_iff (payoff blue) q true).mp (hv ▸ hq)).2.2
  have hmodeQ := follow_mode_some hpath hmode
  have hwinning : Winning blue true q.position.board := by
    apply (payoff_true_iff blue true q.position.board).mp
    simpa only [hmodeQ, Option.getD_some] using hpay
  obtain ⟨s, t, hc, _hblue, hmax⟩ := hwinning
  have hhead := positive_opening_head_order blue origin q ha hop hboard hpath
    (by rw [← hc.2.1.coordinates]; exact word_ne_nil t.val)
  exact hc.inside_selectedLeafCount hhead hmax

theorem terminal_inside_last_body_count {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value)
    (hl : q.position.board.left.rootLabel.Nonempty)
    (hr : q.position.board.right.rootLabel.Nonempty) :
    q.position.board.left.beforeLastLeafCount + q.position.board.left.lastSelectedLabel.card =
      q.position.board.right.beforeLastLeafCount + q.position.board.right.lastSelectedLabel.card +
        1 := by
  simpa only [LabeledWord.selectedLeafCount_decomposition hl,
    LabeledWord.selectedLeafCount_decomposition hr] using
      terminal_inside_selectedLeafCount blue origin q ha hop hboard hmode hwin hpath hq

#print axioms terminal_inside_selectedLeafCount
#print axioms terminal_inside_last_body_count

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
