import ErdosProblems.Erdos118.Reused591.TerminalInsideCounts
import ErdosProblems.Erdos118.Reused591.LastMarkerCounts
import ErdosProblems.Erdos118.Reused591.ReachableRootCard
import ErdosProblems.Erdos118.Reused591.MarkerOrder

namespace Erdos118.Reused591

/-! # Marker/count comparisons with every premise recovered from actual histories -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem terminal_inside_clear_data {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value) :
    ∃ s t : G, Clear q.position.board s t ∧ MaxOrder true q.position.board ∧
      q.position.board.left.coordinates.headD 0 < q.position.board.right.coordinates.headD 0 ∧
      q.position.board.left.rootLabel.card = a := by
  have hv := hwin q value hpath hq
  obtain ⟨_hn, hd, hpay⟩ := (Concrete.kind_terminal_iff (payoff blue) q true).mp (hv ▸ hq)
  have hmodeQ := follow_mode_some hpath hmode
  have hwinning : Winning blue true q.position.board := by
    apply (payoff_true_iff blue true q.position.board).mp
    simpa only [hmodeQ, Option.getD_some] using hpay
  obtain ⟨s, t, hc, _hblue, hmax⟩ := hwinning
  have hhead := positive_opening_head_order blue origin q ha hop hboard hpath
    (by rw [← hc.2.1.coordinates]; exact word_ne_nil t.val)
  have hterm := Board.terminal_of_done hd false
  have hcard := reachable_opening_root_card blue origin q false ha hop
    (by simp [hboard, Board.initial, Board.get]) hpath
    (by intro hs; simp [LabeledWord.terminal, hs] at hterm)
  exact ⟨s, t, hc, hmax, hhead, hcard⟩

theorem terminal_last_marker_lt_iff {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value) :
    q.position.board.left.lastSelectedMarker < q.position.board.right.lastSelectedMarker ↔
      q.position.board.left.beforeLastLeafCount ≤ q.position.board.right.beforeLastLeafCount := by
  obtain ⟨s, t, hc, hmax, hhead, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hpath hq
  obtain ⟨hl, hr, _hpos⟩ := hc.inside_roots_nonempty hhead hmax (by simpa only [hcard] using ha)
  exact hc.last_marker_lt_iff_beforeLastLeafCount_le hhead hmax hl hr

theorem terminal_not_late_before_count_le {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value)
    (hcolor : lateFirstMarkerColor q = false) :
    q.position.board.left.beforeLastLeafCount ≤ q.position.board.right.beforeLastLeafCount := by
  obtain ⟨s, t, hc, hmax, hhead, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hpath hq
  obtain ⟨hl, hr, _hpos⟩ := hc.inside_roots_nonempty hhead hmax (by simpa only [hcard] using ha)
  have hne := hc.lastSelectedMarker_ne hl hr
  have hn : ¬ q.position.board.right.lastSelectedMarker <
      q.position.board.left.lastSelectedMarker :=
    of_decide_eq_false hcolor
  exact (hc.last_marker_lt_iff_beforeLastLeafCount_le hhead hmax hl hr).mp (by omega)

def alignedBodyCountColor {N : Set ℕ} (q : Concrete.Hist N) : Bool :=
  decide (q.position.board.left.beforeLastLeafCount = q.position.board.right.beforeLastLeafCount)

theorem terminal_aligned_right_root_large {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value)
    (hcolor : alignedBodyCountColor q = true) : 2 ≤ q.position.board.right.rootLabel.card := by
  obtain ⟨s, t, hc, hmax, hhead, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hpath hq
  obtain ⟨_hl, hr, hpos⟩ := hc.inside_roots_nonempty hhead hmax (by simpa only [hcard] using ha)
  have heq := of_decide_eq_true hcolor
  exact (hc.2.1.beforeLastLeafCount_pos_iff hr).mp (heq ▸ hpos)

#print axioms terminal_inside_clear_data
#print axioms terminal_last_marker_lt_iff
#print axioms terminal_not_late_before_count_le
#print axioms terminal_aligned_right_root_large

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
