import ErdosProblems.Erdos591.PenultimateCursorCounts
import ErdosProblems.Erdos591.RelaxedSuffixCounts
import ErdosProblems.Erdos591.TerminalMarkerCounts

/-!
# The aligned critical opposite leaf is a penultimate-body endpoint

The first relaxed suffix has one selected leaf followed by its last
body's selections. Consecutive suffix balance and the aligned last-body
identity force precisely the same endpoint description on the second
word. A winning test continuation transfers this fact to the original
partial history without changing any inputs or requested labels.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem history_aligned_penultimate_endpoint_iff {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hfirst : q.position.board.left.coordinates.headD 0 <
      q.position.board.right.coordinates.headD 0)
    (haligned : q.position.board.left.beforeLastLeafCount =
      q.position.board.right.beforeLastLeafCount)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0) :
    (p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody ∧
      (∀ k ∈ p.position.board.left.rootLabel,
        k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length) ∧
      p.position.board.left.NoLeafPending) ↔
    p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody ∧
      (∀ k ∈ p.position.board.right.rootLabel,
        k < p.position.board.right.lastSelectedBody →
          k ≤ p.position.board.right.bodyLabels.length) ∧
      p.position.board.right.NoLeafPending := by
  obtain ⟨as, ha⟩ := History.word_run p false
  obtain ⟨bs, hb⟩ := History.word_run p true
  obtain ⟨cs, hcs, _⟩ := (History.reachable_word_extension hpath).2 false
  obtain ⟨ds, hds, _⟩ := (History.reachable_word_extension hpath).2 true
  change LabeledWord.LegalRun LabeledWord.initial as p.position.board.left at ha
  change LabeledWord.LegalRun LabeledWord.initial bs p.position.board.right at hb
  change LabeledWord.LegalRun p.position.board.left cs q.position.board.left at hcs
  change LabeledWord.LegalRun p.position.board.right ds q.position.board.right at hds
  have hlroot : q.position.board.left.rootLabel.Nonempty := by
    rw [hcs.rootLabel_eq (LabeledWord.relaxed_ne_start
      (ha.cursorInvariant LabeledWord.cursorInvariant_initial) hl)]
    exact ⟨_, (of_decide_eq_true hl).2.1⟩
  have hrroot : q.position.board.right.rootLabel.Nonempty := by
    rw [hds.rootLabel_eq (LabeledWord.relaxed_ne_start
      (hb.cursorInvariant LabeledWord.cursorInvariant_initial) hr)]
    exact ⟨_, (of_decide_eq_true hr).2.1⟩
  have hlast := hc.aligned_last_body_count hfirst hmax hlroot hrroot haligned
  have hleft := hc.1.relaxed_penultimate_iff_suffix_card ha hcs hl
  have hright := hc.2.1.relaxed_penultimate_iff_suffix_card hb hds hr
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  constructor
  · intro hL
    have hcount := hleft.mpr hL
    apply hright.mp
    omega
  · intro hR
    have hcount := hright.mpr hR
    apply hleft.mp
    omega

theorem history_aligned_penultimate_endpoint {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hfirst : q.position.board.left.coordinates.headD 0 <
      q.position.board.right.coordinates.headD 0)
    (haligned : q.position.board.left.beforeLastLeafCount =
      q.position.board.right.beforeLastLeafCount)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.left.rootLabel,
      k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length)
    (hn : p.position.board.left.NoLeafPending) :
    p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody ∧
      (∀ k ∈ p.position.board.right.rootLabel,
        k < p.position.board.right.lastSelectedBody →
          k ≤ p.position.board.right.bodyLabels.length) ∧
      p.position.board.right.NoLeafPending :=
  (history_aligned_penultimate_endpoint_iff hpath hc hmax hfirst haligned hl hr horder).mp
    ⟨hbefore, hpen, hn⟩

theorem winning_aligned_critical_endpoint {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.left.rootLabel,
      k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length)
    (hn : p.position.board.left.NoLeafPending) :
    p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody ∧
      (∀ k ∈ p.position.board.right.rootLabel,
        k < p.position.board.right.lastSelectedBody →
          k ≤ p.position.board.right.bodyLabels.length) ∧
      p.position.board.right.NoLeafPending := by
  obtain ⟨q, hpq, hq⟩ := (hwin.of_reachable (exactGame N blue) hfrom).exists_terminal
    (exactGame N blue) hHN hH
  have hpath := hfrom.trans hpq
  obtain ⟨s, t, hc, hmax, hfirst, _hcard⟩ :=
    terminal_inside_clear_data blue origin q ha hop hboard hmode hwin hpath hq
  exact history_aligned_penultimate_endpoint (follow_history_path hpq) hc hmax hfirst
    (of_decide_eq_true (hall q true hpath hq)) hl hr horder hbefore hpen hn

#print axioms history_aligned_penultimate_endpoint
#print axioms history_aligned_penultimate_endpoint_iff
#print axioms winning_aligned_critical_endpoint

end Erdos591.Positive.Game.Payoff
