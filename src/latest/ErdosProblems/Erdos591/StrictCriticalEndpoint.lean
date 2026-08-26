import ErdosProblems.Erdos591.AlignedCriticalEndpoint

/-!
# The strict critical leaf is before the opposite last selected body

Its suffix has strictly more selections than a penultimate endpoint.
If its current selected body is exhausted, an additional selected body
lies strictly between it and the last body. All statements are recovered
from a genuine terminal extension and then refer to the original cursor.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem ClearSide.relaxed_before_last_of_suffix_gt
    {v last : LabeledWord} {s t : G} {xs ys : List (Finset ℕ × ℕ)}
    (_h : ClearSide last s t)
    (hinit : LabeledWord.LegalRun LabeledWord.initial xs v)
    (htail : LabeledWord.LegalRun v ys last) (hr : v.relaxed = true)
    (hcount : last.lastSelectedLabel.card <
      (last.selectedLeafPairsFrom (v.bodyLabels.length - 1) (v.leafIndex - 1)).card) :
    v.bodyLabels.length < v.lastSelectedBody := by
  have hw := hinit.cursorInvariant LabeledWord.cursorInvariant_initial
  have hsel := (of_decide_eq_true hr).2.1
  have hpos := (hw.2.2.1 _ hsel).1
  have hroot := htail.rootLabel_eq (LabeledWord.relaxed_ne_start hw hr)
  have hlast : last.lastSelectedBody = v.lastSelectedBody :=
    congrArg (fun C : Finset ℕ => C.sup id) hroot
  have hle : v.bodyLabels.length ≤ v.lastSelectedBody := Finset.le_sup (f := id) hsel
  by_contra hn
  have hindex : v.bodyLabels.length - 1 + 1 = last.lastSelectedBody := by omega
  have hbound := LabeledWord.selectedLeafPairsFrom_last_body_card_le
    (j := v.leafIndex - 1) hindex
  exact not_lt_of_ge hbound hcount

theorem history_strict_critical_endpoint {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hfirst : q.position.board.left.coordinates.headD 0 <
      q.position.board.right.coordinates.headD 0)
    (hstrict : q.position.board.left.beforeLastLeafCount <
      q.position.board.right.beforeLastLeafCount)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.left.rootLabel,
      k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length)
    (hn : p.position.board.left.NoLeafPending) :
    p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody ∧
      (p.position.board.right.NoLeafPending → ∃ k ∈ p.position.board.right.rootLabel,
        p.position.board.right.bodyLabels.length < k ∧
          k < p.position.board.right.lastSelectedBody) := by
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
  have htotal := hc.inside_last_body_count hfirst hmax hlroot hrroot
  have hleft := (hc.1.relaxed_penultimate_iff_suffix_card ha hcs hl).mpr ⟨hbefore, hpen, hn⟩
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  have hright : q.position.board.right.lastSelectedLabel.card + 1 <
      (q.position.board.right.selectedLeafPairsFrom (p.position.board.right.bodyLabels.length - 1)
        (p.position.board.right.leafIndex - 1)).card := by omega
  have hbody := hc.2.1.relaxed_before_last_of_suffix_gt hb hds hr (by omega)
  refine ⟨hbody, ?_⟩
  intro hno
  by_contra hnot
  have hpenR : ∀ k ∈ p.position.board.right.rootLabel,
      k < p.position.board.right.lastSelectedBody →
        k ≤ p.position.board.right.bodyLabels.length := by
    intro k hk hkLast
    by_contra hn
    exact hnot ⟨k, hk, lt_of_not_ge hn, hkLast⟩
  have hcount := (hc.2.1.relaxed_penultimate_iff_suffix_card hb hds hr).mpr ⟨hbody, hpenR, hno⟩
  omega

theorem winning_strict_critical_endpoint {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.left.rootLabel,
      k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length)
    (hn : p.position.board.left.NoLeafPending) :
    p.position.board.right.bodyLabels.length < p.position.board.right.lastSelectedBody ∧
      (p.position.board.right.NoLeafPending → ∃ k ∈ p.position.board.right.rootLabel,
        p.position.board.right.bodyLabels.length < k ∧
          k < p.position.board.right.lastSelectedBody) := by
  obtain ⟨q, hpq, hq⟩ := (hwin.of_reachable (exactGame N blue) hfrom).exists_terminal
    (exactGame N blue) hHN hH
  have hpath := hfrom.trans hpq
  obtain ⟨s, t, hc, hmax, hfirst, _hcard⟩ :=
    terminal_inside_clear_data blue origin q ha hop hboard hmode hwin hpath hq
  exact history_strict_critical_endpoint (follow_history_path hpq) hc hmax hfirst
    (hall q true hpath hq) hl hr horder hbefore hpen hn

#print axioms ClearSide.relaxed_before_last_of_suffix_gt
#print axioms history_strict_critical_endpoint
#print axioms winning_strict_critical_endpoint

end Erdos591.Positive.Game.Payoff
