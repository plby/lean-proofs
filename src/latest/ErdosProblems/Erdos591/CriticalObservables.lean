import ErdosProblems.Erdos591.CriticalPair
import ErdosProblems.Erdos591.AlignedCriticalEndpoint

/-!
# Canonical terminal observables recover the actual critical cursor

The penultimate first-word endpoint fixes the suffix count of the
opposite critical leaf. Uniqueness then identifies its exact body and
leaf indices, not merely their counts. Consequently terminal colors
recover the current body's ordinal position, the current leaf's ordinal
position, and whether it is the body's last selected leaf.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact

namespace LabeledWord

theorem LegalRun.criticalPair_eq_of_suffix_card
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)} {n : ℕ}
    (hinit : LegalRun initial xs v) (htail : LegalRun v ys last) (hr : v.relaxed = true)
    (hcount : (last.selectedLeafPairsFrom (v.bodyLabels.length - 1) (v.leafIndex - 1)).card = n) :
    last.criticalPair n = ⟨v.bodyLabels.length, v.leafIndex⟩ := by
  have hw := hinit.cursorInvariant cursorInvariant_initial
  have hstart := relaxed_ne_start hw hr
  have hsel := of_decide_eq_true hr
  have hpos := (hw.2.2.1 _ hsel.2.1).1
  have hbody : last.bodyLabels.getD (v.bodyLabels.length - 1) ∅ = v.currentLabel := by
    rw [htail.body_getD_eq hstart (by omega)]
    exact (currentLabel_eq_getD (by omega)).symm
  apply criticalPair_eq_of_spec
  refine ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, hpos, hsel.1, hcount⟩
  · rw [htail.rootLabel_eq hstart]
    exact hsel.2.1
  · rw [hbody]
    exact hsel.2.2

theorem LegalRun.critical_observables_of_suffix_card
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)} {n : ℕ}
    (hinit : LegalRun initial xs v) (htail : LegalRun v ys last) (hr : v.relaxed = true)
    (hcount : (last.selectedLeafPairsFrom (v.bodyLabels.length - 1) (v.leafIndex - 1)).card = n) :
    last.criticalBodyRank n = (v.rootLabel.filter (fun i => i ≤ v.bodyLabels.length)).card ∧
      last.criticalLeafRank n = (v.currentLabel.filter (fun j => j ≤ v.leafIndex)).card ∧
      (last.criticalLast n = true ↔ v.NoLeafPending) := by
  classical
  have hw := hinit.cursorInvariant cursorInvariant_initial
  have hstart := relaxed_ne_start hw hr
  have hsel := of_decide_eq_true hr
  have hpos := (hw.2.2.1 _ hsel.2.1).1
  have hpair := hinit.criticalPair_eq_of_suffix_card htail hr hcount
  have hbody : last.bodyLabels.getD (v.bodyLabels.length - 1) ∅ = v.currentLabel := by
    rw [htail.body_getD_eq hstart (by omega)]
    exact (currentLabel_eq_getD (by omega)).symm
  simp only [criticalBodyRank, criticalLeafRank, criticalLast, hpair, hbody,
    htail.rootLabel_eq hstart, decide_eq_true_eq, NoLeafPending, and_self]

end LabeledWord

namespace Payoff

noncomputable def criticalLastColor {N : Set ℕ} (q : Concrete.Hist N) : Bool :=
  q.position.board.right.criticalLast q.position.board.left.lastSelectedLabel.card

noncomputable def criticalBodyColor {N : Set ℕ} (e : ℕ) (q : Concrete.Hist N) : Fin (e + 1) :=
  ⟨min (q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card) e,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

noncomputable def criticalLeafColor {N : Set ℕ} (d : ℕ) (q : Concrete.Hist N) : Fin (d + 1) :=
  ⟨min (q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card) d,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem history_critical_observables {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hbefore : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hpen : ∀ k ∈ p.position.board.left.rootLabel,
      k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length)
    (hn : p.position.board.left.NoLeafPending) :
    q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card =
        ⟨p.position.board.right.bodyLabels.length, p.position.board.right.leafIndex⟩ ∧
      q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
        (p.position.board.right.rootLabel.filter
          (fun i => i ≤ p.position.board.right.bodyLabels.length)).card ∧
      q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card =
        (p.position.board.right.currentLabel.filter
          (fun j => j ≤ p.position.board.right.leafIndex)).card ∧
      (criticalLastColor q = true ↔ p.position.board.right.NoLeafPending) := by
  obtain ⟨as, ha⟩ := History.word_run p false
  obtain ⟨bs, hb⟩ := History.word_run p true
  obtain ⟨cs, hcs, _⟩ := (History.reachable_word_extension hpath).2 false
  obtain ⟨ds, hds, _⟩ := (History.reachable_word_extension hpath).2 true
  change LabeledWord.LegalRun LabeledWord.initial as p.position.board.left at ha
  change LabeledWord.LegalRun LabeledWord.initial bs p.position.board.right at hb
  change LabeledWord.LegalRun p.position.board.left cs q.position.board.left at hcs
  change LabeledWord.LegalRun p.position.board.right ds q.position.board.right at hds
  have hleft := (hc.1.relaxed_penultimate_iff_suffix_card ha hcs hl).mpr ⟨hbefore, hpen, hn⟩
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  have hcount : (q.position.board.right.selectedLeafPairsFrom
      (p.position.board.right.bodyLabels.length - 1)
        (p.position.board.right.leafIndex - 1)).card =
      q.position.board.left.lastSelectedLabel.card := by omega
  exact ⟨hb.criticalPair_eq_of_suffix_card hds hr hcount,
    hb.critical_observables_of_suffix_card hds hr hcount⟩

#print axioms LabeledWord.LegalRun.criticalPair_eq_of_suffix_card
#print axioms history_critical_observables

end Payoff

end Erdos591.Positive.Game
