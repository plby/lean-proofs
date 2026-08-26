import ErdosProblems.Erdos591.CriticalCheckpoint
import ErdosProblems.Erdos591.StrictCriticalData
import ErdosProblems.Erdos591.FiniteRank
import ErdosProblems.Erdos591.AlignedReverseEndpoint

/-!
# Stopping at the localized opposite leaf recovers the critical checkpoint

Equality of the two finite ranks identifies the exact canonical pair.
The suffix-count balance then recovers the first word's exhausted
penultimate body. No assumed correspondence between two plays is used.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact

theorem LabeledWord.LegalRun.criticalPair_eq_of_ranks
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)} {n : ℕ}
    (hinit : LabeledWord.LegalRun LabeledWord.initial xs v)
    (htail : LabeledWord.LegalRun v ys last) (hr : v.relaxed = true)
    (hspec : last.CriticalPairSpec n (last.criticalPair n))
    (hbodyRank : last.criticalBodyRank n =
      (v.rootLabel.filter (fun i => i ≤ v.bodyLabels.length)).card)
    (hleafRank : last.criticalLeafRank n =
      (v.currentLabel.filter (fun j => j ≤ v.leafIndex)).card) :
    last.criticalPair n = ⟨v.bodyLabels.length, v.leafIndex⟩ := by
  have hw := hinit.cursorInvariant LabeledWord.cursorInvariant_initial
  have hstart := LabeledWord.relaxed_ne_start hw hr
  have hsel := of_decide_eq_true hr
  have hroot := htail.rootLabel_eq hstart
  have hbody : (last.criticalPair n).1 = v.bodyLabels.length := by
    apply finite_rank_injective last.rootLabel (Finset.mem_sigma.mp hspec.1).1
      (hroot ▸ hsel.2.1)
    simpa only [LabeledWord.criticalBodyRank, hroot] using hbodyRank
  have hpos := (hw.2.2.1 _ hsel.2.1).1
  have hlabel : last.bodyLabels.getD ((last.criticalPair n).1 - 1) ∅ = v.currentLabel := by
    rw [hbody, htail.body_getD_eq hstart (by omega)]
    exact (LabeledWord.currentLabel_eq_getD (by omega)).symm
  have hleaf : (last.criticalPair n).2 = v.leafIndex := by
    apply finite_rank_injective v.currentLabel
      (hlabel ▸ (Finset.mem_sigma.mp hspec.1).2) hsel.2.2
    simpa only [LabeledWord.criticalLeafRank, hlabel] using hleafRank
  exact Sigma.ext hbody (heq_of_eq hleaf)

namespace Payoff

theorem history_critical_reverse_endpoint {N : Set ℕ} {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hspec : q.position.board.right.CriticalPairSpec q.position.board.left.lastSelectedLabel.card
      (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card))
    (hbodyRank : q.position.board.right.criticalBodyRank
      q.position.board.left.lastSelectedLabel.card =
      (p.position.board.right.rootLabel.filter
        (fun i => i ≤ p.position.board.right.bodyLabels.length)).card)
    (hleafRank : q.position.board.right.criticalLeafRank
      q.position.board.left.lastSelectedLabel.card =
      (p.position.board.right.currentLabel.filter
        (fun j => j ≤ p.position.board.right.leafIndex)).card) : CriticalCheckpoint p := by
  obtain ⟨as, ha⟩ := History.word_run p false
  obtain ⟨bs, hb⟩ := History.word_run p true
  obtain ⟨cs, hcs, _⟩ := (History.reachable_word_extension hpath).2 false
  obtain ⟨ds, hds, _⟩ := (History.reachable_word_extension hpath).2 true
  change LabeledWord.LegalRun LabeledWord.initial as p.position.board.left at ha
  change LabeledWord.LegalRun LabeledWord.initial bs p.position.board.right at hb
  change LabeledWord.LegalRun p.position.board.left cs q.position.board.left at hcs
  change LabeledWord.LegalRun p.position.board.right ds q.position.board.right at hds
  have heq := hb.criticalPair_eq_of_ranks hds hr hspec hbodyRank hleafRank
  have hright := hspec.2.2.2
  rw [heq] at hright
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  have hleft : (q.position.board.left.selectedLeafPairsFrom
      (p.position.board.left.bodyLabels.length - 1) (p.position.board.left.leafIndex - 1)).card =
      q.position.board.left.lastSelectedLabel.card + 1 :=
    hbalance.trans (congrArg (fun n : ℕ => n + 1) hright)
  obtain ⟨hbefore, hpen, hno⟩ := (hc.1.relaxed_penultimate_iff_suffix_card ha hcs hl).mp hleft
  exact ⟨hl, hr, horder, hbefore, hpen, hno⟩

theorem winning_strict_reverse_endpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.left.beforeLastLeafCount < q.position.board.right.beforeLastLeafCount)
    (hfixed : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q →
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
  have hwinP := hwin.of_reachable (exactGame N blue) hfrom
  obtain ⟨hl, horder⟩ := winning_left_relaxed_of_right_separation hHN hH blue hwinP hr hpos hsep
  obtain ⟨q, hpq, hq⟩ := hwinP.exists_terminal (exactGame N blue) hHN hH
  have hfull := hfrom.trans hpq
  obtain ⟨s, t, hc, hmax, hfirst, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hfull hq
  have hspec := (hc.strict_critical_data hfirst hmax (by simpa only [hcard] using ha)
    (hall q true hfull hq)).2.1
  have hvalues := hfixed q true hpq hq
  exact history_critical_reverse_endpoint (follow_history_path hpq) hc hmax hl hr horder hspec
    hvalues.1 hvalues.2

#print axioms LabeledWord.LegalRun.criticalPair_eq_of_ranks
#print axioms history_critical_reverse_endpoint
#print axioms winning_strict_reverse_endpoint

end Payoff

end Erdos591.Positive.Game
