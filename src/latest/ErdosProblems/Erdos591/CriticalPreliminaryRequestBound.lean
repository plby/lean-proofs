import ErdosProblems.Erdos591.CriticalRemainderBound
import ErdosProblems.Erdos591.CriticalCheckpoint
import ErdosProblems.Erdos591.ReachableBodyCard

/-!
# The actual last-S-body request fits its preliminary critical-body phase

Extend the actual marker request conservatively on its future pool.
The earlier critical checkpoint identifies the terminal critical pair.
Its current full label persists, and the issued S-body cardinality is
the terminal critical suffix size. No future label size is assumed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem critical_preliminary_request_bound {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p : Concrete.Hist N) {a R : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hcp : CriticalCheckpoint old)
    (hp : p.position.pending = some ⟨false, .advance R⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    old.position.board.right.currentLabel.card -
        (old.position.board.right.currentLabel.filter
          (fun x => x ≤ old.position.board.right.leafIndex)).card + 2 ≤ R := by
  obtain ⟨z, w, hpz, hz⟩ := (exactGame N blue).terminal_reachable_of_infinite
    (hKH.trans hHN) hK b σ p
  have hpzH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpz
  have holdz := holdp.trans hpzH
  have hfull := hfrom.trans holdz
  obtain ⟨s, t, hc, hmax, hfirst, hcardRoot⟩ :=
    terminal_inside_clear_data blue origin z (by omega) hop hboard hmode hwin hfull hz
  obtain ⟨_hsize, hspec, hbefore, _hpos, _hless, _hlast⟩ := hc.strict_critical_data
    hfirst hmax (by simpa only [hcardRoot] using ha) (hall z w hfull hz)
  have hpair := (history_critical_observables (follow_history_path holdz) hc hmax
    hcp.left_relaxed hcp.right_relaxed hcp.coordinate_order hcp.left_before
      hcp.left_penultimate hcp.left_exhausted).1
  have hlastRoot : z.position.board.right.lastSelectedBody ∈ z.position.board.right.rootLabel := by
    have hne : z.position.board.right.rootLabel.Nonempty :=
      ⟨_, (Finset.mem_sigma.mp hspec.1).1⟩
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hbound := hspec.current_remainder_add_two_le hlastRoot hbefore
    (Finset.card_pos.mp (hc.2.1.selected_body_card_pos hlastRoot))
  obtain ⟨as, hrun, _⟩ := (History.reachable_word_extension (follow_history_path holdz)).2 true
  change LabeledWord.LegalRun old.position.board.right as z.position.board.right at hrun
  have hstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 true).1 hcp.right_relaxed
  change old.position.board.right.parser ≠ .start at hstart
  have hbodypos : 0 < old.position.board.right.bodyLabels.length :=
    (((Position.history_dataInvariant old).2.1 true).1.2.2.1 _
      (of_decide_eq_true hcp.right_relaxed).2.1).1
  have hlabel : z.position.board.right.bodyLabels.getD
      (old.position.board.right.bodyLabels.length - 1) ∅ =
        old.position.board.right.currentLabel := by
    rw [hrun.body_getD_eq hstart (by omega)]
    exact (LabeledWord.currentLabel_eq_getD (by omega)).symm
  have hcard := reachable_last_body_label_card blue p z false hp hm hrootLast hpz hz
  change z.position.board.left.lastSelectedLabel.card = R at hcard
  rw [hpair, hlabel] at hbound
  simpa only [hcard] using hbound

#print axioms critical_preliminary_request_bound

end Erdos591.Positive.Game.Payoff
