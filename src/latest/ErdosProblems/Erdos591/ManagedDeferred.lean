import ErdosProblems.Erdos591.ManagedWord
import ErdosProblems.Erdos591.DeferredBody
import ErdosProblems.Erdos591.SelectedBodyCard

/-!
# Deferred firing with the managed upper origin retained

At a selected leaf in the last lower selected body, the managed record
cannot still be a root plan. Fire its prepared body at a nonlast leaf,
retaining the actual upper origin, mode, opposite word and freshness.
The upper label is either singleton or has the lower last index second.
-/

namespace Erdos591.Positive.Game.Relay.Managed

open Erdos591.Negative.Exact
open Payoff

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {t mode : Bool} {other w : LabeledWord}

theorem first_request_of_last_body (M : Managed N H blue b σ t mode other w)
    (hlastBody : w.lastSelectedBody = w.bodyLabels.length) :
    ∃ d, M.target.position.pending = some ⟨t, .advance d⟩ ∧ 0 < d ∧
      (M.target.position.board.get t).markerEvent = true ∧
      (M.target.position.board.get t).NoRootPassed := by
  cases M with
  | root R _ _ _ =>
      have he : w.lastSelectedBody = R.labels.pivot := by
        rw [LabeledWord.lastSelectedBody, R.rootLabel, R.labels.lower_sup]
      have hb := R.before
      omega
  | prepared P hside _ _ hfirst =>
      have hc : 0 < P.upperSize :=
        P.labels.upper_card ▸ Finset.card_pos.mpr ⟨P.labels.pivot, P.labels.pivot_upper⟩
      exact ⟨P.upperSize, by simpa only [target, hside] using P.targetPending, hc,
        by simpa only [target, hside] using P.targetMarker,
        by simpa only [target, hside] using hfirst⟩

theorem fire_deferred_from (M : Managed N H blue b σ t mode other w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hrel : w.relaxed = true)
    (hlastBody : w.lastSelectedBody = w.bodyLabels.length)
    (hlater : ∃ j ∈ w.currentLabel, w.leafIndex < j)
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q : Concrete.Hist N,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ q.position.pending = none ∧
      (q.position.board.get t).coordinates = w.coordinates ∧
      (q.position.board.get t).relaxed = true ∧
      (q.position.board.get t).leafIndex = w.leafIndex ∧
      q.position.board.get (!t) = other ∧ q.position.mode = some mode ∧
      (∀ y ∈ (q.position.board.get (!t)).coordinates,
        y ≤ (q.position.board.get t).coordinates.getLastD 0) ∧
      ((q.position.board.get t).currentLabel.card = 1 →
        (q.position.board.get t).currentLabel = {w.leafIndex}) ∧
      (2 ≤ (q.position.board.get t).currentLabel.card →
        w.currentLabel.sup id ∈ (q.position.board.get t).currentLabel ∧
        ∀ j ∈ (q.position.board.get t).currentLabel,
          w.leafIndex < j → w.currentLabel.sup id ≤ j) ∧
      (q.position.board.get t).currentLabel.card =
        (M.target.position.pending.map Request.size).getD 0 ∧
      (∀ i ∈ (q.position.board.get t).rootLabel,
        (q.position.board.get t).bodyLabels.length ≤ i) := by
  cases M with
  | root R _ _ _ =>
      have he : w.lastSelectedBody = R.labels.pivot := by
        rw [LabeledWord.lastSelectedBody, R.rootLabel, R.labels.lower_sup]
      have hb := R.before
      omega
  | prepared P hside hother hmode hfirst =>
      obtain ⟨j, hj, hjlt⟩ := hlater
      have hjlower : j ∈ P.labels.lower := P.currentLabel ▸ hj
      have hbefore : w.leafIndex < P.labels.pivot := hjlt.trans_le (P.labels.lower_le j hjlower)
      obtain ⟨q, hs, hn, hcoords, hr, hidx, hlabel, _hmarker, ho, hroot, hcount⟩ :=
        P.fire_deferred hHN hinc hrel hbefore
      have hlabelT : (q.position.board.get t).currentLabel =
          P.labels.deferredUpper w.leafIndex := by simpa [← hside] using hlabel
      have hcard : (q.position.board.get t).currentLabel.card = P.upperSize := by
        rw [hlabelT]
        exact P.labels.deferredUpper_card hbefore
      have hsup : w.currentLabel.sup id = P.labels.pivot := by
        rw [P.currentLabel, P.labels.lower_sup]
      refine ⟨q, hfrom.tail hs, P.targetWinning.of_reachable (exactGame N blue)
        (Relation.ReflTransGen.single hs), hn, by simpa [← hside] using hcoords,
        by simpa [← hside] using hr, by simpa [← hside] using hidx,
        by simpa [← hside] using ho.trans hother,
        follow_mode_some (Relation.ReflTransGen.single hs) hmode, ?_, ?_, ?_, ?_, ?_⟩
      · have hsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation
          P.targetPending
        simpa [← hside] using hsep
      · intro hc
        rw [hlabelT]
        exact P.labels.deferredUpper_singleton (hcard.symm.trans hc) _
      · intro hc
        rw [hlabelT, hsup]
        exact P.labels.deferredUpper_second (hcard ▸ hc) hbefore
      · simpa [target, P.targetPending, Request.size] using hcard
      · intro i hi
        have hi' : i ∈ (P.target.position.board.get P.side).rootLabel := by
          rw [← hroot]
          simpa [hside] using hi
        have hlt := hfirst i hi'
        simpa [← hside, hcount] using hlt

#print axioms first_request_of_last_body
#print axioms fire_deferred_from

end Erdos591.Positive.Game.Relay.Managed
