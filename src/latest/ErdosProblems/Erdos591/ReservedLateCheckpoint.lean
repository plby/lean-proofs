import ErdosProblems.Erdos591.LastLastUpper
import ErdosProblems.Erdos591.ManagedLastLeaf
import ErdosProblems.Erdos591.ManagedCriticalOpening
import ErdosProblems.Erdos591.LateMarkerCritical

/-!
# The inserted late-marker critical history on a fresh subpool

Managed moves use the fresh tail pool. The terminal marker and size
observations use the original pool, along the actual converted origin
path. No initial reserved response is falsely treated as a tail-pool
response. The managed upper origin stays on the tail pool throughout.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem reserved_late_checkpoint {N H J : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin fine upperOrigin : Concrete.Hist N) {B a : ℕ} (L : LastLastLabels H B a)
    (hwinOrigin : (exactGame N blue).ArchitectWins H b σ origin)
    (hwinFine : (exactGame N blue).ArchitectWins J b σ fine)
    (hfromFine : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hnone : fine.position.pending = none) (hrel : fine.position.board.left.relaxed = true)
    (hroot : fine.position.board.left.rootLabel = L.upper)
    (hbody : fine.position.board.left.bodyLabels.length = L.firstUpper)
    (hstrict : fine.position.board.left.leafIndex < fine.position.board.left.currentLabel.sup id)
    {other : LabeledWord}
    (hmanaged : ∃ M : Managed N J blue b σ true true other fine.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.rootLabel = L.upper ∧
      q.position.board.left.bodyLabels.length = L.upperPenultimate ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.NoLeafPending ∧
      q.position.board.right.relaxed = true ∧
      q.position.board.right.lastSelectedBody = q.position.board.right.bodyLabels.length ∧
      (∃ j ∈ q.position.board.right.currentLabel, q.position.board.right.leafIndex < j) ∧
      2 ≤ q.position.board.right.currentLabel.card ∧
      ∃ M : Managed N J blue b σ true true other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
  have hJN := hJH.trans hHN
  have pathH {p q : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpath
  have hstart := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant fine).2.1 false).1 hrel
  have hstop : ∃ p, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine p ∧
      p.position.pending = none ∧ p.position.board.left.relaxed = true ∧
      p.position.board.left.NoLeafPending ∧
      p.position.board.left.bodyLabels.length = L.upperPenultimate ∧
      (∀ y ∈ p.position.board.right.coordinates, y ≤ p.position.board.left.coordinates.getLastD 0) ∧
      ∃ M : Managed N J blue b σ true true other p.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upperOrigin M.target := by
    rcases lt_or_eq_of_le L.firstUpper_le_upperPenultimate with hlt | heq
    · exact managed_future_body_last_leaf_from hJN hJ blue hwinFine L.upperPenultimate false
        hstart ⟨hroot ▸ L.upperPenultimate_mem, by simpa [hbody, Board.get] using hlt⟩
        upperOrigin hmanaged
    · obtain ⟨p, hfp, hpn, hpr, hpno, hplabels, _hpm, hpsep, hMp⟩ :=
        managed_current_body_last_leaf_from hJN hJ blue hwinFine false hnone hrel
          (Or.inl hstrict) upperOrigin hmanaged
      have hlen := congrArg List.length hplabels
      exact ⟨p, hfp, hpn, hpr, hpno, hlen.trans (hbody.trans heq), hpsep, hMp⟩
  obtain ⟨p, hfp, _hpn, hpr, hpno, hpbody, hpsep, hMp⟩ := hstop
  have hwinp := hwinFine.of_reachable (exactGame N blue) hfp
  obtain ⟨as, has, _⟩ := follow_word_inputs hfp 0 (fun _ => Nat.zero_le _) false
  have hproot : p.position.board.left.rootLabel = L.upper := (has.rootLabel_eq hstart).trans hroot
  have hbefore : LabeledWord.BeforeBody L.pivot p.position.board.left :=
    ⟨hproot ▸ L.pivot_upper, by simpa [hpbody] using L.upperPenultimate_lt_pivot⟩
  obtain ⟨q, hpq, hpend, hleft, hqr, _hqsep, Mq, hMq⟩ :=
    managed_critical_opening hJN hJ blue hwinp hpr hpsep hbefore upperOrigin hMp
  have hfq := hfp.trans hpq
  have horiginQ := hfromFine.trans (pathH hfq)
  have hqroot : q.position.board.left.rootLabel = L.upper := by simpa [hleft] using hproot
  have hqbody : q.position.board.left.bodyLabels.length = L.upperPenultimate := by
    simpa [hleft] using hpbody
  have hqnext : ∀ k ∈ q.position.board.left.rootLabel,
      q.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.upper_bounds_penultimate k (hqroot ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hqbody] at hlt
      exact (not_lt_of_ge hle hlt).elim
  obtain ⟨hlastBody, hlater, hcard⟩ := winning_before_late_last_other_nonlast hHN hH blue origin
    (hwinOrigin.of_reachable (exactGame N blue) horiginQ) horiginQ hall hlarge hpend
    (by simpa [hleft] using hpr) (by simpa [hleft] using hpno)
    (by simpa [hleft] using hbefore) hqnext
    (fun k hk => (L.upper_bounds k (hqroot ▸ hk)).2) hqr
  exact ⟨q, hfq, hpend, hqroot, hqbody, by simpa [hleft] using hpr,
    by simpa [hleft] using hpno, hqr, hlastBody, hlater, hcard, Mq, hMq⟩

#print axioms reserved_late_checkpoint

end Erdos591.Positive.Game.Payoff
