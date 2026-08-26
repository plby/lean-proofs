import ErdosProblems.Erdos591.AlignedCriticalPreparation
import ErdosProblems.Erdos591.NextMarkerReplayHistory

/-!
# Submit the aligned upper first leaf and leave the lower last-body reply pending

Both histories follow the original strategy. The lower first word's
next-marker response remains unsubmitted while the shared second-word
prefix is fired as the upper first selected leaf.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem aligned_critical_opening_on_subset {N H J : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    (R : AlignedRootPlan N J blue b σ p.position.board.right)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) :
    ∃ old upper, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p old ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
      old.position.pending = some ⟨false, .advance 0⟩ ∧
      old.position.board.left.relaxed = true ∧
      old.position.board.left.bodyLabels.length < old.position.board.left.lastSelectedBody ∧
      (∀ k ∈ old.position.board.left.rootLabel,
        k < old.position.board.left.lastSelectedBody →
          k ≤ old.position.board.left.bodyLabels.length) ∧
      old.position.board.left.NoLeafPending ∧ old.position.board.right.relaxed = true ∧
      old.position.board.right.rootLabel = R.labels.lower ∧
      old.position.board.right.bodyLabels.length = R.labels.shared ∧
      old.position.board.right.NoLeafPending ∧ upper.position.pending = none ∧
      LabeledWord.SameStructure old.position.board.right (upper.position.board.get R.side) ∧
      (upper.position.board.get R.side).relaxed = true ∧
      (upper.position.board.get R.side).rootLabel = R.labels.upper ∧
      (upper.position.board.get R.side).bodyLabels.length = R.labels.shared ∧
      (∀ k ∈ (upper.position.board.get R.side).rootLabel,
        (upper.position.board.get R.side).bodyLabels.length ≤ k) ∧
      upper.position.board.get (!R.side) = R.target.position.board.get (!R.side) ∧
      upper.position.mode = some true ∧
      (∀ x ∈ (upper.position.board.get (!R.side)).coordinates,
        x ≤ (upper.position.board.get R.side).coordinates.getLastD 0) := by
  have pathH {u v : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hp
  obtain ⟨q, hpq, _hqn, hql, hqbefore, hqpen, hqno, hqr, hqroot, hqbody, hqnoT, hqsep,
      P, hPs, hPpath, hPupper, _hPfirst, hPother, hPlast⟩ :=
    aligned_critical_prepared_on_subset hHN hH hJH hJ blue origin p R ha hop hboard hmode
      hwin hfrom hpos hall
  have hlastmem : q.position.board.left.lastSelectedBody ∈ q.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨q.position.board.left.bodyLabels.length, (of_decide_eq_true hql).2.1⟩
  have hbefore : LabeledWord.BeforeBody q.position.board.left.lastSelectedBody
      q.position.board.left := ⟨hlastmem, hqbefore⟩
  have hlive := hbefore.not_terminal ((Position.history_dataInvariant q).2.1 false).1
  obtain ⟨old, r, hqold, hOldBoard, hpOld⟩ :=
    request_on_live_board (H := J) σ q (Board.not_done_of_live (side := false) hlive)
  have hpold := hpq.trans hqold
  have hwinOld := (hwin.of_reachable (exactGame N blue) (hfrom.trans (pathH hpold))).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  have hside : r.side = false := winning_pending_switch (hJH.trans hHN) hJ blue hwinOld hpOld true
    (by simpa only [hOldBoard, Board.get] using hqr)
    (by simpa only [hOldBoard, Board.get, Bool.not_true] using hqsep)
  have hzero := winning_pending_root_advance_zero (hJH.trans hHN) hJ blue hwinOld hpOld false hside
    (by simpa only [hOldBoard, Board.get] using hql)
    (by simpa only [hOldBoard, Board.get] using hbefore)
  have hpend : old.position.pending = some ⟨false, .advance 0⟩ := by
    simpa only [hzero] using hpOld
  obtain ⟨upper, huStep, huNone, huCoords, huRel, huOther, huRoot, _huBody, _huLeaf⟩ :=
    P.fire_full (hJH.trans hHN) ((Position.history_dataInvariant q).2.1 true).2 hPlast
  have huSep := (FiniteResponseGame.FollowStep.next (exactGame N blue) huStep).reply_separation
    P.targetPending
  have huPath := hRfrom.trans (pathH (hPpath.tail huStep))
  have hcoords : (upper.position.board.get R.side).coordinates =
      q.position.board.right.coordinates := by simpa only [hPs] using huCoords
  have hshape : LabeledWord.SameStructure old.position.board.right
      (upper.position.board.get R.side) := by
    obtain ⟨as, has⟩ := History.word_run old true
    obtain ⟨bs, hbs⟩ := History.word_run upper R.side
    apply LabeledWord.sameStructure_of_initial_runs has.run hbs.run
    simpa only [hOldBoard, Board.get] using hcoords.symm
  have hupperRoot : (upper.position.board.get R.side).rootLabel = R.labels.upper := by
    simpa only [hPs] using huRoot.trans hPupper
  have hupperBody : (upper.position.board.get R.side).bodyLabels.length = R.labels.shared := by
    rw [← hshape.body_length, hOldBoard]
    exact hqbody
  refine ⟨old, upper, hpold, huPath, hpend, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, huNone,
    hshape, by simpa only [hPs] using huRel, hupperRoot, hupperBody, ?_, ?_,
    follow_mode_some huPath hmode, by simpa only [hPs] using huSep⟩
  · simpa only [hOldBoard] using hql
  · simpa only [hOldBoard] using hqbefore
  · simpa only [hOldBoard] using hqpen
  · simpa only [hOldBoard] using hqno
  · simpa only [hOldBoard] using hqr
  · simpa only [hOldBoard] using hqroot
  · simpa only [hOldBoard] using hqbody
  · simpa only [hOldBoard] using hqnoT
  · intro k hk
    rw [hupperBody]
    exact (R.labels.upper_bounds k (hupperRoot ▸ hk)).1
  · simpa only [hPs] using huOther.trans hPother

theorem aligned_critical_opening {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    (R : AlignedRootPlan N H blue b σ p.position.board.right)
    {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hRfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin R.target)
    (hpos : 0 < p.position.board.left.coordinates.length)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true) :
    ∃ old upper, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p old ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper ∧
      old.position.pending = some ⟨false, .advance 0⟩ ∧
      old.position.board.left.relaxed = true ∧
      old.position.board.left.bodyLabels.length < old.position.board.left.lastSelectedBody ∧
      (∀ k ∈ old.position.board.left.rootLabel,
        k < old.position.board.left.lastSelectedBody →
          k ≤ old.position.board.left.bodyLabels.length) ∧
      old.position.board.left.NoLeafPending ∧ old.position.board.right.relaxed = true ∧
      old.position.board.right.rootLabel = R.labels.lower ∧
      old.position.board.right.bodyLabels.length = R.labels.shared ∧
      old.position.board.right.NoLeafPending ∧ upper.position.pending = none ∧
      LabeledWord.SameStructure old.position.board.right (upper.position.board.get R.side) ∧
      (upper.position.board.get R.side).relaxed = true ∧
      (upper.position.board.get R.side).rootLabel = R.labels.upper ∧
      (upper.position.board.get R.side).bodyLabels.length = R.labels.shared ∧
      (∀ k ∈ (upper.position.board.get R.side).rootLabel,
        (upper.position.board.get R.side).bodyLabels.length ≤ k) ∧
      upper.position.board.get (!R.side) = R.target.position.board.get (!R.side) ∧
      upper.position.mode = some true ∧
      (∀ x ∈ (upper.position.board.get (!R.side)).coordinates,
        x ≤ (upper.position.board.get R.side).coordinates.getLastD 0) :=
  aligned_critical_opening_on_subset hHN hH (Set.Subset.refl H) hH blue origin p R ha hop
    hboard hmode hwin hfrom hRfrom hpos hall

#print axioms aligned_critical_opening_on_subset
#print axioms aligned_critical_opening

end Erdos591.Positive.Game.Payoff
