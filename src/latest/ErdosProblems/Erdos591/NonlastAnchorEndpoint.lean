import ErdosProblems.Erdos591.PreliminaryRun
import ErdosProblems.Erdos591.PrepareSelectionHistory
import ErdosProblems.Erdos591.PreparedSelectionLastBody
import ErdosProblems.Erdos591.RankedFirstLeafLabels

/-!
# The nonlast anchor: exhaust the old U body before the saved T pivot

The same critical-checkpoint suffix count used by the preliminary
phases gives the exact rank here. The actual last-T-body request
installs its full label; the old lower first-leaf reply remains saved
at one rank beyond the current-body remainder of U.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_anchor_endpoint {N H J : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin checkpoint p oldT : Concrete.Hist N) {a B R D rem F : ℕ}
    (T : RankedFirstLeafLabels J B R D (rem + 1)) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin checkpoint)
    (hCheckpointP : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) checkpoint p)
    (hCheckpoint : CriticalCheckpoint checkpoint)
    (hwinOld : (exactGame N blue).ArchitectWins J b σ oldT)
    (hp : p.position.pending = some ⟨false, .advance R⟩)
    (hpOld : oldT.position.pending = some ⟨true, .advance D⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hmOld : oldT.position.board.right.markerEvent = true)
    (hshape : LabeledWord.SameStructure p.position.board.left oldT.position.board.right)
    (hBp : max p.position.bound (b p) ≤ B) (hBOld : max oldT.position.bound (b oldT) ≤ B)
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hother : p.position.board.right = checkpoint.position.board.right)
    (hUlt : checkpoint.position.board.right.leafIndex <
      checkpoint.position.board.right.currentLabel.sup id)
    (hrank : checkpoint.position.board.right.currentLabel.card -
      (checkpoint.position.board.right.currentLabel.filter
        (fun x => x ≤ checkpoint.position.board.right.leafIndex)).card = rem)
    (hfresh : ∀ x ∈ J, F < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.right.relaxed = true ∧ q.position.board.right.NoLeafPending ∧
      q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [T.source] ∧
      (∀ i ∈ q.position.board.left.rootLabel, i ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.left.currentLabel = T.source ∧
      q.position.board.right.rootLabel = p.position.board.right.rootLabel ∧
      q.position.board.right.bodyLabels = p.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card = rem ∧
      q.position.board.left.leafIndex < T.targetView.pivot ∧
      (∀ x ∈ q.position.board.left.currentLabel,
        q.position.board.left.leafIndex < x → T.targetView.pivot ≤ x) ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ P : PreparedSelection N J blue b σ q.position.board.left,
        P.target = oldT ∧ P.side = true ∧ P.stem = p.position.board.left ∧
        P.lowerLabel = T.source ∧ P.labels.pivot = T.targetView.pivot ∧
        P.labels.upper = T.targetView.upper ∧
      ∃ bs, LabeledWord.LegalRun p.position.board.right bs q.position.board.right ∧
        ∀ atom ∈ bs, atom.2 ∈ J ∧ F < atom.2 := by
  have hJN := hJH.trans hHN
  have pathH {v w : Concrete.Hist N}
      (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ h
  obtain ⟨first, hpFirst, _hFirstNone, hFirstRel, hFirstOther, P, hPtarget, hPside,
      _hPview, hPstem, hPsource, hPpivot, hPupper⟩ :=
    prepare_selection hJN hJ blue hwinOld false true T.source T.source_card T.targetView
      T.pivot_source T.source_fresh hp hpOld hm hmOld hshape hBp hBOld
  simp only [Board.get, Bool.not_false] at hFirstRel hFirstOther hPstem
  have hFirstU : first.position.board.right = checkpoint.position.board.right :=
    hFirstOther.trans hother
  have hFirstRoot : first.position.board.left.rootLabel = p.position.board.left.rootLabel := by
    simpa only [Board.get, hPstem] using P.rootLabel
  have hFirstBody : first.position.board.left.bodyLabels =
      p.position.board.left.bodyLabels ++ [T.source] := by
    have he := P.bodyLabels_eq
    rw [P.first_eq] at he
    have hparse : p.position.board.left.parser = .blocks (P.remainingBodies + 1) := by
      simpa only [hPstem] using P.stemParser
    simpa only [LabeledWord.record, Board.get, hPstem, hPsource, hparse] using he
  have hFirstLast : ∀ i ∈ first.position.board.left.rootLabel,
      i ≤ first.position.board.left.bodyLabels.length := by
    intro i hi
    simpa only [hFirstBody, List.length_append, List.length_singleton] using
      hroot i (hFirstRoot ▸ hi)
  obtain ⟨q, hFirstQ, hqn, hql, hqr, hqno, hqLabels, _hqMarker, hqCurrent,
      hqUlabels, hqUmarker, hqUindex, hqRank, hqBefore, hqNext, hqSep,
      as, bs, has, hbs, _hpoolT, hpoolU⟩ :=
    preliminary_run hHN hJH hJ blue origin checkpoint first T.source T.pivot_source
      T.pivot_rank ha hop hboard hmode hwin hfrom
      (hCheckpointP.trans (pathH (.single hpFirst))) hCheckpoint hFirstRel
      (by simpa only [hFirstU] using hCheckpoint.right_relaxed) hFirstLast
      (P.currentLabel.trans hPsource) (by rw [hFirstU])
      (by simpa only [hFirstU] using hUlt) hrank hfresh hall
  obtain ⟨PT, hPTtarget, hPTside, hPTstem, hPTsource, hPTpivot, hPTupper⟩ :=
    P.move_of_last_body false hFirstQ hFirstLast hql (by
      change q.position.board.left.leafIndex ≤ P.labels.pivot
      rw [hPpivot]
      exact hqBefore.le)
  have hTroot : q.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    (has.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant first).2.1 false).1 hFirstRel)).trans hFirstRoot
  have hUroot : q.position.board.right.rootLabel = p.position.board.right.rootLabel :=
    (hbs.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant first).2.1 true).1
        (by simpa only [hFirstU] using hCheckpoint.right_relaxed))).trans
      (congrArg LabeledWord.rootLabel hFirstOther)
  have hTlabels := hqLabels.trans hFirstBody
  refine ⟨q, (Relation.ReflTransGen.single hpFirst).trans hFirstQ, hqn, hql, hqr, hqno,
    hTroot, hTlabels, ?_, hqCurrent, hUroot, ?_, ?_, ?_, hqRank, hqBefore, ?_, hqSep,
    PT, hPTtarget.trans hPtarget, hPTside.trans hPside, hPTstem.trans hPstem,
    hPTsource.trans hPsource, hPTpivot.trans hPpivot, hPTupper.trans hPupper, bs, ?_, hpoolU⟩
  · intro i hi
    simpa only [hTlabels, List.length_append, List.length_singleton] using
      hroot i (hTroot ▸ hi)
  · simpa only [hother] using hqUlabels
  · simpa only [hFirstOther] using hqUmarker
  · simpa only [hFirstOther] using hqUindex
  · simpa only [hqCurrent] using hqNext
  · simpa only [hFirstOther] using hbs

#print axioms nonlast_anchor_endpoint

end Erdos591.Positive.Game.Payoff
