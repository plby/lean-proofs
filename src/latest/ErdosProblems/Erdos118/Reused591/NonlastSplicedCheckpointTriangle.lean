import ErdosProblems.Erdos118.Reused591.CommonPreliminaryMarkerLabels
import ErdosProblems.Erdos118.Reused591.NonlastSplicedPreliminaryTriangle

namespace Erdos118.Reused591

/-! # Both actual critical checkpoints through the higher-rank nonlast triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem nonlast_spliced_checkpoint_triangle {N H J HT HU HD HE : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old fine upper : Concrete.Hist N)
    {a B BT eT dT jT BU e g j k BD nD cD sD BE nE cE sE : ℕ}
    (S : LastLastLabels H B a)
    (T : CriticalRootLabels HT BT eT dT jT) (U : SplicedRootLabels HU BU e g j k)
    (D : CriticalLeafLabels HD BD nD cD sD) (E : RankedFirstLeafLabels HE BE nE cE sE)
    (ha : 2 ≤ a) (hcE : 0 < cE) (hkg : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromFine : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upper)
    (hOld : CriticalCheckpoint old) (hFine : CriticalCheckpoint fine)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance 0⟩)
    (hOldSroot : old.position.board.left.rootLabel = S.lower)
    (hOldSbody : old.position.board.left.bodyLabels.length = S.penultimate)
    (hFineSroot : fine.position.board.left.rootLabel = S.upper)
    (hFineSbody : fine.position.board.left.bodyLabels.length = S.upperPenultimate)
    (hOldLabel : old.position.board.right.currentLabel = D.lower)
    (hOldIndex : old.position.board.right.leafIndex = D.upperView.pivot)
    (hOldRoot : old.position.board.right.rootLabel = T.lower)
    (hOldBody : old.position.board.right.bodyLabels.length = T.shared)
    (hTshape : LabeledWord.SameStructure upper.position.board.left old.position.board.right)
    (hTrel : upper.position.board.left.relaxed = true)
    (hTlabel : upper.position.board.left.currentLabel = D.upperView.upper)
    (hTindex : upper.position.board.left.leafIndex = D.upperView.pivot)
    (hTroot : upper.position.board.left.rootLabel = T.upper)
    (hUshape : LabeledWord.SameStructure fine.position.board.right upper.position.board.right)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUroot : upper.position.board.right.rootLabel = U.upper)
    (hUbody : upper.position.board.right.bodyLabels.length = U.first)
    (hUlabel : upper.position.board.right.currentLabel = E.targetView.upper)
    (hFineUroot : fine.position.board.right.rootLabel = U.lower)
    (hFineUbody : fine.position.board.right.bodyLabels.length = U.first)
    (hFineUlabel : fine.position.board.right.currentLabel = E.source)
    (hFineUindex : fine.position.board.right.leafIndex = E.targetView.pivot)
    (hUsep : ∀ x ∈ upper.position.board.left.coordinates,
      x ≤ upper.position.board.right.coordinates.getLastD 0)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    {front : List (Finset ℕ × ℕ)}
    (hfront : LabeledWord.LegalRun (LabeledWord.rootRelabel S.upper old.position.board.left)
      front fine.position.board.left)
    (hfrontPool : ∀ atom ∈ front, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x) :
    ¬ blue.CliqueFree 3 := by
  let r := old.position.board.right.currentLabel.card -
    (old.position.board.right.currentLabel.filter
      (fun x => x ≤ old.position.board.right.leafIndex)).card
  let t := fine.position.board.right.currentLabel.card -
    (fine.position.board.right.currentLabel.filter
      (fun x => x ≤ fine.position.board.right.leafIndex)).card
  obtain ⟨p, q, P, Q, C, L, _hP, _hQ, hOldP, hFineQ, _hfromP, _hfromQ,
      _hwinP, _hwinQ, hp, hq, hstem, hmP, hmQ, _hiP, _hiQ, _hrootP, _hrootQ,
      hLastP, hLastQ, hOtherP, hOtherQ, hBP, hBQ⟩ :=
    common_preliminary_marker_labels (r := r) (t := t) hHN hJH hJ blue origin old fine S ha
      hop hboard hmode hwin hfromOld hfromFine hOld hFine hpOld hpFine hOldSroot hOldSbody
      hFineSroot hFineSbody le_rfl le_rfl hall hfront hfrontPool hJfresh
  have hFineQH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hFineQ
  exact nonlast_spliced_preliminary_triangle hHN hJH hJ blue origin old fine p q upper L T U D E
    ha hcE hkg hop hboard hmode hwin hfromOld hfromFine hOldP hFineQH hfromUpper hOld hFine
    hp hq hstem hmP hmQ hLastP hLastQ hOtherP hOtherQ hBP hBQ hOldLabel hOldIndex
    hOldRoot hOldBody hFineUlabel hFineUindex hFineUroot hFineUbody rfl rfl
    hTshape hTrel hTlabel hTindex hTroot hUshape.symm hUrel hUroot hUbody hUlabel
    hUsep hfixed hall hlast

#print axioms nonlast_spliced_checkpoint_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
