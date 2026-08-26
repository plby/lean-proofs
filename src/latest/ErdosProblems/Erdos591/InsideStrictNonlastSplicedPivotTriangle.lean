import ErdosProblems.Erdos591.ReservedNonlastSplicedCheckpoint
import ErdosProblems.Erdos591.NonlastSplicedCheckpointTriangle

/-! # The higher-rank nonlast case from the actual saved upper U-root request -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_nonlast_spliced_pivot_triangle {N H M HT HD : Set ℕ}
    (hHN : H ⊆ N) (hMH : M ⊆ H) (hM : M.Infinite)
    (blue : SimpleGraph G) (htri : blue.CliqueFree 3) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    (origin old upperOrigin : Concrete.Hist N) {B a g k BT eT jT BD d c s : ℕ}
    (S : LastLastLabels H B a) (T : CriticalRootLabels HT BT eT a jT)
    (D : CriticalLeafLabels HD BD d c s) (ha : 2 ≤ a) (hk : 2 ≤ k) (hkg : k < g)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hB : max origin.position.bound (b origin) ≤ B)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromUpper : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin upperOrigin)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩) (hOld : CriticalCheckpoint old)
    (hOldRoot : old.position.board.left.rootLabel = S.lower)
    (hOldBody : old.position.board.left.bodyLabels.length = S.penultimate)
    (hTroot : old.position.board.right.rootLabel = T.lower)
    (hTbody : old.position.board.right.bodyLabels.length = T.shared)
    (hTlabel : old.position.board.right.currentLabel = D.lower)
    (hTindex : old.position.board.right.leafIndex = D.upperView.pivot)
    (hTshape : LabeledWord.SameStructure old.position.board.right upperOrigin.position.board.left)
    (hUpperRel : upperOrigin.position.board.left.relaxed = true)
    (hUpperRoot : upperOrigin.position.board.left.rootLabel = T.upper)
    (hUpperLabel : upperOrigin.position.board.left.currentLabel = D.upperView.upper)
    (hUpperIndex : upperOrigin.position.board.left.leafIndex = D.upperView.pivot)
    (hpUpper : upperOrigin.position.pending = some ⟨true, .advance g⟩)
    (hUpperInit : upperOrigin.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hfixedUpper : ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ M b) upperOrigin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor S.lower S.marker).runAtoms as = some old.position.board.left)
    (hinc : (S.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨K, hKM, _hK, C, e, j, U, _hj, _hje, L, hLK, hL, hLfresh,
      BE, dE, cE, sE, E, hcE, _hsE, _hsdE, fine, tu, hfromFine, hfromTU,
      _hUpperTU, _hwinFine, hpFine, hFine, hFineRoot, hFineBody, hFineUroot,
      hFineUbody, hFineUlabel, hFineUindex, _hnTU, hTUleft, hUshape, hTUrel,
      hTUroot, hTUbody, hTUlabel, _hTUindex, _hTUmode, hTUsep, hfixed,
      front, hfront, hfrontPool⟩ := reserved_nonlast_spliced_checkpoint hHN hMH hM blue htri
        hroot origin old upperOrigin S ha hk hkg hwin hop hboard hmode hB hfromUpper hOldBody
        hpUpper hUpperInit hall hlast hfixedUpper hraw hinc hpool
  exact nonlast_spliced_checkpoint_triangle hHN ((hLK.trans hKM).trans hMH) hL blue
    origin old fine tu S T U D E ha hcE hkg hop hboard hmode hwin hfromOld hfromFine hfromTU
    hOld hFine hpOld hpFine hOldRoot hOldBody hFineRoot hFineBody
    hTlabel hTindex hTroot hTbody (by simpa only [hTUleft] using hTshape.symm)
    (by simpa only [hTUleft] using hUpperRel) (by simpa only [hTUleft] using hUpperLabel)
    (by simpa only [hTUleft] using hUpperIndex) (by simpa only [hTUleft] using hUpperRoot)
    hUshape hTUrel hTUroot hTUbody hTUlabel hFineUroot hFineUbody hFineUlabel hFineUindex
    hTUsep hfixed hall hlast hfront hfrontPool hLfresh

#print axioms inside_strict_nonlast_spliced_pivot_triangle

end Erdos591.Positive.Game.Payoff
