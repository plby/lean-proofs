import ErdosProblems.Erdos118.Reused591.StrictMiddleSharedLeaf
import ErdosProblems.Erdos118.Reused591.DeferredBodyMarker
import ErdosProblems.Erdos118.Reused591.InsideNextLeafPrefixTriangle

namespace Erdos118.Reused591

/-!
# The strict finishing configuration with a next lower T leaf

S is at the common earlier leaf in both lower plays. Its old ST
response and the upper U next-marker response are pending. The
next lower T leaf is the last upper T leaf, while all future upper
U bodies lie beyond the lower U root. No bound for a future lower
completion is imposed on already recorded coordinates.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_strict_next_leaf_endgame {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (oldST su oldTU : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ oldST)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ oldTU)
    (hmSU : su.position.mode = some true) (hmTU : oldTU.position.mode = some true)
    (hpST : oldST.position.pending = some ⟨false, .advance 0⟩)
    (hpTU : oldTU.position.pending = some ⟨true, .advance 0⟩)
    (hSl : su.position.board.left.relaxed = true)
    (hUr : su.position.board.right.relaxed = true)
    (hsep : ∀ x ∈ su.position.board.left.coordinates,
      x ≤ su.position.board.right.coordinates.getLastD 0)
    (hS : LabeledWord.SameStructure oldST.position.board.left su.position.board.left)
    (hT : LabeledWord.SameStructure oldST.position.board.right oldTU.position.board.left)
    (hU : LabeledWord.SameStructure oldTU.position.board.right su.position.board.right)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldST.position.board.left)
    (hSstrict : oldST.position.board.left.leafIndex < gamma)
    (hSnext : ∀ j ∈ oldST.position.board.left.currentLabel,
      oldST.position.board.left.leafIndex < j → gamma ≤ j)
    (hSroot : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ su.position.board.left.currentLabel)
    (hSlast : ∀ j ∈ su.position.board.left.currentLabel, j ≤ gamma)
    {lastT : ℕ} (hTUp : LabeledWord.UpToLeaf lastT oldST.position.board.right)
    (hTstrict : oldST.position.board.right.leafIndex < lastT)
    (hTnext : ∀ j ∈ oldST.position.board.right.currentLabel,
      oldST.position.board.right.leafIndex < j → lastT ≤ j)
    (hUpperT : LabeledWord.UpToLeaf lastT oldTU.position.board.left)
    (hTroot : ∀ i ∈ oldTU.position.board.left.rootLabel,
      i ≤ oldTU.position.board.left.bodyLabels.length)
    (hTlast : ∀ j ∈ oldTU.position.board.left.currentLabel, j ≤ lastT)
    (hUpperUrel : oldTU.position.board.right.relaxed = true)
    (hUpperUno : oldTU.position.board.right.NoLeafPending) {nextU : ℕ}
    (hUpperBefore : LabeledWord.BeforeBody nextU oldTU.position.board.right)
    (hUpperNext : ∀ i ∈ oldTU.position.board.right.rootLabel,
      oldTU.position.board.right.bodyLabels.length < i → nextU ≤ i)
    (hLowerBefore : ∀ i ∈ su.position.board.right.rootLabel, i < nextU) :
    ¬ blue.CliqueFree 3 := by
  let B := max (max oldST.position.bound (b oldST)) (max oldTU.position.bound (b oldTU))
  obtain ⟨st, fine, hSTstep, hSUpath, _hnST, _hnSU, hSshape,
      hSTrel, hSUrel, hUrel, _hSTidx, _hSUidx, _hSTlabels, _hSUlabels,
      hTunchanged, hBothLast, hSTsep, _hSUfresh, hinputs⟩ :=
    strict_middle_shared_leaf hHN hH blue oldST su hwinSU hmSU hpST hSl hUr hsep hS
      hSUp hSstrict hSnext hSroot hgamma hSlast B (le_max_left _ _)
  have hwinSt := hwinST.of_reachable (exactGame N blue) (.single hSTstep)
  have hwinFine := hwinSU.of_reachable (exactGame N blue) hSUpath
  obtain ⟨pendingST, hstPath, hbST, hpT⟩ := winning_next_leaf_request_after_other hHN hH blue
    hwinSt true (by simpa only [Board.get, hTunchanged] using hTUp)
    (by simpa only [Board.get, hTunchanged] using hTstrict) hSTrel hSTsep
  have hwS := ((Position.history_dataInvariant fine).2.1 false).1
  have hwU := ((Position.history_dataInvariant fine).2.1 true).1
  have hstartS := LabeledWord.relaxed_ne_start hwS hSUrel
  have hstartU := LabeledWord.relaxed_ne_start hwU hUrel
  have hliveS := LabeledWord.relaxed_not_terminal hwS.2.1 hwS.2.2 hSUrel
  have hliveU := LabeledWord.relaxed_not_terminal hwU.2.1 hwU.2.2 hUrel
  obtain ⟨pendingSU, rSU, hsuPath, hbSU, hpU, hsU⟩ := request_smaller_at_boundary hHN hH blue
    hwinFine (follow_mode_some hSUpath hmSU) hliveU hstartS (hBothLast false)
  obtain ⟨front, hfront, hfrontPool⟩ := hinputs true
  have hUstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant su).2.1 true).1 hUr
  have hrootEq := hfront.rootLabel_eq hUstart
  have hcurrentRoot : fine.position.board.right.bodyLabels.length ∈
      su.position.board.right.rootLabel := hrootEq ▸ (of_decide_eq_true hUrel).2.1
  have hbefore : fine.position.board.right.bodyLabels.length < nextU :=
    hLowerBefore _ hcurrentRoot
  let C := max pendingSU.position.bound (b pendingSU)
  obtain ⟨upper, hTUstep, _hnTU, _hTUmarker, _hTUindex, hTUother,
      anchor, hanchor, tailU, htail, htailPool⟩ :=
    deferred_next_marker_from_body_prefix_or_empty hHN hH blue σ oldTU true hpTU
      hUpperUrel hUpperUno hUpperBefore hUpperNext hU hfront hbefore
      ((Position.history_dataInvariant fine).2.1 true).2
      (fun a ha => ⟨(hfrontPool a ha).1, (le_max_right _ _).trans_lt (hfrontPool a ha).2⟩) C
  have hTUleft : upper.position.board.left = oldTU.position.board.left := hTUother
  have hTshape' : LabeledWord.SameStructure pendingST.position.board.right
      upper.position.board.left := by
    simpa only [hbST, hTunchanged, hTUleft] using hT
  have hprefix : LabeledWord.SameStructure pendingSU.position.board.right anchor := by
    simpa only [hbSU, Board.get] using hanchor
  exact inside_next_leaf_prefix_triangle hHN hH blue pendingST pendingSU upper
    (hwinSt.of_reachable (exactGame N blue) hstPath)
    (hwinFine.of_reachable (exactGame N blue) hsuPath)
    (hwinTU.of_reachable (exactGame N blue) (.single hTUstep))
    (follow_mode_some (.single hTUstep) hmTU) hpT hpU hsU
    (by simpa only [hbSU, Board.get] using hstartS)
    (by simpa only [hbSU, Board.get] using hliveS)
    (by simpa only [hbSU, Board.get] using hBothLast false)
    (by simpa only [hbSU, Board.get] using hstartU)
    (by simpa only [hbSU, Board.get] using hBothLast true)
    (by simpa only [hbSU, hbST] using hSshape.symm) hTshape'
    (by simpa only [hbST, hTunchanged] using hTUp)
    (by simpa only [hbST, hTunchanged] using hTstrict)
    (by simpa only [hbST, hTunchanged] using hTnext)
    (by simpa only [hTUleft] using hUpperT)
    (by simpa only [hTUleft] using hTroot)
    (by simpa only [hTUleft] using hTlast) hprefix htail htailPool

#print axioms inside_strict_next_leaf_endgame

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
