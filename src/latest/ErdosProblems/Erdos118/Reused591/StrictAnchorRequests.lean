import ErdosProblems.Erdos118.Reused591.RankedFirstLeafLabels
import ErdosProblems.Erdos118.Reused591.PrepareSelectionHistory
import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker
import ErdosProblems.Erdos118.Reused591.FutureBodyLocalization

namespace Erdos118.Reused591

/-!
# Read the T anchor label and obtain both U anchor requests

The T lower first leaf is saved at upper rank K+1, while the upper
play reads only its first T leaf. Its next U marker response is then
replayed in SU. T stays fixed during these moves, so the saved lower
T request and full source label remain intact. The new upper U size
is the already localized K, not a new size chosen after the labels.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_requests {N H J : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (oldT oldU upper : Concrete.Hist N)
    {B R D K i : ℕ} (T : RankedFirstLeafLabels J B R D (K + 1))
    (hwinT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hwinU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hwinUpper : (exactGame N blue).ArchitectWins J b σ upper)
    (hpT : oldT.position.pending = some ⟨true, .advance D⟩)
    (hpUpper : upper.position.pending = some ⟨false, .advance R⟩)
    (hmT : oldT.position.board.right.markerEvent = true)
    (hmUpper : upper.position.board.left.markerEvent = true)
    (hTshape : LabeledWord.SameStructure upper.position.board.left oldT.position.board.right)
    (hBT : max oldT.position.bound (b oldT) ≤ B)
    (hBUpper : max upper.position.bound (b upper) ≤ B)
    (hpU : oldU.position.pending = some ⟨true, .advance 0⟩)
    (hrelU : oldU.position.board.right.relaxed = true)
    (hnoU : oldU.position.board.right.NoLeafPending)
    (hbeforeU : LabeledWord.BeforeBody i oldU.position.board.right)
    (hnextU : ∀ m ∈ oldU.position.board.right.rootLabel,
      oldU.position.board.right.bodyLabels.length < m → i ≤ m)
    {anchor : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hUshape : LabeledWord.SameStructure oldU.position.board.right anchor)
    (hfrontU : LabeledWord.LegalRun anchor frontU upper.position.board.right)
    (hfrontPool : ∀ a ∈ frontU, a.2 ∈ H ∧ max oldU.position.bound (b oldU) < a.2)
    (hJfresh : ∀ x ∈ J, max oldU.position.bound (b oldU) < x)
    (hrelUpperU : upper.position.board.right.relaxed = true)
    (hnoUpperU : upper.position.board.right.NoLeafPending)
    (hbeforeUpperU : LabeledWord.BeforeBody i upper.position.board.right)
    (hnextUpperU : ∀ m ∈ upper.position.board.right.rootLabel,
      upper.position.board.right.bodyLabels.length < m → i ≤ m)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        (z.position.board.right.bodyLabels.getD (i - 1) ∅).card = K) :
    ∃ su tu c, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) oldU su ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper tu ∧
      su.position.pending = some ⟨true, .advance c⟩ ∧
      tu.position.pending = some ⟨true, .advance K⟩ ∧ 0 < c ∧
      LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
      su.position.board.right.markerEvent = true ∧ tu.position.board.right.markerEvent = true ∧
      su.position.board.right.bodyLabels.length + 1 = i ∧
      tu.position.board.right.bodyLabels.length + 1 = i ∧
      su.position.board.right.rootLabel = oldU.position.board.right.rootLabel ∧
      tu.position.board.right.rootLabel = upper.position.board.right.rootLabel ∧
      su.position.board.left = oldU.position.board.left ∧ tu.position.board.left.relaxed = true ∧
      ∃ P : PreparedSelection N J blue b σ tu.position.board.left,
        P.target = oldT ∧ P.side = true ∧ P.stem = upper.position.board.left ∧
          P.lowerLabel = T.source ∧ P.labels.pivot = T.targetView.pivot ∧
          P.labels.upper = T.targetView.upper := by
  obtain ⟨first, hUpperFirst, hFirstNone, hFirstRel, hFirstOther, P, hPtarget, hPside,
      _hPview, hPstem, hPlabel, hPpivot, hPupper⟩ :=
    prepare_selection (hJH.trans hHN) hJ blue
      (hwinT.mono (exactGame N blue) hJH (fun _ => le_rfl)) false true
      T.source T.source_card T.targetView T.pivot_source T.source_fresh
      hpUpper hpT hmUpper hmT hTshape hBUpper hBT
  have hFirstU : first.position.board.right = upper.position.board.right := hFirstOther
  have hFirstSep :=
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hUpperFirst).reply_separation hpUpper
  have hwinFirst := hwinUpper.of_reachable (exactGame N blue) (.single hUpperFirst)
  obtain ⟨v, hFirstV, hVboard, hpV⟩ := winning_next_body_after_fresh_leaf
    (hJH.trans hHN) hJ blue hwinFirst false hFirstRel hFirstSep
      (by simpa only [Bool.not_false, Board.get, hFirstU] using hrelUpperU)
      (by simpa only [Bool.not_false, Board.get, hFirstU] using hbeforeUpperU)
  have hUpperV := (Relation.ReflTransGen.single hUpperFirst).trans hFirstV
  have hVU : v.position.board.right = upper.position.board.right := by
    simpa only [hVboard] using hFirstU
  obtain ⟨su, tu, c, d, hOldSU, hVTU, hpSU, hpTU, hc, _hd, hshape, hmSU, hmTU,
      hiSU, hiTU, hrootSU, hrootTU, hOtherSU, hOtherTU⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue oldU v hwinU
      (hwinUpper.of_reachable (exactGame N blue) hUpperV) true true hpU hpV hUshape
      (by simpa only [Board.get, hVU] using hfrontU) hfrontPool hJfresh
      hrelU hnoU hbeforeU hnextU
      (by simpa only [Board.get, hVU] using hrelUpperU)
      (by simpa only [Board.get, hVU] using hnoUpperU)
      (by simpa only [Board.get, hVU] using hbeforeUpperU)
      (by simpa only [Board.get, hVU] using hnextUpperU)
  have hUpperTU := hUpperV.trans hVTU
  have hdK := localized_body_request_size (hJH.trans hHN) hJ blue upper tu true hwinUpper
    hfixed hUpperTU hpTU hmTU hiTU
  have hTUleft : tu.position.board.left = first.position.board.left := by
    simpa only [Board.get, Bool.not_true, hVboard] using hOtherTU
  have hTUroot : tu.position.board.right.rootLabel = upper.position.board.right.rootLabel := by
    simpa only [Board.get, hVU] using hrootTU
  refine ⟨su, tu, c, hOldSU, hUpperTU, hpSU, by simpa only [hdK] using hpTU, hc,
    hshape, hmSU, hmTU, hiSU, hiTU, hrootSU, hTUroot, hOtherSU, ?_, ?_⟩
  · simpa only [hTUleft, Board.get] using hFirstRel
  · rw [hTUleft]
    exact ⟨P, hPtarget, hPside, hPstem, hPlabel, hPpivot, hPupper⟩

#print axioms strict_anchor_requests

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
