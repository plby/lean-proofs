import ErdosProblems.Erdos118.Reused591.StrictAnchorRequests
import ErdosProblems.Erdos118.Reused591.StrictAnchorLeafTriangle

namespace Erdos118.Reused591

/-!
# The localized strict anchor requests yield a triangle

Choose the rank-K+1 T label after its two actual sizes and the fixed
future U size are known. Replay the U marker, choose both U labels
after their actual requests, and apply the checked anchor-leaf triangle.
Old lower paths keep their ambient pool; later replies use the smaller
infinite pool on which the terminal profile and size are fixed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_requests_triangle {N H J HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (oldT oldU upper : Concrete.Hist N)
    {R D K BU e g j k : ℕ} (U : SplicedRootLabels HU BU e g j (k + 1))
    (hD : 0 < D) (hK : 0 < K) (hKR : K + 2 ≤ R) (hAfter : k + 1 < g)
    (hwinT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hwinU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hwinUpper : (exactGame N blue).ArchitectWins J b σ upper)
    (hpT : oldT.position.pending = some ⟨true, .advance D⟩)
    (hpUpper : upper.position.pending = some ⟨false, .advance R⟩)
    (hmT : oldT.position.board.right.markerEvent = true)
    (hmUpper : upper.position.board.left.markerEvent = true)
    (hTshape : LabeledWord.SameStructure upper.position.board.left oldT.position.board.right)
    (hTlast : ∀ i ∈ upper.position.board.left.rootLabel,
      i ≤ upper.position.board.left.bodyLabels.length + 1)
    (hpU : oldU.position.pending = some ⟨true, .advance 0⟩)
    (hrelU : oldU.position.board.right.relaxed = true)
    (hnoU : oldU.position.board.right.NoLeafPending)
    (hbeforeU : LabeledWord.BeforeBody U.anchor oldU.position.board.right)
    (hnextU : ∀ i ∈ oldU.position.board.right.rootLabel,
      oldU.position.board.right.bodyLabels.length < i → U.anchor ≤ i)
    (hLowerRoot : oldU.position.board.right.rootLabel = U.lower)
    {anchor : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hUshape : LabeledWord.SameStructure oldU.position.board.right anchor)
    (hfrontU : LabeledWord.LegalRun anchor frontU upper.position.board.right)
    (hfrontPool : ∀ a ∈ frontU, a.2 ∈ H ∧ max oldU.position.bound (b oldU) < a.2)
    (hJfresh : ∀ x ∈ J, max oldU.position.bound (b oldU) < x)
    (hrelUpperU : upper.position.board.right.relaxed = true)
    (hnoUpperU : upper.position.board.right.NoLeafPending)
    (hbeforeUpperU : LabeledWord.BeforeBody U.anchor upper.position.board.right)
    (hnextUpperU : ∀ i ∈ upper.position.board.right.rootLabel,
      upper.position.board.right.bodyLabels.length < i → U.anchor ≤ i)
    (hUpperRoot : upper.position.board.right.rootLabel = U.upper)
    (hModeUpper : upper.position.mode = some true) (hModeSU : oldU.position.mode = some true)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        (z.position.board.right.bodyLabels.getD (U.anchor - 1) ∅).card = K)
    (hvalid : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) upper z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.CriticalPairSpec z.position.board.left.lastSelectedLabel.card
          (z.position.board.right.criticalPair z.position.board.left.lastSelectedLabel.card) ∧
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k ∧
        criticalLastColor z = true)
    (hSrel : oldU.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure oldT.position.board.left oldU.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldT.position.board.left)
    (hSstrict : oldT.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ oldT.position.board.left.currentLabel,
      oldT.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ oldU.position.board.left.rootLabel,
      i ≤ oldU.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ oldU.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ oldU.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  let BT := max (max oldT.position.bound (b oldT)) (max upper.position.bound (b upper))
  obtain ⟨T⟩ := RankedFirstLeafLabels.exists_of_infinite hJ BT R D (K + 1)
    (by omega) (by omega) hD
  obtain ⟨su, tu, c, hOldSU, hUpperTU, hpSU, hpTU, hc, hshape, hmSU, hmTU,
      _hiSU, hiTU, hrootSU, hrootTU, hOtherSU, hTUrel,
      P, hPtarget, hPside, hPstem, hPsource, hPpivot, hPupper⟩ :=
    strict_anchor_requests hHN hH hJH hJ blue oldT oldU upper T hwinT hwinU hwinUpper
      hpT hpUpper hmT hmUpper hTshape (le_max_left _ _) (le_max_right _ _)
      hpU hrelU hnoU hbeforeU hnextU hUshape hfrontU hfrontPool hJfresh
      hrelUpperU hnoUpperU hbeforeUpperU hnextUpperU hfixed
  have hTUlast : ∀ i ∈ tu.position.board.left.rootLabel,
      i ≤ tu.position.board.left.bodyLabels.length := by
    intro i hi
    rw [P.rootLabel, hPstem] at hi
    rw [P.body_length, hPstem]
    exact hTlast i hi
  have hSUroot : su.position.board.right.rootLabel = U.lower := hrootSU.trans hLowerRoot
  have hTUroot : tu.position.board.right.rootLabel = U.upper := hrootTU.trans hUpperRoot
  let B := max (max tu.position.bound (b tu)) (max su.position.bound (b su))
  obtain ⟨E⟩ := LastFirstLabels.exists_of_infinite hJ B K c hK hc
  exact strict_anchor_leaf_triangle (hJH.trans hHN) hJ blue tu su T U E P
    (hwinUpper.of_reachable (exactGame N blue) hUpperTU)
    ((hwinU.of_reachable (exactGame N blue) hOldSU).mono
      (exactGame N blue) hJH (fun _ => le_rfl)) hpTU hpSU hmTU hmSU hshape.symm
    (le_max_left _ _) (le_max_right _ _) hTUrel hTUlast hPside hPsource hPpivot hPupper
    hTUroot hiTU hSUroot hAfter (follow_mode_some hUpperTU hModeUpper)
    (follow_mode_some hOldSU hModeSU)
    (fun z w hpz hz => hvalid z w (hUpperTU.trans hpz) hz)
    (by simpa only [hOtherSU] using hSrel)
    (by simpa only [hPtarget, hOtherSU] using hS)
    (by simpa only [hPtarget] using hSUp) (by simpa only [hPtarget] using hSstrict)
    (by simpa only [hPtarget] using hSnext) (by simpa only [hOtherSU] using hSroot)
    (by simpa only [hOtherSU] using hgamma) (by simpa only [hOtherSU] using hSlast)

#print axioms strict_anchor_requests_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
