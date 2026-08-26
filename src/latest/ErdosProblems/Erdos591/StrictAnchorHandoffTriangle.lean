import ErdosProblems.Erdos591.StrictAnchorHandoff
import ErdosProblems.Erdos591.RankedStrictFinishing
import ErdosProblems.Erdos591.SplicedNextRoot
import ErdosProblems.Erdos591.LastBodyEndpoint

/-!
# The paired saved-anchor endpoint yields the strict triangle

Submit the saved lower U and T first leaves, recover their actual
fresh separation from the replies, and apply the ranked finishing
theorem. The least future upper U root comes from the original spliced
labels, and every S datum is preserved by the two opposite replies.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem strict_anchor_handoff_triangle {N H HT HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p : Concrete.Hist N) {BT R D rank BU e g j r : ℕ}
    (T : RankedFirstLeafLabels HT BT R D rank) (U : SplicedRootLabels HU BU e g j r)
    (PT : PreparedSelection N H blue b σ p.position.board.left)
    (PU : PreparedSelection N H blue b σ p.position.board.right)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hModeSU : PU.target.position.mode = some true)
    (hPTside : PT.side = true) (hPUside : PU.side = true)
    (hPTsource : PT.lowerLabel = T.source)
    (hPTpivot : PT.labels.pivot = T.targetView.pivot)
    (hPTupper : PT.labels.upper = T.targetView.upper)
    (hUrel : p.position.board.right.relaxed = true)
    (hUat : p.position.board.right.leafIndex = PU.labels.pivot)
    (hUno : p.position.board.right.NoLeafPending)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hUbody : p.position.board.right.bodyLabels.length = U.anchor)
    (hLowerUroot : PU.target.position.board.right.rootLabel = U.lower)
    (hAfterU : r < g)
    (hsep : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0)
    (hnextRank : (p.position.board.left.currentLabel.filter
        (fun x => x ≤ PT.labels.pivot)).card =
      (p.position.board.left.currentLabel.filter
        (fun x => x ≤ p.position.board.left.leafIndex)).card + 1)
    (hTroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hSrel : PU.target.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure PT.target.position.board.left PU.target.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma PT.target.position.board.left)
    (hSstrict : PT.target.position.board.left.leafIndex < gamma)
    (hSnext : ∀ i ∈ PT.target.position.board.left.currentLabel,
      PT.target.position.board.left.leafIndex < i → gamma ≤ i)
    (hSroot : ∀ i ∈ PU.target.position.board.left.rootLabel,
      i ≤ PU.target.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ PU.target.position.board.left.currentLabel)
    (hSlast : ∀ i ∈ PU.target.position.board.left.currentLabel, i ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  obtain ⟨tu, st, su, hpTU, hSTstep, hSUstep, _hTUnone, _hSTnone, _hSUnone,
      hTUrel, hTUright, hTUlabel, hTUindex, hTUsep, hTshape, hUshape, hSTrel, hSUrel,
      hSTlabel, _hSUlabel, _hSTindex, _hSUindex, _hSTroot, hSUroot, hSTother, hSUother⟩ :=
    strict_anchor_handoff hHN hH blue PT PU hwin hUrel hUat hsep hnextRank
  have hSTleft : st.position.board.left = PT.target.position.board.left := by
    simpa only [hPTside, Bool.not_true, Board.get] using hSTother
  have hSUleft : su.position.board.left = PU.target.position.board.left := by
    simpa only [hPUside, Bool.not_true, Board.get] using hSUother
  have hSTsep : ∀ x ∈ st.position.board.left.coordinates,
      x ≤ st.position.board.right.coordinates.getLastD 0 := by
    simpa only [hPTside, Bool.not_true, Board.get] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hSTstep).reply_separation
        PT.targetPending
  have hSUsep : ∀ x ∈ su.position.board.left.coordinates,
      x ≤ su.position.board.right.coordinates.getLastD 0 := by
    simpa only [hPUside, Bool.not_true, Board.get] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hSUstep).reply_separation
        PU.targetPending
  obtain ⟨ts, hts, _⟩ := follow_word_inputs hpTU 0 (fun _ => Nat.zero_le _) false
  obtain ⟨a, k, hparse⟩ := PT.upto.parser_leaves ((Position.history_dataInvariant p).2.1 false).1
  have hstart : p.position.board.left.parser ≠ .start := by simp [hparse]
  have hTbody := (hts.last_body_relaxed_labels hstart hTroot hTUrel).1
  have hTRootEq := hts.rootLabel_eq hstart
  have hTrootFinal : ∀ i ∈ tu.position.board.left.rootLabel,
      i ≤ tu.position.board.left.bodyLabels.length := by
    intro i hi
    change tu.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hTbody
    rw [hTbody]
    exact hTroot i (hTRootEq ▸ hi)
  obtain ⟨nextU, hnextMem, hAnchorLt, hnextLeast, hLowerLt⟩ := U.next_after_anchor hAfterU
  have hUpperRoot : tu.position.board.right.rootLabel = U.upper := by
    rw [hTUright]
    exact hUroot
  have hUpperBody : tu.position.board.right.bodyLabels.length = U.anchor := by
    rw [hTUright]
    exact hUbody
  have hBeforeU : LabeledWord.BeforeBody nextU tu.position.board.right :=
    ⟨hUpperRoot ▸ hnextMem, by rw [hUpperBody]; exact hAnchorLt⟩
  have hNextU : ∀ i ∈ tu.position.board.right.rootLabel,
      tu.position.board.right.bodyLabels.length < i → nextU ≤ i := by
    simpa only [hUpperRoot, hUpperBody] using hnextLeast
  have hLowerBeforeU : ∀ i ∈ su.position.board.right.rootLabel, i < nextU := by
    have hr : su.position.board.right.rootLabel = U.lower := by
      simpa only [hPUside, Board.get, hLowerUroot] using hSUroot
    simpa only [hr] using hLowerLt
  exact ranked_strict_finishing hHN hH blue st su tu T
    (PT.targetWinning.of_reachable (exactGame N blue) (.single hSTstep))
    (PU.targetWinning.of_reachable (exactGame N blue) (.single hSUstep))
    (hwin.of_reachable (exactGame N blue) hpTU)
    (follow_mode_some (.single hSUstep) hModeSU) (follow_mode_some hpTU hmode)
    (by simpa only [hPTside, Board.get] using hSTrel)
    (by simpa only [hSUleft] using hSrel)
    (by simpa only [hPUside, Board.get] using hSUrel) hTUrel
    (by simpa only [hTUright] using hUrel) hSTsep hSUsep hTUsep
    (by simpa only [hSTleft, hSUleft] using hS)
    (by simpa only [hPTside, Board.get] using hTshape.symm)
    (by simpa only [hPUside, Board.get] using hUshape)
    (by simpa only [hSTleft] using hSUp) (by simpa only [hSTleft] using hSstrict)
    (by simpa only [hSTleft] using hSnext) (by simpa only [hSUleft] using hSroot)
    (by simpa only [hSUleft] using hgamma) (by simpa only [hSUleft] using hSlast)
    (by simpa only [hPTside, Board.get, hPTupper] using hSTlabel)
    (hTUlabel.trans hPTsource) (hTUindex.trans hPTpivot) hTrootFinal
    (by simpa only [hTUright] using hUno) hBeforeU hNextU hLowerBeforeU

#print axioms strict_anchor_handoff_triangle

end Erdos591.Positive.Game.Payoff
