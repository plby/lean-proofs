import ErdosProblems.Erdos118.Reused591.InsideStrictFinishing
import ErdosProblems.Erdos118.Reused591.RankedFirstLeafLabels

namespace Erdos118.Reused591

/-!
# The strict finishing theorem at the actual paired anchor handoff

The stored T label is the prescribed-rank pattern already used by
the anchor construction. Its target size decides the next-leaf versus
exhausted-current-body alternatives. Issue the actual old S and upper
U requests before applying the unified finishing construction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem ranked_strict_finishing {N H HT : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su tu : Concrete.Hist N) {BT R D rank : ℕ}
    (T : RankedFirstLeafLabels HT BT R D rank)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ tu)
    (hmSU : su.position.mode = some true) (hmTU : tu.position.mode = some true)
    (hSTrel : st.position.board.right.relaxed = true)
    (hSUleft : su.position.board.left.relaxed = true)
    (hSUright : su.position.board.right.relaxed = true)
    (hTUleft : tu.position.board.left.relaxed = true)
    (hTUright : tu.position.board.right.relaxed = true)
    (hSTsep : ∀ x ∈ st.position.board.left.coordinates,
      x ≤ st.position.board.right.coordinates.getLastD 0)
    (hSUsep : ∀ x ∈ su.position.board.left.coordinates,
      x ≤ su.position.board.right.coordinates.getLastD 0)
    (hTUsep : ∀ x ∈ tu.position.board.right.coordinates,
      x ≤ tu.position.board.left.coordinates.getLastD 0)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right tu.position.board.left)
    (hU : LabeledWord.SameStructure tu.position.board.right su.position.board.right)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma st.position.board.left)
    (hSstrict : st.position.board.left.leafIndex < gamma)
    (hSnext : ∀ j ∈ st.position.board.left.currentLabel,
      st.position.board.left.leafIndex < j → gamma ≤ j)
    (hSroot : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ su.position.board.left.currentLabel)
    (hSlast : ∀ j ∈ su.position.board.left.currentLabel, j ≤ gamma)
    (hTtarget : st.position.board.right.currentLabel = T.targetView.upper)
    (hTsource : tu.position.board.left.currentLabel = T.source)
    (hTindex : tu.position.board.left.leafIndex = T.targetView.pivot)
    (hTroot : ∀ i ∈ tu.position.board.left.rootLabel,
      i ≤ tu.position.board.left.bodyLabels.length)
    (hUno : tu.position.board.right.NoLeafPending) {nextU : ℕ}
    (hBeforeU : LabeledWord.BeforeBody nextU tu.position.board.right)
    (hNextU : ∀ i ∈ tu.position.board.right.rootLabel,
      tu.position.board.right.bodyLabels.length < i → nextU ≤ i)
    (hLowerBeforeU : ∀ i ∈ su.position.board.right.rootLabel, i < nextU) :
    ¬ blue.CliqueFree 3 := by
  classical
  obtain ⟨oldST, hstPath, hbST, hpST⟩ := winning_next_leaf_request_after_other hHN hH blue
    hwinST false hSUp hSstrict hSTrel hSTsep
  obtain ⟨oldTU, htuPath, hbTU, hpTU⟩ := winning_next_body_after_fresh_leaf hHN hH blue
    hwinTU false hTUleft hTUsep hTUright hBeforeU
  have hmaxMem : T.source.sup id ∈ T.source := by
    simpa using Finset.sup_mem_of_nonempty (f := id) ⟨_, T.pivot_source⟩
  have hupper : LabeledWord.UpToLeaf (T.source.sup id) tu.position.board.left :=
    ⟨(of_decide_eq_true hTUleft).2.1, hTsource ▸ hmaxMem,
      by rw [hTindex]; exact T.pivot_lt_last.le⟩
  have hstrict : tu.position.board.left.leafIndex < T.source.sup id := by
    rw [hTindex]
    exact T.pivot_lt_last
  have hlast : ∀ j ∈ tu.position.board.left.currentLabel, j ≤ T.source.sup id := by
    intro j hj
    exact Finset.le_sup (f := id) (hTsource ▸ hj)
  have htargetIndex : st.position.board.right.leafIndex = T.targetView.pivot :=
    hT.leaf_eq.trans hTindex
  have hlower :
      (LabeledWord.UpToLeaf (T.source.sup id) st.position.board.right ∧
        ∀ j ∈ st.position.board.right.currentLabel,
          st.position.board.right.leafIndex < j → T.source.sup id ≤ j) ∨
      st.position.board.right.NoLeafPending := by
    by_cases hD : 2 ≤ D
    · left
      refine ⟨⟨(of_decide_eq_true hSTrel).2.1, hTtarget ▸ T.last_target hD, ?_⟩, ?_⟩
      · rw [htargetIndex]
        exact T.pivot_lt_last.le
      · simpa only [hTtarget, htargetIndex] using T.target_next
    · right
      have hDpos : 0 < D := by
        rw [← T.targetView.upper_card]
        exact Finset.card_pos.mpr ⟨_, T.targetView.pivot_upper⟩
      have heq : D = 1 := by omega
      subst D
      intro j hj
      rw [hTtarget, T.target_singleton] at hj
      rw [Finset.mem_singleton.mp hj, htargetIndex]
  exact inside_strict_finishing hHN hH blue oldST su oldTU
    (hwinST.of_reachable (exactGame N blue) hstPath) hwinSU
    (hwinTU.of_reachable (exactGame N blue) htuPath)
    hmSU (follow_mode_some htuPath hmTU) hpST hpTU hSUleft hSUright hSUsep
    (by simpa only [hbST] using hS) (by simpa only [hbST, hbTU] using hT)
    (by simpa only [hbTU] using hU)
    (by simpa only [hbST] using hSUp) (by simpa only [hbST] using hSstrict)
    (by simpa only [hbST] using hSnext) hSroot hgamma hSlast
    (by simpa only [hbST] using hSTrel)
    (by simpa only [hbTU] using hupper) (by simpa only [hbTU] using hstrict)
    (by simpa only [hbTU] using hTroot) (by simpa only [hbTU] using hlast)
    (by simpa only [hbST] using hlower)
    (by simpa only [hbTU] using hTUright) (by simpa only [hbTU] using hUno)
    (by simpa only [hbTU] using hBeforeU) (by simpa only [hbTU] using hNextU) hLowerBeforeU

#print axioms ranked_strict_finishing

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
