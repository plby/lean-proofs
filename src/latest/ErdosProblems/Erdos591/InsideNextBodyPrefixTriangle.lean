import ErdosProblems.Erdos591.UpperLastLeafCompletion
import ErdosProblems.Erdos591.DeferredBodyMarker
import ErdosProblems.Erdos591.SharedHeadPrefixesTriangle

/-!
# The strict singleton finishing branch with a future lower T body

The remaining upper T leaves fit inside the pending lower next-body
response. Complete the common U word before extending that response
beyond the last upper T leaf. The new segment starts after the actual
upper T completion bound and supplies the retained final-head prefix.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_next_body_prefix_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su upper : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinUpper : (exactGame N blue).ArchitectWins H b σ upper)
    (hmode : upper.position.mode = some true)
    (hpST : st.position.pending = some ⟨true, .advance 0⟩)
    {rSU : Request} (hpSU : su.position.pending = some rSU) (hsSU : rSU.side = true)
    (hstartS : su.position.board.left.parser ≠ .start)
    (hliveS : su.position.board.left.terminal = false)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hstartU : su.position.board.right.parser ≠ .start)
    (hlastU : ¬ Macro.Pending su.position.board.right)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right upper.position.board.left)
    (hrelT : st.position.board.right.relaxed = true)
    (hnoT : st.position.board.right.NoLeafPending) {i : ℕ}
    (hbeforeT : LabeledWord.BeforeBody i st.position.board.right)
    (hnextT : ∀ k ∈ st.position.board.right.rootLabel,
      st.position.board.right.bodyLabels.length < k → i ≤ k)
    {j : ℕ} (hfine : LabeledWord.UpToLeaf j upper.position.board.left)
    (hstrict : upper.position.board.left.leafIndex < j)
    (hroot : ∀ k ∈ upper.position.board.left.rootLabel,
      k ≤ upper.position.board.left.bodyLabels.length)
    (hlast : ∀ k ∈ upper.position.board.left.currentLabel, k ≤ j)
    {anchor : LabeledWord} {frontU : List (Finset ℕ × ℕ)}
    (hU : LabeledWord.SameStructure su.position.board.right anchor)
    (hfrontU : LabeledWord.LegalRun anchor frontU upper.position.board.right)
    (hpoolU : ∀ a ∈ frontU, a.2 ∈ H ∧ max su.position.bound (b su) < a.2) :
    ¬ blue.CliqueFree 3 := by
  let B := max st.position.bound (b st)
  obtain ⟨doneTU, doneSU, hTUPath, hSUStep, _hTUnone, _hSUnone, hTrel, hTlast,
      _hTidx, hTlabels, hSUother, hTUterm, hSUterm, hUshape, ts, hts, htsPool⟩ :=
    upper_last_leaf_and_shared_completion hHN hH blue su upper hwinUpper hmode hpSU hsSU
      hstartU hlastU hfine hstrict hroot hlast hU hfrontU hpoolU B
  have hwinTU := hwinUpper.of_reachable (exactGame N blue) hTUPath
  have hwinDoneSU := hwinSU.of_reachable (exactGame N blue) (.single hSUStep)
  have hwT := ((Position.history_dataInvariant doneTU).2.1 false).1
  have hstartT := LabeledWord.relaxed_ne_start hwT hTrel
  have hliveT := LabeledWord.relaxed_not_terminal hwT.2.1 hwT.2.2 hTrel
  obtain ⟨pendingTU, rT, hTPath, hbT, hpT, hsT⟩ :=
    request_opposite_complete σ doneTU true hTUterm hliveT
  obtain ⟨pendingSU, rS, hSPath, hbS, hpS, hsS⟩ := request_opposite_complete σ doneSU true
    hSUterm (by simpa only [Bool.not_true, Board.get, hSUother] using hliveS)
  have hsT' : rT.side = false := hsT
  have hsS' : rS.side = false := hsS
  have hbefore : doneTU.position.board.left.bodyLabels.length < i := by
    rw [hTlabels, ← hT.body_length]
    exact hbeforeT.2
  let C := max pendingTU.position.bound (b pendingTU)
  obtain ⟨st', hSTstep, _hSTnone, _hSTmarker, _hSTindex, hSTother,
      beforeT, hbeforeShape, newT, hnewT, hnewTPool⟩ :=
    deferred_next_marker_from_body_prefix_or_empty hHN hH blue σ st true hpST hrelT hnoT
      hbeforeT hnextT hT hts hbefore ((Position.history_dataInvariant doneTU).2.1 false).2
      htsPool C
  have hSTleft : st'.position.board.left = st.position.board.left := hSTother
  have hSshape : LabeledWord.SameStructure pendingSU.position.board.left
      st'.position.board.left := by
    simpa only [hbS, hSUother, hSTleft] using hS
  have hTshape : LabeledWord.SameStructure pendingTU.position.board.left beforeT := by
    simpa only [hbT] using hbeforeShape
  have hSprefix : ∃ anchor, LabeledWord.SameStructure pendingSU.position.board.left anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as st'.position.board.left ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max pendingSU.position.bound (b pendingSU) < a.2 :=
    ⟨_, hSshape, [], .nil _, by simp⟩
  have hTprefix : ∃ anchor, LabeledWord.SameStructure pendingTU.position.board.left anchor ∧
      ∃ as, LabeledWord.LegalRun anchor as st'.position.board.right ∧
        ∀ a ∈ as, a.2 ∈ H ∧ max pendingTU.position.bound (b pendingTU) < a.2 :=
    ⟨beforeT, hTshape, newT, hnewT, hnewTPool⟩
  exact triangle_of_two_pending_heads_from_prefixes hHN hH blue st' pendingSU pendingTU
    (hwinST.of_reachable (exactGame N blue) (.single hSTstep))
    (hwinDoneSU.of_reachable (exactGame N blue) hSPath)
    (hwinTU.of_reachable (exactGame N blue) hTPath) hpS hpT hsS' hsT'
    (by simpa only [hbS, hSUother] using hstartS)
    (by simpa only [hbT, Board.get] using hstartT)
    (by simpa only [hbS, hSUother] using hlastS)
    (by simpa only [hbT] using hTlast)
    (by simpa only [hbS] using hSUterm) (by simpa only [hbT] using hTUterm)
    (by simpa only [hbS, hbT] using hUshape.coordinates_eq) hSprefix hTprefix

#print axioms inside_next_body_prefix_triangle

end Erdos591.Positive.Game.Payoff
