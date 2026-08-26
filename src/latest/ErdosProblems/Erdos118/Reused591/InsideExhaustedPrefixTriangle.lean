import ErdosProblems.Erdos118.Reused591.UpperLastLeafCompletion
import ErdosProblems.Erdos118.Reused591.DeferredCompleteTail
import ErdosProblems.Erdos118.Reused591.SharedHeadPrefixesTriangle

namespace Erdos118.Reused591

/-!
# The strict finishing branch with no remaining lower T selection

The upper T selected prefix is retained inside the pending lower
completion. Finish U first, record both head bounds, then choose
only the new lower completion tail above the upper T head bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_exhausted_prefix_triangle {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (st su upper : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinUpper : (exactGame N blue).ArchitectWins H b σ upper)
    (hmode : upper.position.mode = some true)
    {rST : Request} (hpST : st.position.pending = some rST) (hsST : rST.side = true)
    {rSU : Request} (hpSU : su.position.pending = some rSU) (hsSU : rSU.side = true)
    (hstartS : su.position.board.left.parser ≠ .start)
    (hliveS : su.position.board.left.terminal = false)
    (hlastS : ¬ Macro.Pending su.position.board.left)
    (hstartU : su.position.board.right.parser ≠ .start)
    (hlastU : ¬ Macro.Pending su.position.board.right)
    (hS : LabeledWord.SameStructure su.position.board.left st.position.board.left)
    (hT : LabeledWord.SameStructure st.position.board.right upper.position.board.left)
    (hstartOldT : st.position.board.right.parser ≠ .start)
    (hlastOldT : ¬ Macro.Pending st.position.board.right)
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
      _hTidx, _hTlabels, hSUother, hTUterm, hSUterm, hUshape, ts, hts, htsPool⟩ :=
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
  let C := max pendingTU.position.bound (b pendingTU)
  obtain ⟨st', hSTstep, _hSTnone, _hSTterm, hSTother,
      beforeT, hbeforeShape, newT, hnewT, hnewTPool⟩ :=
    deferred_complete_tail_from_prefix hHN hH blue σ st hpST
      (by simpa only [hsST, Board.get] using hstartOldT)
      (by simpa only [hsST, Board.get] using hlastOldT)
      (by simpa only [hsST, Board.get] using hT) hts
      ((Position.history_dataInvariant doneTU).2.1 false).2 htsPool C
  have hSTleft : st'.position.board.left = st.position.board.left := by
    simpa only [hsST, Bool.not_true, Board.get] using hSTother
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
    ⟨beforeT, hTshape, newT, by simpa only [hsST, Board.get] using hnewT, hnewTPool⟩
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

#print axioms inside_exhausted_prefix_triangle

end Erdos591.Positive.Game.Payoff


end Erdos118.Reused591
