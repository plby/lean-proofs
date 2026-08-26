import ErdosProblems.Erdos118.ConsecutiveSuffixCounts
import ErdosProblems.Erdos118.CompletionReplay
import ErdosProblems.Erdos118.InsideCounts

/-! One actual blue completion above the old pair bound gives exact
remaining selected-count balance at the two pending endpoints. -/

namespace Erdos118.PendingSuffixBalance

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns LeafSuffixCounts

private theorem last_mem (xs : List ℕ) (hne : xs ≠ []) : xs.getLastD 0 ∈ xs := by
  simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne, Option.getD_some]
    using List.getLast_mem hne

theorem exists_completion {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (P Q : Pending)
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    ∃ S T : Completed, GraphPayoff.payoff B .inside S T = true ∧
      SkippedCuts.StateExtension (.leaf P) (.complete S) ∧
      SkippedCuts.StateExtension (.leaf Q) (.complete T) ∧
      (remaining S.stem P.position.stem.done.length P.position.entries.length).card =
        (remaining T.stem Q.position.stem.done.length Q.position.entries.length).card + 1 := by
  let b := pairBound (.leaf P, .leaf Q)
  let J := H \ Set.Iic b
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic b)
  have hJH : J ⊆ H := fun _ hx ↦ hx.1
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hJ (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) (hblue.almost_mono (RamseyGame.almostSubset_of_subset hJH))
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  obtain ⟨u, v, hu, hv, huf, _⟩ := CompletionReplay.run_supported_suffixes hrun
  change S.stem.ordinary = P.position.ordinary ++ u at hu
  change T.stem.ordinary = Q.position.ordinary ++ v at hv
  obtain ⟨_, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hp
  have hPne : P.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
  have hQne : Q.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
  let x := P.position.ordinary.getLastD 0
  let y := Q.position.ordinary.getLastD 0
  let pre := P.position.ordinary.dropLast
  let before := Q.position.ordinary.dropLast
  have hpx : pre ++ [x] = P.position.ordinary := by
    simpa only [pre, x, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hPne,
      Option.getD_some] using List.dropLast_concat_getLast hPne
  have hqy : before ++ [y] = Q.position.ordinary := by
    simpa only [before, y, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hQne,
      Option.getD_some] using List.dropLast_concat_getLast hQne
  have hS : pre ++ x :: u = S.stem.ordinary := by
    rw [hu, ← hpx]
    simp only [List.append_assoc, List.singleton_append]
  have hT : before ++ y :: v = T.stem.ordinary := by
    rw [hv, ← hqy]
    simp only [List.append_assoc, List.singleton_append]
  have hdropP : S.stem.ordinary.drop (P.position.ordinary.length - 1) = x :: u := by
    rw [hu, List.drop_append_of_le_length (Nat.sub_le _ _), List.drop_length_sub_one hPne]
    simp only [x, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hPne,
      Option.getD_some, List.singleton_append]
  have hdropQ : T.stem.ordinary.drop (Q.position.ordinary.length - 1) = y :: v := by
    rw [hv, List.drop_append_of_le_length (Nat.sub_le _ _), List.drop_length_sub_one hQne]
    simp only [y, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hQne,
      Option.getD_some, List.singleton_append]
  have hincS : (pre ++ x :: u).Pairwise (· < ·) :=
    hS ▸ S.stem.increasing.sublist S.stem.ordinary_sublist
  have hincT : (before ++ y :: v).Pairwise (· < ·) :=
    hT ▸ T.stem.increasing.sublist T.stem.ordinary_sublist
  have hdisj : (pre ++ x :: u).Disjoint (before ++ y :: v) := by
    rw [hS, hT]
    exact InsideCounts.ordinary_disjoint hc
  have hfresh : ∀ z ∈ u, y < z := by
    intro z hz
    have hyb : y ≤ b := pairBound_right (.leaf P, .leaf Q)
      (Q.position.ordinary_sublist.subset (last_mem Q.position.ordinary hQne))
    exact hyb.trans_lt (Nat.lt_of_not_ge (huf z hz).2)
  have hSn : S.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  have hTn : T.stem.ordinary ≠ [] := by simp [Stem.ordinary]
  have hlast : (y :: v).getLastD 0 < (x :: u).getLastD 0 := by
    have he : T.stem.ordinary.getLastD 0 < S.stem.ordinary.getLastD 0 := by
      simpa only [GraphPayoff.Oriented, GraphPayoff.endpoint, List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast hSn, List.getLast?_eq_some_getLast hTn,
        Option.getD_some] using ho
    rw [← hS, ← hT] at he
    simpa only [List.getLastD_eq_getLast?,
      List.getLast?_append_of_ne_nil pre (List.cons_ne_nil x u),
      List.getLast?_append_of_ne_nil before (List.cons_ne_nil y v)] using he
  have hpref : P.position.ordinary <+: S.stem.ordinary := heP.ordinary
  have hqref : Q.position.ordinary <+: T.stem.ordinary := heQ.ordinary
  have hbalance := ConsecutiveSuffixCounts.balance hincS hincT hdisj horder hfresh hlast
  have hleft := suffix_gaps_card S.stem T.stem S.full (InsideCounts.ordinary_disjoint hc)
    hc.interiorLeft hc.exactLeft P.position.toInterior
    (by rw [Position.toInterior_word]; exact hpref)
  have hright := suffix_gaps_card T.stem S.stem T.full (InsideCounts.ordinary_disjoint hc).symm
    hc.interiorRight hc.exactRight Q.position.toInterior
    (by rw [Position.toInterior_word]; exact hqref)
  rw [Position.toInterior_word] at hleft hright
  simp only [Position.toInterior, List.length_map] at hleft hright
  rw [hdropP] at hleft
  rw [hdropQ] at hright
  rw [hS, hT, hleft, hright] at hbalance
  exact ⟨S, T, hp, heP, heQ, hbalance⟩

end Erdos118.PendingSuffixBalance
