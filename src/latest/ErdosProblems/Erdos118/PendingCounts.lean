import ErdosProblems.Erdos118.LastSuffixCounts

/-! The completed-pair count identities transferred through one actual
blue completion of exact pending last-body states. -/

namespace Erdos118.PendingCounts

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open SelectedGapCounts LastBodyRefinement LastMarkerRefinement InsideCounts BlueRuns

theorem selected_filter_of_prefix (S T : Stem) (hp : S.bodyLabels <+: T.bodyLabels) :
    (selected T).filter (fun a ↦ a.1 < S.bodyLabels.length) = selected S := by
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, mem_selected]
  constructor
  · rintro ⟨⟨hiT, hjT⟩, hiS⟩
    exact ⟨hiS, by rw [hp.getElem hiS]; exact hjT⟩
  · rintro ⟨hiS, hjS⟩
    have hiT := hiS.trans_le hp.length_le
    refine ⟨⟨hiT, ?_⟩, hiS⟩
    rw [← hp.getElem hiS]
    exact hjS

theorem beforeLast_of_extension (P : Pending) (S : Completed)
    (hP : ExactSlots.Exact (.leaf P)) (hroots : P.roots = [])
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) :
    beforeLast S = (selected P.position.stem).card := by
  have hp : P.position.stem.bodyLabels <+: S.stem.bodyLabels :=
    (List.prefix_append _ [P.position.label]).trans hext.labels.bodies
  unfold beforeLast
  rw [lastIndex_of_extension P S hP hroots hext.labels]
  have hlen : P.position.stem.done.length = P.position.stem.bodyLabels.length := by
    simp [Stem.bodyLabels]
  rw [hlen, selected_filter_of_prefix _ _ hp]

theorem rootLabel_ne_nil_of_extension (P : Pending) (S : Completed)
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) : S.stem.rootLabel ≠ [] := by
  have he : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root _ rfl)
  rw [he]
  exact List.ne_nil_of_mem P.rootSelected

theorem inside_count {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    (selected P.position.stem).card + P.position.label.length =
      (selected Q.position.stem).card + Q.position.label.length + 1 := by
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) hblue
  obtain ⟨hroot, hclear, horient, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hpay
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have h := inside_decomposition S T hclear hroot horient
    (rootLabel_ne_nil_of_extension P S heP) (rootLabel_ne_nil_of_extension Q T heQ)
  rw [beforeLast_of_extension P S hP hPR heP, beforeLast_of_extension Q T hQ hQR heQ,
    lastLabel_of_extension P S hP hPR heP.labels,
    lastLabel_of_extension Q T hQ hQR heQ.labels] at h
  exact h

theorem marker_lt_iff_count_le {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    P.position.size < Q.position.size ↔
      (selected P.position.stem).card ≤ (selected Q.position.stem).card := by
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) hblue
  obtain ⟨hroot, hclear, horient, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hpay
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have h := LastSuffixCounts.marker_lt_iff_before_le S T hclear hroot horient
    (rootLabel_ne_nil_of_extension P S heP) (rootLabel_ne_nil_of_extension Q T heQ)
  rw [beforeLast_of_extension P S hP hPR heP, beforeLast_of_extension Q T hQ hQR heQ,
    lastMarker_of_extension P S hP hPR heP, lastMarker_of_extension Q T hQ hQR heQ] at h
  exact h

end Erdos118.PendingCounts
