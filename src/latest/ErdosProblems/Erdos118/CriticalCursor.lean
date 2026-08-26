import ErdosProblems.Erdos118.CriticalPair
import ErdosProblems.Erdos118.PendingEndpointCounts
import ErdosProblems.Erdos118.PendingSuffixBalance

/-! Recover the actual pending cursor and its ranks from a terminal
selected-suffix count, retaining exact root and body annotations. -/

namespace Erdos118.CriticalCursor

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open CutIndices SelectedGapCounts LeafSuffixCounts InsideCounts LastBodyRefinement CriticalPair

theorem current_label (P : Pending) (S : Completed)
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) :
    S.stem.bodyLabels.getD P.position.stem.done.length [] = P.position.label := by
  have hp : P.position.bodyLabels <+: S.stem.bodyLabels := hext.labels.bodies
  have hi : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  rw [List.getD_eq_getElem _ _ (hi.trans_le hp.length_le), ← hp.getElem hi]
  simp [Position.bodyLabels, Stem.bodyLabels]

theorem selected_of_extension (P : Pending) (S : Completed)
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) :
    (⟨P.position.stem.done.length, P.position.entries.length⟩ : Σ _ : ℕ, ℕ) ∈ selected S.stem := by
  have hp : P.position.bodyLabels <+: S.stem.bodyLabels := hext.labels.bodies
  have hi : P.position.stem.done.length < S.stem.bodyLabels.length := by
    have hi : P.position.stem.done.length < P.position.bodyLabels.length := by
      simp [Position.bodyLabels, Stem.bodyLabels]
    exact hi.trans_le hp.length_le
  apply Finset.mem_sigma.mpr
  exact ⟨Finset.mem_range.mpr hi, List.mem_toFinset.mpr (current_label P S hext ▸ P.leafSelected)⟩

theorem pair_of_extension (P : Pending) (S : Completed)
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) (n : ℕ)
    (hcount : (remaining S.stem P.position.stem.done.length P.position.entries.length).card = n) :
    CriticalPair.pair S.stem n = ⟨P.position.stem.done.length, P.position.entries.length⟩ :=
  pair_eq_of_spec ⟨selected_of_extension P S hext, hcount⟩

theorem observables (P : Pending) (S : Completed) (hP : ExactSlots.Exact (.leaf P))
    (hext : SkippedCuts.StateExtension (.leaf P) (.complete S)) (n : ℕ)
    (hcount : (remaining S.stem P.position.stem.done.length P.position.entries.length).card = n) :
    bodyRank S.stem n = (P.position.stem.rootLabel.toFinset.filter
      (fun i ↦ i ≤ P.position.stem.done.length + 1)).card ∧
    leafRank S.stem n = (P.position.label.toFinset.filter
      (fun j ↦ j ≤ P.position.entries.length)).card ∧
    (last S.stem n = true ↔ P.leaves = []) := by
  classical
  have he := pair_of_extension P S hext n hcount
  have hr : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root _ rfl)
  have hb := current_label P S hext
  refine ⟨?_, ?_, ?_⟩
  · simp only [bodyRank, he, hr]
  · simp only [leafRank, he, hb]
  · simp only [last, he, hb, decide_eq_true_eq]
    rw [hP.2]
    constructor
    · intro h
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨hjl, hjgt⟩ := List.mem_filter.mp hj
      exact (not_lt_of_ge (h j hjl)) (of_decide_eq_true hjgt)
    · intro h j hj
      by_contra hn
      have hm : j ∈ ExactSlots.above P.position.label P.position.entries.length :=
        List.mem_filter.mpr ⟨hj, decide_eq_true (Nat.lt_of_not_ge hn)⟩
      rw [h] at hm
      exact List.not_mem_nil hm

theorem at_left_endpoint {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hcritical : ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [])
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    ∃ S T : Completed, GraphPayoff.payoff B .inside S T = true ∧
      SkippedCuts.StateExtension (.leaf P) (.complete S) ∧
      SkippedCuts.StateExtension (.leaf Q) (.complete T) ∧
      CriticalPair.pair T.stem (lastLabel S).length =
        ⟨Q.position.stem.done.length, Q.position.entries.length⟩ ∧
      bodyRank T.stem (lastLabel S).length = (Q.position.stem.rootLabel.toFinset.filter
        (fun i ↦ i ≤ Q.position.stem.done.length + 1)).card ∧
      leafRank T.stem (lastLabel S).length = (Q.position.label.toFinset.filter
        (fun j ↦ j ≤ Q.position.entries.length)).card ∧
      (last T.stem (lastLabel S).length = true ↔ Q.leaves = []) := by
  obtain ⟨S, T, hp, heP, heQ, hbalance⟩ :=
    PendingSuffixBalance.exists_completion hH B P Q horder hblue
  have hc := ((GraphPayoff.payoff_true_iff B .inside S T).mp hp).2.1
  have hl := (PendingEndpointCounts.criterion P S T.stem hc.exactLeft hP heP).mpr hcritical
  have hcount : (remaining T.stem Q.position.stem.done.length Q.position.entries.length).card =
      (lastLabel S).length := by omega
  exact ⟨S, T, hp, heP, heQ, pair_of_extension Q T heQ _ hcount,
    observables Q T hQ heQ _ hcount⟩

end Erdos118.CriticalCursor
