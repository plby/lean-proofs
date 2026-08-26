import ErdosProblems.Erdos118.PendingEndpointCounts
import ErdosProblems.Erdos118.PendingSuffixBalance

/-! Equal terminal before-last counts force the two actual pending
penultimate-body last-leaf endpoints to occur together. -/

namespace Erdos118.AlignedEndpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open InsideCounts LastBodyRefinement LeafSuffixCounts

theorem critical_iff {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    (∃ c : ℕ, P.roots = [c] ∧ P.leaves = []) ↔
      ∃ d : ℕ, Q.roots = [d] ∧ Q.leaves = [] := by
  obtain ⟨S, T, hp, heP, heQ, hbalance⟩ :=
    PendingSuffixBalance.exists_completion hH B P Q horder hblue
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hp
  have hS := PendingCounts.rootLabel_ne_nil_of_extension P S heP
  have hT := PendingCounts.rootLabel_ne_nil_of_extension Q T heQ
  have hlast := last_counts_of_before_eq S T hc hr ho hS hT (hall S T hp)
  rw [← PendingEndpointCounts.criterion P S T.stem hc.exactLeft hP heP,
    ← PendingEndpointCounts.criterion Q T S.stem hc.exactRight hQ heQ]
  omega

end Erdos118.AlignedEndpoint
