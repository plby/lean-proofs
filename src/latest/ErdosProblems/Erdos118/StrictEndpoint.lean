import ErdosProblems.Erdos118.CriticalCursor
import ErdosProblems.Erdos118.StrictCriticalBounds

/-! A left critical endpoint in the strict class leaves the right word
before its last selected body, and before two future bodies when its
current selected leaf is exhausted. -/

namespace Erdos118.StrictEndpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open InsideCounts LastBodyRefinement LeafSuffixCounts

theorem future_roots {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hcritical : ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [])
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    Q.roots ≠ [] ∧ (Q.leaves = [] → 2 ≤ Q.roots.length) := by
  obtain ⟨S, T, hp, heP, heQ, hbalance⟩ :=
    PendingSuffixBalance.exists_completion hH B P Q horder hblue
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hp
  have hS := PendingCounts.rootLabel_ne_nil_of_extension P S heP
  have hT := PendingCounts.rootLabel_ne_nil_of_extension Q T heQ
  have hgap := last_counts_of_before_lt S T hc hr ho hS hT (hall S T hp)
  have hleft := (PendingEndpointCounts.criterion P S T.stem hc.exactLeft hP heP).mpr hcritical
  have hright : (lastLabel T).length + 1 <
      (remaining T.stem Q.position.stem.done.length Q.position.entries.length).card := by omega
  have hnonempty : Q.roots ≠ [] := by
    intro he
    have hindex := lastIndex_of_extension Q T hQ he heQ.labels
    have hb := SelectedEndpointCounts.remaining_last_le T S.stem hc.exactRight hT
      Q.position.entries.length
    rw [hindex] at hb
    omega
  refine ⟨hnonempty, ?_⟩
  intro hQL
  obtain ⟨c, rest, hR⟩ := List.exists_cons_of_ne_nil hnonempty
  have hrne : rest ≠ [] := by
    intro he
    have hcQ : ∃ d : ℕ, Q.roots = [d] ∧ Q.leaves = [] := ⟨c, by rw [hR, he], hQL⟩
    have hcount := (PendingEndpointCounts.criterion Q T S.stem hc.exactRight hQ heQ).mpr hcQ
    omega
  have hlen := List.length_pos_iff.mpr hrne
  rw [hR, List.length_cons]
  omega

end Erdos118.StrictEndpoint
