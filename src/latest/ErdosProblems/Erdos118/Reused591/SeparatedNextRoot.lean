import ErdosProblems.Erdos118.Reused591.LocalizedNonlastCheckpoint

namespace Erdos118.Reused591

/-! # The next separated upper root is beyond every lower selected body -/

namespace Erdos591.Positive.Game.SeparatedRootLabels

theorem next_after_first {H : Set ℕ} {B e d j : ℕ}
    (U : SeparatedRootLabels H B e d j) (hd : 2 ≤ d) :
    ∃ i, i ∈ U.upper ∧ U.first < i ∧
      (∀ k ∈ U.upper, U.first < k → i ≤ k) ∧
      ∀ k ∈ U.lower, k < i := by
  classical
  let F := U.upper.filter (fun k => U.first < k)
  have hF : F.Nonempty := by
    by_contra hn
    have hall : ∀ k ∈ U.upper, k ≤ U.first := by
      intro k hk
      by_contra hlt
      exact hn ⟨k, Finset.mem_filter.mpr ⟨hk, lt_of_not_ge hlt⟩⟩
    have heq : U.upper.filter (fun k => k ≤ U.first) = U.upper :=
      Finset.filter_eq_self.mpr hall
    have hcard := U.first_upper_rank
    rw [heq, U.upper_card] at hcard
    omega
  let i := F.min' hF
  have hi := Finset.mem_filter.mp (Finset.min'_mem F hF)
  have hlast : U.last < i := (U.upper_after i hi.1).resolve_left (ne_of_gt hi.2)
  refine ⟨i, hi.1, hi.2, ?_, ?_⟩
  · exact fun k hk hlt => Finset.min'_le F k (Finset.mem_filter.mpr ⟨hk, hlt⟩)
  · intro k hk
    have hle : k ≤ U.last := by
      rw [← U.lower_sup]
      exact Finset.le_sup (f := id) hk
    exact hle.trans_lt hlast

#print axioms next_after_first

end Erdos591.Positive.Game.SeparatedRootLabels

end Erdos118.Reused591
