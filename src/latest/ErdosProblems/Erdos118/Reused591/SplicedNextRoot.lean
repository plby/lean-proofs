import ErdosProblems.Erdos118.Reused591.SplicedRootLabels

namespace Erdos118.Reused591

/-! # The next upper root after the anchor lies beyond every lower root -/

namespace Erdos591.Positive.Game.SplicedRootLabels

theorem next_after_first_le_anchor {H : Set ℕ} {B e d j r : ℕ}
    (U : SplicedRootLabels H B e d j r) :
    ∃ i, i ∈ U.upper ∧ U.first < i ∧ i ≤ U.anchor ∧
      ∀ k ∈ U.upper, U.first < k → i ≤ k := by
  classical
  let F := U.upper.filter (fun k => U.first < k)
  have hF : F.Nonempty :=
    ⟨U.anchor, Finset.mem_filter.mpr ⟨U.anchor_upper, U.first_lt_anchor⟩⟩
  let i := F.min' hF
  have hi := Finset.mem_filter.mp (Finset.min'_mem F hF)
  refine ⟨i, hi.1, hi.2, ?_, ?_⟩
  · exact Finset.min'_le F U.anchor
      (Finset.mem_filter.mpr ⟨U.anchor_upper, U.first_lt_anchor⟩)
  · exact fun k hk hlt => Finset.min'_le F k (Finset.mem_filter.mpr ⟨hk, hlt⟩)

theorem next_after_anchor {H : Set ℕ} {B e d j r : ℕ}
    (U : SplicedRootLabels H B e d j r) (hrd : r < d) :
    ∃ i, i ∈ U.upper ∧ U.anchor < i ∧
      (∀ k ∈ U.upper, U.anchor < k → i ≤ k) ∧
      ∀ k ∈ U.lower, k < i := by
  classical
  let F := U.upper.filter (fun k => U.anchor < k)
  have hF : F.Nonempty := by
    by_contra hn
    have hall : ∀ k ∈ U.upper, k ≤ U.anchor := by
      intro k hk
      by_contra hlt
      exact hn ⟨k, Finset.mem_filter.mpr ⟨hk, lt_of_not_ge hlt⟩⟩
    have heq : U.upper.filter (fun k => k ≤ U.anchor) = U.upper :=
      Finset.filter_eq_self.mpr hall
    have hcard := U.anchor_upper_rank
    rw [heq, U.upper_card] at hcard
    omega
  let i := F.min' hF
  have hi := Finset.mem_filter.mp (Finset.min'_mem F hF)
  have hlast : U.last < i := (U.upper_gap i hi.1).resolve_left (not_le_of_gt hi.2)
  refine ⟨i, hi.1, hi.2, ?_, ?_⟩
  · exact fun k hk hlt => Finset.min'_le F k (Finset.mem_filter.mpr ⟨hk, hlt⟩)
  · intro k hk
    have hle : k ≤ U.last := by
      rw [← U.lower_sup]
      exact Finset.le_sup (f := id) hk
    exact hle.trans_lt hlast

#print axioms next_after_anchor
#print axioms next_after_first_le_anchor

end Erdos591.Positive.Game.SplicedRootLabels

end Erdos118.Reused591
