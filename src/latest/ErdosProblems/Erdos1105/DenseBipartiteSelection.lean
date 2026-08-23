import ErdosProblems.Erdos1105.DenseBipartite

namespace Erdos1105

open Finset

/-- Trim a bounded integer degree sequence to the required size while
retaining two units above the `(l-1)` baseline. -/
theorem exists_dense_degree_subset {V : Type*} [DecidableEq V] (f : V → ℕ) {l : ℕ}
    (hl : 2 ≤ l) (S : Finset V) (hsize : l ≤ S.card)
    (hcap : ∀ v ∈ S, f v ≤ l) (hsum : (l - 1) * S.card + 2 ≤ ∑ v ∈ S, f v) :
    ∃ B ⊆ S, B.card = l ∧ (l - 1) * l + 2 ≤ ∑ v ∈ B, f v := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases heq : S.card = l
    · exact ⟨S, Subset.rfl, heq, by simpa only [heq] using hsum⟩
    · by_cases hlow : ∃ v ∈ S, f v ≤ l - 1
      · obtain ⟨v, hv, hfv⟩ := hlow
        have hcount := card_erase_add_one hv
        have hsplit := sum_erase_add S f hv
        have hsize' : l ≤ (S.erase v).card := by omega
        have hsum' : (l - 1) * (S.erase v).card + 2 ≤ ∑ w ∈ S.erase v, f w := by
          nlinarith
        obtain ⟨B, hBS, hcard, hsumB⟩ := ih _ (by omega) (S.erase v) hsize'
          (fun w hw ↦ hcap w (mem_erase.mp hw).2) hsum' rfl
        exact ⟨B, hBS.trans (erase_subset _ _), hcard, hsumB⟩
      · have hfull : ∀ v ∈ S, f v = l := by
          intro v hv
          have h := hcap v hv
          have hnot : ¬f v ≤ l - 1 := fun h ↦ hlow ⟨v, hv, h⟩
          omega
        obtain ⟨B, hBS, hcard⟩ := exists_subset_card_eq hsize
        refine ⟨B, hBS, hcard, ?_⟩
        have hB : (∑ v ∈ B, f v) = l * l := by
          calc
            _ = ∑ _v ∈ B, l := sum_congr rfl (fun v hv ↦ hfull v (hBS hv))
            _ = l * l := by rw [sum_const, hcard, smul_eq_mul]
        rw [hB]
        have hpred : l - 1 + 1 = l := by omega
        nlinarith

/-- A full-degree vertex and a dense balanced part can be selected
disjointly from an unbalanced bipartite degree sequence. -/
theorem exists_full_degree_and_dense_subset {V : Type*} [DecidableEq V]
    (f : V → ℕ) {l : ℕ} (hl : 2 ≤ l) (S : Finset V) (hsize : l + 1 ≤ S.card)
    (hcap : ∀ v ∈ S, f v ≤ l) (hsum : (l - 1) * S.card + 3 ≤ ∑ v ∈ S, f v) :
    ∃ y ∈ S, f y = l ∧ ∃ B ⊆ S.erase y, B.card = l ∧
      (l - 1) * l + 2 ≤ ∑ v ∈ B, f v := by
  have hex : ∃ y ∈ S, f y = l := by
    by_contra h
    push Not at h
    have hbound : (∑ v ∈ S, f v) ≤ (l - 1) * S.card := by
      calc
        _ ≤ ∑ _v ∈ S, (l - 1) :=
          sum_le_sum (fun v hv ↦ by have := hcap v hv; have := h v hv; omega)
        _ = _ := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    omega
  obtain ⟨y, hy, hfy⟩ := hex
  have hcount := card_erase_add_one hy
  have hsplit := sum_erase_add S f hy
  have hsum' : (l - 1) * (S.erase y).card + 2 ≤ ∑ v ∈ S.erase y, f v := by
    have hpred : l - 1 + 1 = l := by omega
    nlinarith
  obtain ⟨B, hBS, hcard, hB⟩ := exists_dense_degree_subset f hl (S.erase y) (by omega)
    (fun v hv ↦ hcap v (mem_erase.mp hv).2) hsum'
  exact ⟨y, hy, hfy, B, hBS, hcard, hB⟩

end Erdos1105

#print axioms Erdos1105.exists_full_degree_and_dense_subset
