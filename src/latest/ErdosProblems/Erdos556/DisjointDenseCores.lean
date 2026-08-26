import ErdosProblems.Erdos556.CoreCleaning

/-! Cleaning two cores of opposite colours and removing their small overlap. -/

namespace Erdos556

open SimpleGraph Finset

theorem dense_core_bound_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) (d : ℕ)
    (hAS : A ⊆ S)
    (hcore : ∀ v ∈ S, S.card ≤ (G.neighborFinset v ∩ S).card + d) :
    ∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + d := by
  intro v hv
  have hS := neighbor_and_complement_in_set_card G S v (hAS hv)
  have hA := neighbor_and_complement_in_set_card G A v hv
  have hc := hcore v (hAS hv)
  have hm : (Gᶜ.neighborFinset v ∩ A).card ≤ (Gᶜ.neighborFinset v ∩ S).card :=
    card_le_card (inter_subset_inter_left hAS)
  omega

theorem opposite_clean_cores_intersection_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B S T : Finset V) (r : ℕ) (hAS : A ⊆ S) (hBT : B ⊆ T)
    (hA : ∀ v ∈ A, (Gᶜ.neighborFinset v ∩ S).card ≤ r)
    (hB : ∀ v ∈ B, (G.neighborFinset v ∩ T).card ≤ r) :
    (A ∩ B).card ≤ 2 * r + 1 := by
  classical
  by_cases hne : (A ∩ B).Nonempty
  · obtain ⟨v, hv⟩ := hne
    have h := neighbor_and_complement_in_set_card G (A ∩ B) v hv
    have hred : (G.neighborFinset v ∩ (A ∩ B)).card ≤ r := by
      apply (card_le_card (inter_subset_inter_left
        ((inter_subset_right : A ∩ B ⊆ B).trans hBT))).trans
      exact hB v (mem_inter.mp hv).2
    have hblue : (Gᶜ.neighborFinset v ∩ (A ∩ B)).card ≤ r := by
      apply (card_le_card (inter_subset_inter_left
        ((inter_subset_left : A ∩ B ⊆ A).trans hAS))).trans
      exact hA v (mem_inter.mp hv).1
    omega
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty]
    omega

theorem exists_disjoint_dense_cores {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) (r t : ℕ)
    (hr : 0 < r)
    (hS : 2 * (Gᶜ.induce (S : Set V)).edgeFinset.card ≤ r * t)
    (hT : 2 * (G.induce (T : Set V)).edgeFinset.card ≤ r * t) :
    ∃ A B : Finset V, A ⊆ S ∧ B ⊆ T ∧ Disjoint A B ∧
      S.card ≤ A.card + t + 2 * r + 1 ∧ T.card ≤ B.card + t ∧
      (∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + (r + 1)) ∧
      (∀ v ∈ B, B.card ≤ (Gᶜ.neighborFinset v ∩ B).card + (r + 1)) := by
  classical
  obtain ⟨A, hAS, hAbad, hA⟩ := exists_clean_core Gᶜ S r
  obtain ⟨B, hBT, hBbad, hB⟩ := exists_clean_core G T r
  have hAloss : S.card - A.card ≤ t := Nat.le_of_mul_le_mul_left (hAbad.trans hS) hr
  have hBloss : T.card - B.card ≤ t := Nat.le_of_mul_le_mul_left (hBbad.trans hT) hr
  have hinter := opposite_clean_cores_intersection_bound G A B S T r hAS hBT hA hB
  have hdis : Disjoint (A \ B) B := Finset.disjoint_left.mpr fun _ hv => (mem_sdiff.mp hv).2
  refine ⟨A \ B, B, sdiff_subset.trans hAS, hBT, hdis, ?_, ?_, ?_, ?_⟩
  · have hcard := card_sdiff_add_card_inter A B
    omega
  · omega
  · apply dense_core_after_cleaning G (A \ B) S r (sdiff_subset.trans hAS)
    intro v hv
    exact hA v (mem_sdiff.mp hv).1
  · apply dense_core_after_cleaning Gᶜ B T r hBT
    intro v hv
    have heq : Gᶜᶜ.neighborFinset v = G.neighborFinset v := by ext w; simp
    rw [heq]
    exact hB v hv

#print axioms exists_disjoint_dense_cores

end Erdos556
