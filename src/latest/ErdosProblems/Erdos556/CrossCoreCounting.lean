import ErdosProblems.Erdos556.DisjointDenseCores

/-! Counting edges between two disjoint cores to select vertices for absorption. -/

namespace Erdos556

open SimpleGraph Finset

theorem neighbor_inter_card_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) :
    (G.neighborFinset v ∩ A).card = ∑ u ∈ A, if G.Adj v u then 1 else 0 := by
  rw [sum_boole]
  congr 1
  ext u
  simp only [mem_inter, mem_neighborFinset, mem_filter, and_comm]

theorem cross_degree_sum_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    ∑ v ∈ B, (G.neighborFinset v ∩ A).card =
      ∑ u ∈ A, (G.neighborFinset u ∩ B).card := by
  simp_rw [neighbor_inter_card_eq_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

theorem cross_degree_sum_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (hdis : Disjoint A B) :
    (∑ v ∈ B, (G.neighborFinset v ∩ A).card) +
      (∑ u ∈ A, (Gᶜ.neighborFinset u ∩ B).card) = A.card * B.card := by
  classical
  rw [cross_degree_sum_comm G A B, ← sum_add_distrib]
  have hsum (u : V) (hu : u ∈ A) :
      (G.neighborFinset u ∩ B).card + (Gᶜ.neighborFinset u ∩ B).card = B.card := by
    rw [neighbor_inter_card_eq_sum, neighbor_inter_card_eq_sum, ← sum_add_distrib]
    calc
      (∑ v ∈ B, ((if G.Adj u v then 1 else 0) +
        if Gᶜ.Adj u v then 1 else 0)) = ∑ _v ∈ B, 1 := by
        apply sum_congr rfl
        intro v hv
        have huv : u ≠ v := fun h => (Finset.disjoint_left.mp hdis hu) (h ▸ hv)
        by_cases h : G.Adj u v <;> simp [compl_adj, huv, h]
      _ = B.card := by simp
  simp_rw [sum_congr rfl hsum]
  simp

theorem sum_le_of_few_large_values {V : Type*} [DecidableEq V]
    (B : Finset V) (f : V → ℕ) (a k : ℕ) (hmax : ∀ v ∈ B, f v ≤ a)
    (hgood : (B.filter (fun v => k + 1 ≤ f v)).card ≤ k) :
    ∑ v ∈ B, f v ≤ k * (a + B.card) := by
  classical
  let C := B.filter (fun v => k + 1 ≤ f v)
  have hCB : C ⊆ B := filter_subset _ _
  have hC : ∑ v ∈ C, f v ≤ C.card * a := by
    calc
      _ ≤ ∑ _v ∈ C, a := sum_le_sum fun v hv => hmax v (hCB hv)
      _ = _ := by simp
  have hD : ∑ v ∈ B \ C, f v ≤ (B \ C).card * k := by
    calc
      _ ≤ ∑ _v ∈ B \ C, k := by
        apply sum_le_sum
        intro v hv
        have hn : ¬ k + 1 ≤ f v := by
          intro h
          exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, h⟩)
        omega
      _ = _ := by simp
  have hc : C.card ≤ k := hgood
  have hd : (B \ C).card ≤ B.card := card_le_card sdiff_subset
  have hs := sum_sdiff hCB (f := f)
  have hm₁ := Nat.mul_le_mul_right a hc
  have hm₂ := Nat.mul_le_mul_right k hd
  nlinarith

theorem exists_absorbable_cross_set {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (a k : ℕ)
    (hdis : Disjoint A B) (hA : A.card = a) (hB : B.card = a) (hsize : 4 * k < a) :
    (∃ W ⊆ B, W.card = k ∧ ∀ v ∈ W, k + 1 ≤ (G.neighborFinset v ∩ A).card) ∨
    (∃ W ⊆ A, W.card = k ∧ ∀ v ∈ W, k + 1 ≤ (Gᶜ.neighborFinset v ∩ B).card) := by
  classical
  let R := B.filter (fun v => k + 1 ≤ (G.neighborFinset v ∩ A).card)
  let C := A.filter (fun v => k + 1 ≤ (Gᶜ.neighborFinset v ∩ B).card)
  by_cases hR : k ≤ R.card
  · obtain ⟨W, hWR, hW⟩ := exists_subset_card_eq hR
    exact Or.inl ⟨W, hWR.trans (filter_subset _ _), hW,
      fun v hv => (mem_filter.mp (hWR hv)).2⟩
  by_cases hC : k ≤ C.card
  · obtain ⟨W, hWC, hW⟩ := exists_subset_card_eq hC
    exact Or.inr ⟨W, hWC.trans (filter_subset _ _), hW,
      fun v hv => (mem_filter.mp (hWC hv)).2⟩
  have hred := sum_le_of_few_large_values B
    (fun v => (G.neighborFinset v ∩ A).card) a k
    (fun v _ => (card_le_card inter_subset_right).trans hA.le)
    (show R.card ≤ k by omega)
  have hblue := sum_le_of_few_large_values A
    (fun v => (Gᶜ.neighborFinset v ∩ B).card) a k
    (fun v _ => (card_le_card inter_subset_right).trans hB.le)
    (show C.card ≤ k by omega)
  have hsum := cross_degree_sum_complement G A B hdis
  rw [hB] at hred
  rw [hA] at hblue
  rw [hA, hB] at hsum
  have ha : 0 < a := by omega
  exfalso
  nlinarith

#print axioms exists_absorbable_cross_set

end Erdos556
