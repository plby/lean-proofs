import ErdosProblems.Erdos19.DummyDemand
import ErdosProblems.Erdos19.CapacityColoring

/-! # Augmenting hyperedges to enforce buffer capacities -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E I : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

theorem sum_inter_card_le_of_disjoint (S : Finset V) (B : I → Finset V)
    (hB : Pairwise fun i j ↦ Disjoint (B i) (B j)) :
    (∑ i : I, (S ∩ B i).card) ≤ S.card := by
  classical
  have hd : ((univ : Finset I) : Set I).PairwiseDisjoint (fun i ↦ S ∩ B i) := by
    intro i _ j _ hij
    exact (hB hij).mono inter_subset_right inter_subset_right
  rw [← card_biUnion hd]
  apply card_le_card
  intro x hx
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
  exact (mem_inter.mp hi).1

theorem sum_support_inter_card_eq_sum_degree (H : FiniteHypergraph V E) (B : Finset V) :
    (∑ e : E, (H.support e ∩ B).card) = ∑ v ∈ B, H.edgeDegree v := by
  classical
  have hdegree (v : V) : H.edgeDegree v =
      ∑ e : E, if v ∈ H.support e then 1 else 0 := by
    unfold edgeDegree
    rw [card_eq_sum_ones, sum_filter]
  simp_rw [hdegree]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [inter_comm]
  simp

/-- Disjoint buffers can be given smaller disjoint dummy pools, provided the
pool-load slack beats the explicit codegree exclusion bound. Every future
proper coloring of the augmented hypergraph respects all buffer capacities. -/
theorem exists_capacity_augmentation
    (H : FiniteHypergraph V E) (r D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (B P : I → Finset V) (Dlow : I → ℕ)
    (hB : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hP : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (hpool : ∀ i, P i ⊆ H.vertexSet)
    (hunused : ∀ e i, Disjoint (H.support e) (P i))
    (hbound : H.IsBounded r)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L)
    (hlow : ∀ i v, v ∈ B i → H.edgeDegree v ≤ Dlow i)
    (hroom : ∀ i, ((B i).card * Dlow i) / D + 2 * r +
      (2 * r) * ((2 * r) * D / L) < (P i).card) :
    ∃ K : FiniteHypergraph V E,
      K.vertexSet = H.vertexSet ∧ (∀ e, H.support e ⊆ K.support e) ∧
      K.IsBounded (2 * r) ∧ (∀ v ∈ K.vertexSet, K.edgeDegree v ≤ D) ∧
      (∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y → K.edgePairDegree x y ≤ L) ∧
      ∀ e i, (K.support e ∩ P i).card = (H.support e ∩ B i).card := by
  classical
  let a : E → I → ℕ := fun e i ↦ (H.support e ∩ B i).card
  let M : I → ℕ := fun i ↦ (B i).card * Dlow i
  have hrank : ∀ e, (H.support e).card + ∑ i : I, a e i ≤ 2 * r := by
    intro e
    have hsum := sum_inter_card_le_of_disjoint (H.support e) B hB
    have hr := hbound e
    dsimp [a]
    omega
  have hzero : ∀ i v, v ∈ P i → H.edgeDegree v = 0 := by
    intro i v hv
    unfold edgeDegree
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro e _ he
    exact (Finset.disjoint_left.mp (hunused e i) he) hv
  have hload : ∀ i, (∑ d ∈ P i, H.edgeDegree d) + ∑ e : E, a e i ≤ M i := by
    intro i
    have hpzero : (∑ d ∈ P i, H.edgeDegree d) = 0 := sum_eq_zero (hzero i)
    rw [hpzero, zero_add]
    change (∑ e : E, (H.support e ∩ B i).card) ≤ (B i).card * Dlow i
    rw [sum_support_inter_card_eq_sum_degree]
    calc
      _ ≤ ∑ _v ∈ B i, Dlow i := sum_le_sum (hlow i)
      _ = _ := by simp
  obtain ⟨K, hKv, hKs, hKr, hKd, hKp, hKcount⟩ :=
    exists_augmentation_of_demands H (2 * r) D L hD hL P hP hpool M a hroom
      hdeg hpair hrank hload
  refine ⟨K, hKv, hKs, hKr, hKd, hKp, ?_⟩
  intro e i
  simpa only [disjoint_iff_inter_eq_empty.mp (hunused e i), card_empty, zero_add, a] using
    hKcount e i

#print axioms exists_capacity_augmentation

end Erdos19
