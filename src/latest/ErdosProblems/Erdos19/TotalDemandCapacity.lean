import ErdosProblems.Erdos19.CapacityAugmentation

/-! # Buffer capacities from total incidence demand

This strengthens the degree-based load estimate to the exact total demand,
which is useful when a hypergraph has small volume but some large degrees.
-/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E I : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

theorem exists_capacity_augmentation_of_demand_bound
    (H : FiniteHypergraph V E) (r D L : ℕ) (hD : 0 < D) (hL : 0 < L)
    (B P : I → Finset V) (T : I → ℕ)
    (hB : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hP : Pairwise fun i j ↦ Disjoint (P i) (P j))
    (hpool : ∀ i, P i ⊆ H.vertexSet)
    (hunused : ∀ e i, Disjoint (H.support e) (P i))
    (hbound : H.IsBounded r)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, x ≠ y → H.edgePairDegree x y ≤ L)
    (hloadBound : ∀ i, (∑ e : E, (H.support e ∩ B i).card) ≤ T i)
    (hroom : ∀ i, T i / D + 2 * r +
      (2 * r) * ((2 * r) * D / L) < (P i).card) :
    ∃ K : FiniteHypergraph V E,
      K.vertexSet = H.vertexSet ∧ (∀ e, H.support e ⊆ K.support e) ∧
      K.IsBounded (2 * r) ∧ (∀ v ∈ K.vertexSet, K.edgeDegree v ≤ D) ∧
      (∀ x ∈ K.vertexSet, ∀ y ∈ K.vertexSet, x ≠ y → K.edgePairDegree x y ≤ L) ∧
      ∀ e i, (K.support e ∩ P i).card = (H.support e ∩ B i).card := by
  classical
  let a : E → I → ℕ := fun e i ↦ (H.support e ∩ B i).card
  let M : I → ℕ := T
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
    exact hloadBound i
  obtain ⟨K, hKv, hKs, hKr, hKd, hKp, hKcount⟩ :=
    exists_augmentation_of_demands H (2 * r) D L hD hL P hP hpool M a hroom
      hdeg hpair hrank hload
  refine ⟨K, hKv, hKs, hKr, hKd, hKp, ?_⟩
  intro e i
  simpa only [disjoint_iff_inter_eq_empty.mp (hunused e i), card_empty, zero_add, a] using
    hKcount e i

#print axioms exists_capacity_augmentation_of_demand_bound

end Erdos19
