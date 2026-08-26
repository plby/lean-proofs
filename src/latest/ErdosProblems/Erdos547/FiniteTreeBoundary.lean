import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Counting the boundary of a subtree with internal degree at most two
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

theorem sum_degreeIn_comm (A B : Finset U) :
    ∑ u ∈ A, degreeIn T B u = ∑ v ∈ B, degreeIn T A v := by
  classical
  have hrepr (S : Finset U) (u : U) : degreeIn T S u =
      ∑ v ∈ S, (if T.Adj u v then 1 else 0 : ℕ) := by simp [degreeIn]
  simp_rw [hrepr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  simp only [T.adj_comm]

theorem degreeIn_add_sdiff [DecidableEq U] {I H : Finset U} (hIH : I ⊆ H) (v : U) :
    degreeIn T I v + degreeIn T (H \ I) v = degreeIn T H v := by
  classical
  have hdis : Disjoint (I.filter (T.Adj v)) ((H \ I).filter (T.Adj v)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
      (Finset.mem_filter.mp hu).1
  unfold degreeIn
  rw [← Finset.card_union_of_disjoint hdis,
    ← Finset.filter_union, Finset.union_sdiff_of_subset hIH]

theorem sum_degreeIn_tree {I : Finset U} (hI : (T.induce (I : Set U)).IsTree) :
    (∑ v ∈ I, degreeIn T I v) + 2 = 2 * I.card := by
  classical
  have hs : ∑ v : (I : Set U), (T.induce (I : Set U)).degree v =
      ∑ v ∈ I, degreeIn T I v := by
    simp only [← degreeIn_eq_induce_degree]
    exact Finset.sum_finset_coe _ _
  have hd := (T.induce (I : Set U)).sum_degrees_eq_twice_card_edges
  have he := hI.card_edgeFinset
  rw [hs] at hd
  have hc : Fintype.card ↥(I : Set U) = I.card := by simp
  rw [hc] at he
  omega

open scoped Classical in
theorem card_boundary_le_two_of_degreeIn_le_two {I H : Finset U}
    (hI : (T.induce (I : Set U)).IsTree) (hIH : I ⊆ H)
    (hdeg : ∀ u ∈ I, degreeIn T H u ≤ 2) :
    ((H \ I).filter (fun v ↦ 0 < degreeIn T I v)).card ≤ 2 := by
  classical
  have hbound : ((H \ I).filter (fun v ↦ 0 < degreeIn T I v)).card ≤
      ∑ v ∈ H \ I, degreeIn T I v := by
    calc
      _ = ∑ v ∈ H \ I, (if 0 < degreeIn T I v then 1 else 0 : ℕ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs <;> omega
  rw [sum_degreeIn_comm T (H \ I) I] at hbound
  have hsum : (∑ v ∈ I, degreeIn T I v) + (∑ v ∈ I, degreeIn T (H \ I) v) ≤
      2 * I.card := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ v ∈ I, degreeIn T H v :=
        Finset.sum_congr rfl (fun v _ ↦ degreeIn_add_sdiff T hIH v)
      _ ≤ ∑ _v ∈ I, 2 := Finset.sum_le_sum hdeg
      _ = _ := by simp [Nat.mul_comm]
  have htree := sum_degreeIn_tree T hI
  omega

end Erdos547

#print axioms Erdos547.card_boundary_le_two_of_degreeIn_le_two
