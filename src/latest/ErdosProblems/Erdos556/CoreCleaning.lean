import ErdosProblems.Erdos556.DenseCoreAbsorption
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Deleting vertices incident with too many missing edges. -/

namespace Erdos556

open SimpleGraph Finset

theorem sum_induced_degrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ v ∈ S, (G.neighborFinset v ∩ S).card =
      2 * (G.induce (S : Set V)).edgeFinset.card := by
  classical
  rw [← (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges]
  simp_rw [degree_induce_finset_eq]
  exact (Finset.sum_coe_sort S (fun v => (G.neighborFinset v ∩ S).card)).symm

theorem exists_clean_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (r : ℕ) :
    ∃ A : Finset V, A ⊆ S ∧
      r * (S.card - A.card) ≤ 2 * (G.induce (S : Set V)).edgeFinset.card ∧
      ∀ v ∈ A, (G.neighborFinset v ∩ S).card ≤ r := by
  classical
  let A := S.filter (fun v => (G.neighborFinset v ∩ S).card ≤ r)
  have hAS : A ⊆ S := filter_subset _ _
  refine ⟨A, hAS, ?_, fun v hv => (mem_filter.mp hv).2⟩
  have hbad (v : V) (hv : v ∈ S \ A) : r ≤ (G.neighborFinset v ∩ S).card := by
    have hvS := (mem_sdiff.mp hv).1
    have hvA := (mem_sdiff.mp hv).2
    have hn : ¬ (G.neighborFinset v ∩ S).card ≤ r := by
      intro h
      exact hvA (mem_filter.mpr ⟨hvS, h⟩)
    omega
  calc
    r * (S.card - A.card) = ∑ _v ∈ S \ A, r := by
      rw [sum_const, smul_eq_mul, card_sdiff, inter_eq_left.mpr hAS, Nat.mul_comm]
    _ ≤ ∑ v ∈ S \ A, (G.neighborFinset v ∩ S).card := sum_le_sum hbad
    _ ≤ ∑ v ∈ S, (G.neighborFinset v ∩ S).card :=
      sum_le_sum_of_subset sdiff_subset
    _ = 2 * (G.induce (S : Set V)).edgeFinset.card := sum_induced_degrees G S

theorem neighbor_and_complement_in_set_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) (hv : v ∈ S) :
    (G.neighborFinset v ∩ S).card + (Gᶜ.neighborFinset v ∩ S).card + 1 = S.card := by
  classical
  have hdis : Disjoint (G.neighborFinset v ∩ S) (Gᶜ.neighborFinset v ∩ S) := by
    apply Finset.disjoint_left.mpr
    intro u hu huc
    have h := (G.mem_neighborFinset v u).mp (mem_inter.mp hu).1
    have hc := (Gᶜ.mem_neighborFinset v u).mp (mem_inter.mp huc).1
    exact (show ¬ G.Adj v u from hc.2) h
  have hunion : (G.neighborFinset v ∩ S) ∪ (Gᶜ.neighborFinset v ∩ S) = S.erase v := by
    ext u
    simp only [mem_union, mem_inter, mem_neighborFinset, compl_adj, mem_erase]
    constructor
    · rintro (⟨h, hu⟩ | ⟨⟨h, _⟩, hu⟩)
      · exact ⟨h.ne.symm, hu⟩
      · exact ⟨h.symm, hu⟩
    · rintro ⟨huv, hu⟩
      by_cases h : G.Adj v u
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr ⟨⟨huv.symm, h⟩, hu⟩
  have h := congrArg Finset.card hunion
  rw [card_union_of_disjoint hdis, card_erase_of_mem hv] at h
  have hp := card_pos.mpr ⟨v, hv⟩
  omega

theorem dense_core_after_cleaning {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A S : Finset V) (r : ℕ)
    (hAS : A ⊆ S) (hclean : ∀ v ∈ A, (Gᶜ.neighborFinset v ∩ S).card ≤ r) :
    ∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + (r + 1) := by
  intro v hv
  have h := neighbor_and_complement_in_set_card G A v hv
  have hle : (Gᶜ.neighborFinset v ∩ A).card ≤ r :=
    (card_le_card (inter_subset_inter_left hAS)).trans (hclean v hv)
  omega

#print axioms exists_clean_core
#print axioms dense_core_after_cleaning

end Erdos556
