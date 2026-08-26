import ErdosProblems.Erdos19.GraphDegreeAccounting
import Mathlib.Data.Set.Card.Arithmetic

/-! # The exact residual degree after packing a matching family -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I]

theorem matching_family_degree (G : _root_.SimpleGraph V) (M : I → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)) (v : V) :
    ((⨆ i, (M i).spanningCoe).neighborSet v).ncard =
      ∑ i : I, if v ∈ (M i).verts then 1 else 0 := by
  rw [neighborSet_iSup, Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) (fun i j hij ↦
    disjoint_neighborSet.mpr (hdis hij) v)]
  simp only [finsum_eq_sum_of_fintype, matching_neighbor_ncard G _ (hM _)]

theorem matching_family_degree_add_absences (G : _root_.SimpleGraph V) (M : I → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)) (v : V) :
    ((⨆ i, (M i).spanningCoe).neighborSet v).ncard +
      (∑ i : I, if v ∈ (M i).verts then 0 else 1) = Fintype.card I := by
  rw [matching_family_degree G M hM hdis v, ← sum_add_distrib]
  have hper : ∀ i : I, (if v ∈ (M i).verts then 1 else 0) +
      (if v ∈ (M i).verts then 0 else 1) = 1 := by
    intro i
    split_ifs <;> rfl
  simp only [hper, sum_const, card_univ, smul_eq_mul, mul_one]

theorem residual_degree_bound_after_matching_family (G : _root_.SimpleGraph V)
    (M : I → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)) (D : ℕ)
    (hbudget : ∀ v, (G.neighborSet v).ncard +
      (∑ i : I, if v ∈ (M i).verts then 0 else 1) ≤ D + Fintype.card I) :
    ∀ v, ((G \ ⨆ i, (M i).spanningCoe).neighborSet v).ncard ≤ D := by
  intro v
  have hU : (⨆ i, (M i).spanningCoe) ≤ G :=
    iSup_le (fun i _ _ h ↦ (show (M i).Adj _ _ from h).adj_sub)
  have hsub : (⨆ i, (M i).spanningCoe).neighborSet v ⊆ G.neighborSet v := fun _ h ↦ hU h
  have heq := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hcovered := matching_family_degree_add_absences G M hM hdis v
  have hb := hbudget v
  rw [neighborSet_sdiff]
  omega

#print axioms residual_degree_bound_after_matching_family

end Erdos19
