import ErdosProblems.Erdos73.ComponentAugmenting

/-! A surplus of matching edges supplies disjoint augmenting paths. -/

namespace Erdos73

open SimpleGraph Finset Erdos556
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_disjoint_augmentingPaths {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N) {k : ℕ}
    (hk : M.card + k ≤ N.card) :
    ∃ P : Fin k → GraphPath G,
      (∀ i, IsMatchingAugmentingPath M (P i)) ∧
        Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) := by
  classical
  let H := matchingUnion hM hN
  let good : Finset H.ConnectedComponent := Finset.univ.filter
    (fun C => (componentMatching M C).card < (componentMatching N C).card)
  have hbound (C : H.ConnectedComponent) :
      (componentMatching N C).card ≤
        (componentMatching M C).card + if C ∈ good then 1 else 0 := by
    by_cases hc : C ∈ good
    · have hh := (exists_augmentingPath_of_component_surplus hM hN C
        (Finset.mem_filter.mp hc).2).1
      rw [if_pos hc, hh]
    · have hh : (componentMatching N C).card ≤ (componentMatching M C).card := by
        simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hc
      simpa only [if_neg hc, Nat.add_zero] using hh
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun C _ => hbound C)
  rw [Finset.sum_add_distrib,
    sum_componentMatching_card (matchingUnion_right_matching hM hN),
    sum_componentMatching_card (matchingUnion_left_matching hM hN)] at hsum
  have hgoodSum : (∑ C : H.ConnectedComponent, if C ∈ good then 1 else 0) = good.card := by
    simp
  rw [hgoodSum] at hsum
  have hkgood : k ≤ good.card := by omega
  let emb : Fin k ↪ good :=
    (Fin.castLEEmb (by simpa using hkgood)).trans (Fintype.equivFin good).symm.toEmbedding
  have hgood (i : Fin k) :
      (componentMatching M (emb i).val).card < (componentMatching N (emb i).val).card :=
    (Finset.mem_filter.mp (emb i).property).2
  choose P hP hset using fun i =>
    (exists_augmentingPath_of_component_surplus hM hN (emb i).val (hgood i)).2
  refine ⟨P, hP, ?_⟩
  intro i j hij
  rw [hset i, hset j]
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have hc := ConnectedComponent.eq_of_common_vertex (Set.mem_toFinset.mp hvi)
    (Set.mem_toFinset.mp hvj)
  exact hij (emb.injective (Subtype.ext hc))

end Erdos73
