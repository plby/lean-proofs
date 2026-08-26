import ErdosProblems.Erdos547.MatchingEmbedding

/-!
# Realizing pairs with large combined neighbourhoods
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_neighbor_union [DecidableEq V] (x z : V) :
    (G.neighborFinset x ∪ G.neighborFinset z).card =
      G.degree x + (G.neighborFinset z \ G.neighborFinset x).card := by
  have h₁ := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset z)
  have h₂ := Finset.card_sdiff_add_card_inter (G.neighborFinset z) (G.neighborFinset x)
  rw [Finset.inter_comm] at h₂
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h₁
  rw [G.card_neighborFinset_eq_degree] at h₂
  omega

open scoped Classical in
theorem many_neighbours_with_large_union [DecidableEq V] (m d k : ℕ)
    (hdk : d < k) (hroom : k + d ≤ m) (hdegree : ∀ z, m ≤ G.degree z + d)
    (hescape : ∀ x, G.degree x ≤ m → ∀ a, k ≤ ((G.neighborFinset a).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card) :
    ∀ a x, k ≤ ((G.neighborFinset a).filter
      fun z ↦ m < (G.neighborFinset x ∪ G.neighborFinset z).card).card := by
  classical
  intro a x
  by_cases hx : G.degree x ≤ m
  · apply (hescape x hx a).trans
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzN, hzout⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzN, ?_⟩
    rw [card_neighbor_union G x z]
    have hdeg := hdegree x
    omega
  · have hfull : (G.neighborFinset a).filter
        (fun z ↦ m < (G.neighborFinset x ∪ G.neighborFinset z).card) = G.neighborFinset a := by
      apply Finset.filter_eq_self.mpr
      intro z _
      rw [card_neighbor_union G x z]
      omega
    rw [hfull, G.card_neighborFinset_eq_degree]
    have hdeg := hdegree a
    omega

open scoped Classical in
theorem exists_copy_with_paired_neighbourhoods {U : Type*} [Fintype U] [Nonempty V]
    (T : SimpleGraph U) (hT : T.IsTree) (P : SimpleGraph U) (hP : IsPairingOn P Finset.univ)
    (m d k : ℕ) (hsize : Fintype.card U ≤ k) (hdk : d < k) (hroom : k + d ≤ m)
    (hdegree : ∀ z, m ≤ G.degree z + d)
    (hescape : ∀ x, G.degree x ≤ m → ∀ a, k ≤ ((G.neighborFinset a).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card) :
    ∃ f : T.Copy G, ∀ u v, P.Adj u v →
      m < (G.neighborFinset (f u) ∪ G.neighborFinset (f v)).card := by
  classical
  apply exists_copy_with_matching_constraints T G hT P hP
    (fun x z ↦ m < (G.neighborFinset x ∪ G.neighborFinset z).card)
  · intro a b h
    simpa only [Finset.union_comm] using h
  · intro a x
    convert hsize.trans
      (many_neighbours_with_large_union G m d k hdk hroom hdegree hescape a x) using 1
    · congr 2
    · congr 1
      ext z
      simp

end Erdos547

#print axioms Erdos547.exists_copy_with_paired_neighbourhoods
