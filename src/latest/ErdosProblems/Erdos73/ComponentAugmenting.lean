import ErdosProblems.Erdos73.MatchingAugmenting

/-! A component with more edges of the second matching is an augmenting path. -/

namespace Erdos73

open SimpleGraph Finset Erdos556
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open scoped Classical in
theorem exists_augmentingPath_of_component_surplus {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N)
    (C : (matchingUnion hM hN).ConnectedComponent)
    (hsurplus : (componentMatching M C).card < (componentMatching N C).card) :
    (componentMatching N C).card = (componentMatching M C).card + 1 ∧
      ∃ P : GraphPath G, IsMatchingAugmentingPath M P ∧ P.vertexSet = C.supp.toFinset := by
  classical
  let H := matchingUnion hM hN
  have hMH := matchingUnion_left_matching hM hN
  have hNH := matchingUnion_right_matching hM hN
  let MC := componentMatching M C
  let NC := componentMatching N C
  change MC.card < NC.card at hsurplus
  have hMC : EdgeMatching H MC := matchingOn_isMatching hMH C.supp.toFinset
  have hNC : EdgeMatching H NC := matchingOn_isMatching hNH C.supp.toFinset
  have hcsM := hMC.card_support
  have hcsN := hNC.card_support
  have hstrict : (matchingSupport MC).card < (matchingSupport NC).card := by omega
  obtain ⟨x, hxN, hxM⟩ := Finset.exists_mem_notMem_of_card_lt_card hstrict
  have hxC : x ∈ C.supp.toFinset := matchingOn_support_subset N C.supp.toFinset hxN
  have hxMg : x ∉ matchingSupport M := by
    intro hx
    apply hxM
    rw [show MC = componentMatching M C from rfl, componentMatching_support hMH]
    exact Finset.mem_inter.mpr ⟨hx, hxC⟩
  have hxNg : x ∈ matchingSupport N :=
    matchingSupport_mono (matchingOn_subset N C.supp.toFinset) hxN
  have hxadj : ∃ y, H.Adj x y := by
    obtain ⟨e, he, hxe⟩ := matchingSupport_mem.mp hxNg
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    exact ⟨y, Or.inr he⟩
  have hxdeg : ∀ a b, H.Adj x a → H.Adj x b → a = b := by
    intro a b ha hb
    have hnotM : ∀ y, s(x, y) ∉ M := fun y he => hxMg
      (matchingSupport_mem.mpr ⟨s(x, y), he, Sym2.mem_mk_left _ _⟩)
    rcases ha with ha | ha
    · exact (hnotM a ha).elim
    rcases hb with hb | hb
    · exact (hnotM b hb).elim
    exact matching_neighbors_unique hN ha hb
  obtain ⟨P, hsrc, hne, hclosed⟩ := GraphPath.exists_closed_path_from_degree_one
    (matchingUnion_twoNeighbors hM hN) x hxadj hxdeg
  have hset : P.vertexSet = C.supp.toFinset := by
    apply Finset.coe_injective
    have hh := P.vertexSet_eq_component_of_closed hclosed
    have hc : H.connectedComponentMk x = C :=
      (ConnectedComponent.mem_supp_iff C x).mp (Set.mem_toFinset.mp hxC)
    rw [hsrc, hc] at hh
    simpa only [Set.coe_toFinset] using hh
  let I := P.vertexSet \ {P.source, P.target}
  have hIcard : I.card + 2 = P.vertexSet.card := by
    have he : ({P.source, P.target} : Finset V) ⊆ P.vertexSet := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨P.source_mem_vertexSet, P.target_mem_vertexSet⟩
    simpa only [Finset.card_pair hne] using Finset.card_sdiff_add_card_eq_card he
  have hIM : I ⊆ matchingSupport MC := by
    intro v hv
    obtain ⟨hvP, hvE⟩ := Finset.mem_sdiff.mp hv
    have hs : v ≠ P.source := fun he => hvE (by simp [he])
    have ht : v ≠ P.target := fun he => hvE (by simp [he])
    obtain ⟨w, hwM, hwP⟩ := (internal_matched_in_union hM hN P hvP hs ht).1
    apply matchingSupport_mem.mpr
    refine ⟨s(v, w), mem_matchingOn.mpr ⟨hwM, ?_, ?_⟩, Sym2.mem_mk_left _ _⟩
    · exact hset ▸ hvP
    · exact hset ▸ (P.endpoints_mem_vertexSet_of_edgeSet hwP).2
  have hNP : matchingSupport NC ⊆ P.vertexSet := by
    rw [hset]
    exact matchingOn_support_subset N C.supp.toFinset
  have hIMcard := Finset.card_le_card hIM
  have hNPcard := Finset.card_le_card hNP
  have hdiff : NC.card = MC.card + 1 := by omega
  have hMfull : matchingSupport MC = I := by
    apply (Finset.eq_of_subset_of_card_le hIM ?_).symm
    omega
  have htMg : P.target ∉ matchingSupport M := by
    intro ht
    have htMC : P.target ∈ matchingSupport MC := by
      rw [show MC = componentMatching M C from rfl, componentMatching_support hMH]
      exact Finset.mem_inter.mpr ⟨ht, hset ▸ P.target_mem_vertexSet⟩
    rw [hMfull] at htMC
    exact (Finset.mem_sdiff.mp htMC).2 (by simp)
  have haug : IsMatchingAugmentingPath M P := by
    refine ⟨hne, ?_, htMg, ?_⟩
    · simpa only [hsrc] using hxMg
    · intro v hv hs ht
      exact (internal_matched_in_union hM hN P hv hs ht).1
  refine ⟨hdiff, P.mapLe (matchingUnion_le hM hN),
    haug.mapLe (matchingUnion_le hM hN), ?_⟩
  simpa only [GraphPath.mapLe_vertexSet] using hset

end Erdos73
