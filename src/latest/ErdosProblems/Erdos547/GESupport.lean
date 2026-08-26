import ErdosProblems.Erdos547.GEOptimization

/-!
# Support and vertex classes in a Gallai–Edmonds partition
-/

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem mem_singletonVertices_iff (D : GallaiEdmondsPartition G) (u : V) :
    u ∈ D.singletonVertices ↔ {u} ∈ D.blocks := by
  constructor
  · intro hu
    obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hCF, hcard⟩ := Finset.mem_filter.mp hC
    obtain ⟨v, hCv⟩ := Finset.card_eq_one.mp hcard
    have huv : u = v := by simpa only [hCv, id_eq, Finset.mem_singleton] using huC
    simpa only [hCv, huv] using hCF
  · intro hu
    exact Finset.mem_biUnion.mpr ⟨{u}, Finset.mem_filter.mpr ⟨hu, Finset.card_singleton u⟩,
      Finset.mem_singleton_self u⟩

theorem singleton_not_separator (D : GallaiEdmondsPartition G) {u : V}
    (hu : u ∈ D.singletonVertices) : u ∉ D.separator := by
  have hC := (D.mem_singletonVertices_iff u).mp hu
  exact (Finset.mem_sdiff.mp (D.separates.part_subset hC (Finset.mem_singleton_self u))).2

theorem nontrivial_not_separator (D : GallaiEdmondsPartition G) {u : V}
    (hu : u ∈ D.nontrivialVertices) : u ∉ D.separator := by
  obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
  exact (Finset.mem_sdiff.mp (D.separates.part_subset (Finset.mem_filter.mp hC).1 huC)).2

theorem singleton_not_nontrivial (D : GallaiEdmondsPartition G) {u : V}
    (hu : u ∈ D.singletonVertices) : u ∉ D.nontrivialVertices := by
  intro hbig
  obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hbig
  obtain ⟨hCF, hcard⟩ := Finset.mem_filter.mp hC
  have heq : C = {u} := D.separates.eq_of_mem_parts hCF
    ((D.mem_singletonVertices_iff u).mp hu) huC (Finset.mem_singleton_self u)
  rw [heq, Finset.card_singleton] at hcard
  exact (lt_irrefl 1) hcard

theorem vertex_classes (D : GallaiEdmondsPartition G) (u : V) :
    u ∈ D.separator ∨ u ∈ D.singletonVertices ∨ u ∈ D.nontrivialVertices := by
  by_cases hu : u ∈ D.separator
  · exact Or.inl hu
  · obtain ⟨C, hC, huC⟩ := D.separates.exists_part
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩)
    have hpos := (D.separates.nonempty C hC).card_pos
    by_cases hcard : C.card = 1
    · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
        ⟨C, Finset.mem_filter.mpr ⟨hC, hcard⟩, huC⟩))
    · exact Or.inr (Or.inr (Finset.mem_biUnion.mpr
        ⟨C, Finset.mem_filter.mpr ⟨hC, by omega⟩, huC⟩))

theorem neighbour_of_singleton_mem_separator (D : GallaiEdmondsPartition G)
    {u v : V} (hu : u ∈ D.singletonVertices) (huv : G.Adj u v) : v ∈ D.separator := by
  by_contra hv
  have hpart := (D.mem_singletonVertices_iff u).mp hu
  have hvu := D.separates.closed {u} hpart u (Finset.mem_singleton_self u) v
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩) huv
  exact huv.ne (Finset.mem_singleton.mp hvu).symm

theorem completionSupport_symm (D : GallaiEdmondsPartition G) {u v : V}
    (h : D.CompletionSupport u v) : D.CompletionSupport v u := by
  rcases h with h | ⟨C, hC, hlarge, hu, hv⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨C, hC, hlarge, hv, hu⟩

theorem allowed_symm (D : GallaiEdmondsPartition G) {u v : V}
    (h : D.Allowed u v) : D.Allowed v u := by
  rcases h with h | h | h
  · exact Or.inl (D.completionSupport_symm h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem allowed_from_separator (D : GallaiEdmondsPartition G) {u v : V}
    (hu : u ∈ D.separator) (h : D.Allowed u v) :
    D.matching.Adj u v ∨ v ∈ D.singletonVertices := by
  rcases h with (h | ⟨C, hC, _, huC, _⟩) | ⟨_, hv⟩ | ⟨_, hus⟩
  · exact Or.inl h
  · exact (Finset.disjoint_left.mp (D.separates.part_disjoint_separator hC) huC hu).elim
  · exact Or.inr hv
  · exact (D.singleton_not_separator hus hu).elim

theorem not_allowed_separator (D : GallaiEdmondsPartition G) {u v : V}
    (hu : u ∈ D.separator) (hv : v ∈ D.separator) : ¬ D.Allowed u v := by
  intro h
  rcases D.allowed_from_separator hu h with hm | hs
  · rcases D.crosses u v hm with ⟨_, hv'⟩ | ⟨_, hu'⟩
    · exact hv' hv
    · exact hu' hu
  · exact D.singleton_not_separator hs hv

theorem IsFractionalGE.load_separator {D : GallaiEdmondsPartition G} {μ : FractionalMatching G}
    (h : D.IsFractionalGE μ) {u : V} (hu : u ∈ D.separator) : μ.load u = 1 :=
  h.1 u (Finset.mem_union_left _ hu)

theorem IsFractionalGE.load_nontrivial {D : GallaiEdmondsPartition G} {μ : FractionalMatching G}
    (h : D.IsFractionalGE μ) {u : V} (hu : u ∈ D.nontrivialVertices) : μ.load u = 1 :=
  h.1 u (Finset.mem_union_right _ hu)

theorem IsFractionalGE.allowed_of_pos {D : GallaiEdmondsPartition G} {μ : FractionalMatching G}
    (h : D.IsFractionalGE μ) {u v : V} (huv : 0 < μ.weight u v) : D.Allowed u v := by
  by_contra hnot
  rw [h.2 u v hnot] at huv
  exact (lt_irrefl 0) huv

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.neighbour_of_singleton_mem_separator
