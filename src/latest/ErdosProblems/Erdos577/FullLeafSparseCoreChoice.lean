import ErdosProblems.Erdos577.FullLeafSparseFullCase

/-! A four-subset of the second side supplies a center-to-center path removing the core gap. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma near_clique_path_through_four {core u : Finset V} {r b x z : V}
    (hcl : (G ⊔ SimpleGraph.edge x z).IsClique core)
    (hr : r ∈ core) (hb : b ∈ core) (hx : x ∈ core) (hz : z ∈ core) (hxz : x ≠ z)
    (hpool : (core \ {r, b}).card = 5) (hu : u ⊆ core \ {r, b}) (hu4 : u.card = 4) :
    ∃ v ∈ u, G.Adj r v ∧ G.Adj v b ∧ G.IsClique (core \ {r, v, b} : Finset V) := by
  have havoid (v : V) (hv : v ∈ u) : v ≠ r ∧ v ≠ b := by
    have hh := (mem_sdiff.mp (hu hv)).2
    simpa only [mem_insert, mem_singleton, not_or] using hh
  have hsub : u ⊆ core := hu.trans sdiff_subset
  have hswap : (G ⊔ SimpleGraph.edge z x).IsClique core := by
    simpa only [SimpleGraph.edge_comm x z] using hcl
  by_cases hend : x ∈ ({r, b} : Finset V) ∨ z ∈ ({r, b} : Finset V)
  · obtain ⟨v, hv, hvout⟩ := exists_mem_notMem_of_card_lt_card
      (show ({x, z} : Finset V).card < u.card by
        have hh : ({x, z} : Finset V).card ≤ 2 := card_le_two
        omega)
    have hvends : v ≠ x ∧ v ≠ z := by
      simpa only [mem_insert, mem_singleton, not_or] using hvout
    have hvr := adj_of_add_edge_of_avoids_endpoints
      (hcl (hsub hv) hr (havoid v hv).1) hvends.1 hvends.2
    have hvb := adj_of_add_edge_of_avoids_endpoints
      (hcl (hsub hv) hb (havoid v hv).2) hvends.1 hvends.2
    refine ⟨v, hv, hvr.symm, hvb, ?_⟩
    rcases hend with hend | hend
    · apply clique_sdiff_of_add_edge hcl
      simp only [mem_insert, mem_singleton] at hend ⊢
      tauto
    · apply clique_sdiff_of_add_edge hswap
      simp only [mem_insert, mem_singleton] at hend ⊢
      tauto
  · have hxavoid : x ≠ r ∧ x ≠ b := by
      have hh : x ∉ ({r, b} : Finset V) := fun hh ↦ hend (Or.inl hh)
      simpa only [mem_insert, mem_singleton, not_or] using hh
    have hzavoid : z ≠ r ∧ z ≠ b := by
      have hh : z ∉ ({r, b} : Finset V) := fun hh ↦ hend (Or.inr hh)
      simpa only [mem_insert, mem_singleton, not_or] using hh
    have hpairs : ({x, z} : Finset V) ⊆ core \ {r, b} := by
      apply insert_subset
      · exact mem_sdiff.mpr ⟨hx, by simpa only [mem_insert, mem_singleton, not_or] using hxavoid⟩
      · apply singleton_subset_iff.mpr
        exact mem_sdiff.mpr ⟨hz, by simpa only [mem_insert, mem_singleton, not_or] using hzavoid⟩
    have heither : x ∈ u ∨ z ∈ u := by
      by_contra hh
      have hsmall : u ⊆ (core \ {r, b}) \ {x, z} := by
        intro v hv
        refine mem_sdiff.mpr ⟨hu hv, ?_⟩
        simp only [mem_insert, mem_singleton]
        rintro (rfl | rfl)
        · exact hh (Or.inl hv)
        · exact hh (Or.inr hv)
      have hc := card_le_card hsmall
      rw [hu4, card_sdiff_of_subset hpairs, hpool, card_pair hxz] at hc
      omega
    have hpath (v : V) (hv : v ∈ u) : G.Adj r v ∧ G.Adj v b := by
      exact ⟨adj_of_add_edge_of_avoids_endpoints
        (hcl hr (hsub hv) (havoid v hv).1.symm) hxavoid.1.symm hzavoid.1.symm,
        (adj_of_add_edge_of_avoids_endpoints
          (hcl hb (hsub hv) (havoid v hv).2.symm) hxavoid.2.symm hzavoid.2.symm).symm⟩
    rcases heither with hxu | hzu
    · exact ⟨x, hxu, (hpath x hxu).1, (hpath x hxu).2,
        clique_sdiff_of_add_edge hcl (by simp)⟩
    · exact ⟨z, hzu, (hpath z hzu).1, (hpath z hzu).2,
        clique_sdiff_of_add_edge hswap (by simp)⟩

end Erdos577.FullLeafSparse

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.center_path_through_four (h : Configuration c p s a y)
    {u : Finset V} (hu : u ⊆ insert (p.vertices 3) a) (hu4 : u.card = 4) :
    ∃ z ∈ u, G.Adj p.center z ∧ G.Adj z (p.vertices 2) ∧
      G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, z, p.vertices 2}) := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  have hr : p.center ∈ p.triangle ∪ a := mem_union_left _ p.center_mem_triangle
  have hb : p.vertices 2 ∈ p.triangle ∪ a := mem_union_left _ (by simp [Paw.triangle])
  have hrb : p.center ≠ p.vertices 2 := p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have hpool : ((p.triangle ∪ a) \ {p.center, p.vertices 2}).card = 5 := by
    rw [← h.second_five_eq, h.second_five_card]
  have hu' : u ⊆ (p.triangle ∪ a) \ {p.center, p.vertices 2} := h.second_five_eq ▸ hu
  have hpath : ∃ z ∈ u, G.Adj p.center z ∧ G.Adj z (p.vertices 2) ∧
      G.IsClique ((p.triangle ∪ a) \ {p.center, z, p.vertices 2} : Finset V) := by
    rcases dense_join_clique_or_cross_gap p.triangle_clique h.core_clique hd h.dense with
      hcl | ⟨v, hv, w, hw, hvw, _, hcl⟩
    · exact FullLeafSparse.near_clique_path_through_four
        (SimpleGraph.IsClique.mono
          (le_sup_left : G ≤ G ⊔ SimpleGraph.edge p.center (p.vertices 2)) hcl)
        hr hb hr hb hrb hpool hu' hu4
    · exact FullLeafSparse.near_clique_path_through_four hcl hr hb
        (mem_union_left _ hv) (mem_union_right _ hw) hvw hpool hu' hu4
  obtain ⟨z, hz, hrz, hzb, hcl⟩ := hpath
  have ht : G.IsNClique 3 ({p.center, z, p.vertices 2} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hrz, p.edge12, hzb⟩
  have htSub : ({p.center, z, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a := by
    exact insert_subset hr (insert_subset (h.second_five_subset (hu hz))
      (singleton_subset_iff.mpr hb))
  refine ⟨z, hz, hrz, hzb, hcl, ?_⟩
  rw [card_sdiff_of_subset htSub, card_union_of_disjoint hd, p.triangle_clique.card_eq,
    h.core_clique.card_eq, ht.card_eq]

end Erdos577.FullLeafCore
