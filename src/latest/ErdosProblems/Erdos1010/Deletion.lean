import ErdosProblems.Erdos1010.GraphCuts

/-! # Vertex deletion and edge trimming

The first three lemmas preserve the proved deletion infrastructure from the
original main file. The exact triangle partition strengthens that work.
-/

open Finset

namespace Erdos1010

lemma card_compl_singleton_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) : Fintype.card {x : V // x ∈ ({v}ᶜ : Set V)} = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set]
  simp

lemma card_induce_compl_singleton_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.induce ({v}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - G.degree v := by
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

lemma card_induce_compl_singleton_triangles_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card ≤ (G.cliqueFinset 3).card := by
  let s : Set V := ({v}ᶜ : Set V)
  let f : s ↪ V := Function.Embedding.subtype _
  have hmap : (G.induce s).map f ≤ G := by
    intro x y hxy
    rw [SimpleGraph.map_adj] at hxy
    rcases hxy with ⟨x', y', hxy', rfl, rfl⟩
    exact hxy'
  calc
    ((G.induce s).cliqueFinset 3).card =
        (((G.induce s).map f).cliqueFinset 3).card := by
          rw [SimpleGraph.cliqueFinset_map]
          · simp
          · norm_num
    _ ≤ (G.cliqueFinset 3).card :=
      Finset.card_le_card (SimpleGraph.cliqueFinset_mono
        (G := (G.induce s).map f) (H := G) hmap)

lemma card_induce_compl_singleton_triangles_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card + (trianglesAt G v).card =
      (G.cliqueFinset 3).card := by
  have hcard' : ((G.induce ({v}ᶜ : Set V)).cliqueFinset 3).card =
      ((G.cliqueFinset 3).filter fun p ↦ v ∉ p).card := by
    let s : Set V := ({v}ᶜ : Set V)
    let f : s ↪ V := Function.Embedding.subtype _
    apply card_bij (fun p _ ↦ p.map f)
    · intro p hp
      apply mem_filter.mpr
      constructor
      · apply G.mem_cliqueFinset_iff.mpr
        exact (SimpleGraph.isNClique_induce_iff s p 3).mp
          ((G.induce s).mem_cliqueFinset_iff.mp hp)
      · intro hv
        obtain ⟨a, ha, hav⟩ := mem_map.mp hv
        have han : a.val ≠ v := by
          simpa only [s, Set.mem_compl_iff, Set.mem_singleton_iff] using a.property
        exact han hav
    · intro p hp q hq h
      exact Finset.map_injective f h
    · intro p hp
      obtain ⟨hpG, hpv⟩ := mem_filter.mp hp
      let q : Finset s := p.subtype (fun x ↦ x ∈ s)
      have hmap : q.map f = p := by
        apply subtype_map_of_mem
        intro x hx
        simp only [s, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hxv
        subst x
        exact hpv hx
      refine ⟨q, ?_, hmap⟩
      apply (G.induce s).mem_cliqueFinset_iff.mpr
      apply (SimpleGraph.isNClique_induce_iff s q 3).mpr
      rw [show q.map (Function.Embedding.subtype _) = p from hmap]
      exact G.mem_cliqueFinset_iff.mp hpG
  rw [hcard']
  have h := card_filter_add_card_filter_not (s := G.cliqueFinset 3) (fun p ↦ v ∈ p)
  unfold trianglesAt
  omega

lemma exists_subgraph_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hm : m ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet.ncard = m := by
  classical
  obtain ⟨E, hEG, hEcard⟩ := exists_subset_card_eq hm
  let H := G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))
  have hHG : H ≤ G := G.deleteEdges_le _
  have hH : H.edgeFinset = E := by
    unfold H
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact Finset.sdiff_sdiff_eq_self hEG
  refine ⟨H, hHG, ?_⟩
  have : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← H.coe_edgeFinset]
    exact Set.ncard_coe_finset _
  rw [this, hH, hEcard]

end Erdos1010
