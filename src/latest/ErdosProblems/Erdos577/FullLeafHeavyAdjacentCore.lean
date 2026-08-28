import ErdosProblems.Erdos577.FullLeafHeavyAdjacentGeometry

/-! The dense core supplies the two actual blocks needed to force a fifth edge. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.two_complete_core_partition_of_four {z : V}
    (hz : z ∉ p.triangle ∪ a) (hfour : degreeIn G z (insert (p.vertices 3) a) = 4)
    (hr : ∀ w ∈ a, G.Adj p.center w) (hb : ∀ w ∈ a, G.Adj (p.vertices 2) w) :
    ∃ f : BlockPartition G (insert z (p.triangle ∪ a)), f.weightSum (edgeCount G) = 12 := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  obtain ⟨t, ht, hcl, hrem⟩ := dense_triangle_four_subset p.triangle_clique h.core_clique
    hd h.dense p.center_mem_triangle (show p.vertices 2 ∈ p.triangle by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)) hr hb
    (show (insert (p.vertices 3) a).filter (G.Adj z) ⊆
        (p.triangle ∪ a) \ {p.center, p.vertices 2} by
      rw [← h.second_five_eq]
      exact filter_subset _ _) hfour
  have htK := (ht.trans (filter_subset _ _)).trans h.second_five_subset
  have hfirst : G.IsNClique 4 (insert z t) := hcl.insert
    (fun w hw ↦ (mem_filter.mp (ht hw)).2)
  have hsecond : G.IsNClique 4 ((p.triangle ∪ a) \ t) := by
    refine ⟨hrem, ?_⟩
    rw [card_sdiff_of_subset htK, card_union_of_disjoint hd, p.triangle_clique.card_eq,
      h.core_clique.card_eq, hcl.card_eq]
  obtain ⟨f, hf⟩ := FullLeafHeavy.partition_of_core_split htK hz
    (QuadOn.of_clique hfirst.card_eq hfirst.isClique) hsecond
  refine ⟨f, ?_⟩
  rw [edgeCount_clique hfirst.isClique, hfirst.card_eq] at hf
  norm_num only [Nat.choose] at hf
  exact hf

theorem Configuration.second_clique_or_centers_full :
    G.IsNClique 5 (insert (p.vertices 3) a) ∨
      (∀ w ∈ a, G.Adj p.center w) ∧ (∀ w ∈ a, G.Adj (p.vertices 2) w) := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  rcases dense_join_clique_or_cross_gap p.triangle_clique h.core_clique hd h.dense with
    hcl | ⟨u, _, v, hva, _, _, hcl⟩
  · exact Or.inl ⟨SimpleGraph.IsClique.subset (coe_subset.mpr h.second_five_subset) hcl,
      h.second_five_card⟩
  · by_cases hu : u = p.center ∨ u = p.vertices 2
    · have hsub : insert (p.vertices 3) a ⊆ (p.triangle ∪ a).erase u := by
        intro z hz
        refine mem_erase.mpr ⟨?_, h.second_five_subset hz⟩
        rcases hu with rfl | rfl
        · exact (h.second_avoids hz).2.1
        · exact (h.second_avoids hz).2.2
      exact Or.inl ⟨SimpleGraph.IsClique.subset (coe_subset.mpr hsub)
        (clique_erase_of_add_edge hcl), h.second_five_card⟩
    · have hrow {d : V} (hdt : d ∈ p.triangle) (hdu : d ≠ u) : ∀ w ∈ a, G.Adj d w := by
        intro w hw
        have hdw : d ≠ w := fun he ↦ disjoint_left.mp hd (he ▸ hdt) hw
        have hdv : d ≠ v := fun he ↦ disjoint_left.mp hd (he ▸ hdt) hva
        exact adj_of_add_edge_of_avoids_endpoints
          (hcl (mem_union_left _ hdt) (mem_union_right _ hw) hdw) hdu hdv
      exact Or.inr ⟨hrow p.center_mem_triangle (Ne.symm (not_or.mp hu).1),
        hrow (by simp [Paw.triangle]) (Ne.symm (not_or.mp hu).2)⟩

lemma Configuration.second_neighbor_edge_of_three {z : V}
    (hthree : 3 ≤ degreeIn G z (insert (p.vertices 3) a)) :
    ∃ u ∈ insert (p.vertices 3) a, ∃ v ∈ insert (p.vertices 3) a,
      G.Adj z u ∧ G.Adj z v ∧ G.Adj u v := by
  have hout : p.vertices 3 ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) hh
  rw [degreeIn_insert G z (p.vertices 3) hout] at hthree
  have htwo : 2 ≤ degreeIn G z a := by split_ifs at hthree <;> omega
  obtain ⟨u, hu, v, hv, hzu, hzv, huv⟩ :=
    FullLeafHeavy.neighbor_edge_of_clique h.core_clique.isClique htwo
  exact ⟨u, mem_insert_of_mem hu, v, mem_insert_of_mem hv, hzu, hzv, huv⟩

theorem Configuration.second_neighbor_edge_of_heavy_pair {z w : V}
    (hz : z ∉ p.triangle ∪ a)
    (hpair : 6 ≤ degreeIn G z (insert (p.vertices 3) a) +
      degreeIn G w (insert (p.vertices 3) a))
    (hno : ¬∃ f : BlockPartition G (insert z (p.triangle ∪ a)),
      f.weightSum (edgeCount G) = 12) :
    ∃ u ∈ insert (p.vertices 3) a, ∃ v ∈ insert (p.vertices 3) a,
      G.Adj w u ∧ G.Adj w v ∧ G.Adj u v := by
  have hzfour : degreeIn G z (insert (p.vertices 3) a) ≤ 4 := by
    have hbound := degreeIn_le_card G z (insert (p.vertices 3) a)
    rw [h.second_five_card] at hbound
    by_contra hmore
    exact hno (h.two_complete_core_partition hz (by omega))
  by_cases hwthree : 3 ≤ degreeIn G w (insert (p.vertices 3) a)
  · exact h.second_neighbor_edge_of_three hwthree
  · have hwtwo : 2 ≤ degreeIn G w (insert (p.vertices 3) a) := by omega
    rcases h.second_clique_or_centers_full with hcl | ⟨hr, hb⟩
    · exact FullLeafHeavy.neighbor_edge_of_clique hcl.isClique hwtwo
    · exact False.elim (hno (h.two_complete_core_partition_of_four hz (by omega) hr hb))

theorem Configuration.core_partition_of_second_neighbor_edge {z u v : V}
    (hz : z ∉ p.triangle ∪ a)
    (hu : u ∈ insert (p.vertices 3) a) (hv : v ∈ insert (p.vertices 3) a)
    (hzu : G.Adj z u) (hzv : G.Adj z v) (huv : G.Adj u v) :
    ∃ f : BlockPartition G (insert z (p.triangle ∪ a)), 11 ≤ f.weightSum (edgeCount G) := by
  obtain ⟨t, ht, hcl, hut, hvt, hrem⟩ := h.second_triangle_extension hu hv huv
  have htK := ht.trans h.second_five_subset
  have hout : z ∉ t := fun hh ↦ hz (htK hh)
  have htwo := JointFinal.two_neighbors_degree hut hvt huv.ne hzu hzv
  obtain ⟨hquad, hedge⟩ := JointFinal.triangle_plus_two_five hcl hout htwo
  obtain ⟨f, hf⟩ := FullLeafHeavy.partition_of_core_split htK hz hquad hrem
  exact ⟨f, by omega⟩

end Erdos577.FullLeafCore
