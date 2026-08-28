import ErdosProblems.Erdos577.FullLeafHeavyThreeRow

/-! Dense-core triangle extensions and two complete blocks at a full second-side column. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.second_triangle_extension {u v : V}
    (hu : u ∈ insert (p.vertices 3) a) (hv : v ∈ insert (p.vertices 3) a) (huv : G.Adj u v) :
    ∃ t ⊆ insert (p.vertices 3) a, G.IsNClique 3 t ∧ u ∈ t ∧ v ∈ t ∧
      G.IsNClique 4 ((p.triangle ∪ a) \ t) := by
  have hd : Disjoint p.triangle a :=
    (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
  obtain ⟨t, ht, hcl, hut, hvt, hrem⟩ := dense_triangle_edge_extension p.triangle_clique
    h.core_clique hd h.dense p.center_mem_triangle (show p.vertices 2 ∈ p.triangle by
      simp [Paw.triangle]) (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
    (by simpa only [← h.second_five_eq] using hu)
    (by simpa only [← h.second_five_eq] using hv) huv
  have ht' : t ⊆ insert (p.vertices 3) a := by simpa only [← h.second_five_eq] using ht
  refine ⟨t, ht', hcl, hut, hvt, hrem, ?_⟩
  rw [card_sdiff_of_subset (ht'.trans h.second_five_subset), card_union_of_disjoint hd,
    p.triangle_clique.card_eq, h.core_clique.card_eq, hcl.card_eq]

theorem Configuration.core_split_of_full {z : V} (hz : z ∉ p.triangle ∪ a)
    (hfull : degreeIn G z (insert (p.vertices 3) a) = 5) :
    ∃ t ⊆ insert (p.vertices 3) a, G.IsNClique 3 t ∧
      G.IsNClique 4 (insert z t) ∧ G.IsNClique 4 ((p.triangle ∪ a) \ t) := by
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by rw [h.core_clique.card_eq]; decide)
  obtain ⟨t, ht, hcl, _, _, hrem⟩ := h.second_triangle_extension (mem_insert_of_mem hu)
    (mem_insert_of_mem hv) (h.core_clique.isClique hu hv huv)
  have hrow := (degreeIn_eq_card_iff z (insert (p.vertices 3) a)).mp
    (hfull.trans h.second_five_card.symm)
  have hnew : G.IsNClique 4 (insert z t) := hcl.insert (fun w hw ↦ hrow w (ht hw))
  have hout : z ∉ t := fun hh ↦ hz (h.second_five_subset (ht hh))
  have hsize : (insert z t).card = 4 := by rw [card_insert_of_notMem hout, hcl.card_eq]
  exact ⟨t, ht, hcl, ⟨hnew.isClique, hsize⟩, hrem⟩

theorem Configuration.two_complete_core_partition {z : V} (hz : z ∉ p.triangle ∪ a)
    (hfull : degreeIn G z (insert (p.vertices 3) a) = 5) :
    ∃ f : BlockPartition G (insert z (p.triangle ∪ a)), f.weightSum (edgeCount G) = 12 := by
  obtain ⟨t, ht, _, hfirst, hsecond⟩ := h.core_split_of_full hz hfull
  have htK := ht.trans h.second_five_subset
  have hdis : Disjoint (insert z t) ((p.triangle ∪ a) \ t) := disjoint_insert_left.mpr
    ⟨fun hh ↦ hz (mem_sdiff.mp hh).1, disjoint_sdiff_self_right⟩
  let f := (BlockPartition.single (QuadOn.of_clique hfirst.card_eq hfirst.isClique)).union
    (BlockPartition.single (QuadOn.of_clique hsecond.card_eq hsecond.isClique)) hdis
  have he : (insert z t) ∪ ((p.triangle ∪ a) \ t) = insert z (p.triangle ∪ a) := by
    rw [insert_union, union_sdiff_of_subset htK]
  have hw : f.weightSum (edgeCount G) = 12 := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single, edgeCount_clique hfirst.isClique,
      edgeCount_clique hsecond.isClique, hfirst.card_eq, hsecond.card_eq]
    rfl
  let all : BlockPartition G (insert z (p.triangle ∪ a)) := {
    blocks := f.blocks
    disjoint := f.disjoint
    cover := f.cover.trans he
    quad := f.quad }
  exact ⟨all, hw⟩

end Erdos577.FullLeafCore
