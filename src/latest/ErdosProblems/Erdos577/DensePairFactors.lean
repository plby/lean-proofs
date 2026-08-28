import ErdosProblems.Erdos577.DensePairConfig

/-! Exact factor completions for the three pairs of spokes, with an arbitrary exposed vertex. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PairConfig.exposed_pair_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support) :
    ¬LocalFactor G (insert z ({p.center, d 2, d 3} ∪ j)) := by
  intro hf
  obtain ⟨e, _, ht, htri, _, _, hkeep⟩ := h.exposed_chain hc
  have hu : ({p.center, d 2, d 3} : Finset V) ⊆ e.triangle ∪ d.support := by
    rw [htri]
    exact insert_subset (mem_union_left _ p.center_mem_triangle)
      (insert_subset (mem_union_right _ ((d.mem_support _).mpr ⟨2, rfl⟩))
        (singleton_subset_iff.mpr (mem_union_right _ ((d.mem_support _).mpr ⟨3, rfl⟩))))
  have hr : QuadOn G ((e.triangle ∪ d.support) \ {p.center, d 2, d 3}) := by
    rw [htri]
    exact QuadOn.of_clique h.pair.primary.card_eq h.pair.primary.isClique
  have hsel : ({j} : Finset (Finset V)) ⊆ e.blocks :=
    singleton_subset_iff.mpr (hkeep j hj hjs)
  have hna : d.support ∉ ({j} : Finset (Finset V)) := by simpa using hjd.symm
  apply hn (e.hasPacking_of_selected_core hcard (hkeep d.support h.core h.different)
    {j} hsel hna hu hr ?_)
  simpa only [singleton_biUnion, id_eq, ht] using hf.partition

theorem PairConfig.mixed_pair_no_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    ¬LocalFactor G (insert z (insert p.leaf ({d i, p.center} ∪ j))) := by
  intro hf
  have hFQ := h.paw_disjoint h.first
  have hFJ := h.paw_disjoint hj
  have hDQ : Disjoint d.support s := c.property.blocks_disjoint h.core h.first h.different
  have hJQ : Disjoint j s := c.property.blocks_disjoint hj h.first hjs
  have hm (a : Fin 4) : p.vertices a ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨a, rfl⟩
  have hdi : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hdiQ : d i ∉ s := fun hh ↦ disjoint_left.mp hDQ hdi hh
  have hdis : Disjoint (insert p.leaf ({d i, p.center} ∪ j)) s := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ (hm 0) hh, ?_⟩
    refine disjoint_union_left.mpr ⟨?_, hJQ⟩
    exact disjoint_insert_left.mpr ⟨hdiQ,
      disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hFQ (hm 1) hh)⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbdi : p.vertices 2 ≠ d i := fun he ↦
    disjoint_left.mp h.pair.disjoint (hm 2) (he.symm ▸ hdi)
  have hbout : p.vertices 2 ∉ (insert p.leaf ({d i, p.center} ∪ j)) ∪ s := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, ⟨hbdi, hbr⟩, fun hh ↦ disjoint_left.mp hFJ (hm 2) hh⟩,
      fun hh ↦ disjoint_left.mp hFQ (hm 2) hh⟩
  obtain ⟨part⟩ := hf.partition
  let parts := part.replacementUnion hdis hbout h.exposed (BlockPartition.single h.second_quad)
  have he : insert (p.vertices 2) ((insert p.leaf ({d i, p.center} ∪ j)) ∪ s) =
      insert p.leaf ({d i, p.center, p.vertices 2} ∪
        ({s, j} : Finset (Finset V)).biUnion id) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, singleton_union]
    rw [union_comm j s, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) (d i), insert_comm (p.vertices 2) p.center]
  have hsel : ({s, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr hj)
  have hna : d.support ∉ ({s, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro h.different hjd.symm
  have hu : ({d i, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ d.support :=
    insert_subset (mem_union_right _ hdi) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (JointFirst.hasPacking_of_selected_core hcard p h.paw h.core {s, j}
    hsel hna hu (h.pair.mixed_complement i hi) ⟨he ▸ parts⟩)

end Erdos577.DenseObstruction
