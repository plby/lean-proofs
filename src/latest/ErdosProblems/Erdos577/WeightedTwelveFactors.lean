import ErdosProblems.Erdos577.WeightedTwelveComplements

/-! Every common-path factor completes with actual first-block and dense-core complements. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.exposed_pair_no_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support) :
    ¬LocalFactor G (insert (q 3) ({p.center, d 2, d 3} ∪ j)) := by
  intro hf
  have hFQ := h.paw_disjoint h.first
  obtain ⟨e, _, _, _, hp', _, _, _, _, _, hkeep⟩ :=
    exists_swap hc hcard hn p h.paw h.first q rfl hFQ h.pattern
  let p' := exposedPaw p q hFQ h.pattern
  have htri : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ h.pattern
  have hu : ({p.center, d 2, d 3} : Finset V) ⊆ p'.triangle ∪ d.support := by
    rw [htri]
    exact insert_subset (mem_union_left _ p.center_mem_triangle)
      (insert_subset (mem_union_right _ ((d.mem_support _).mpr ⟨2, rfl⟩))
        (singleton_subset_iff.mpr (mem_union_right _ ((d.mem_support _).mpr ⟨3, rfl⟩))))
  have hr : QuadOn G ((p'.triangle ∪ d.support) \ {p.center, d 2, d 3}) := by
    rw [htri]
    exact QuadOn.of_clique h.pair.primary.card_eq h.pair.primary.isClique
  exact hn (JointCore.hasPacking_of_partial_core hcard p' hp'
    (hkeep d.support h.core h.different).1 (hkeep j hj hjq).1 hjd.symm hu hr hf.partition)

theorem Configuration.mixed_pair_no_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    ¬LocalFactor G (insert (q 3) (insert p.leaf ({d i, p.center} ∪ j))) := by
  intro hf
  have hFQ := h.paw_disjoint h.first
  have hFJ := h.paw_disjoint hj
  have hDQ : Disjoint d.support q.support :=
    c.property.blocks_disjoint h.core h.first h.different
  have hJQ : Disjoint j q.support := c.property.blocks_disjoint hj h.first hjq
  have hm (a : Fin 4) : p.vertices a ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨a, rfl⟩
  have hz : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hzQ : d i ∉ q.support := fun hh ↦ disjoint_left.mp hDQ hz hh
  have hdis : Disjoint (insert p.leaf ({d i, p.center} ∪ j)) q.support := by
    refine disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ (hm 0) hh, ?_⟩
    refine disjoint_union_left.mpr ⟨?_, hJQ⟩
    exact disjoint_insert_left.mpr ⟨hzQ,
      disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hFQ (hm 1) hh)⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbz : p.vertices 2 ≠ d i := fun he ↦ disjoint_left.mp h.pair.disjoint (hm 2) (he.symm ▸ hz)
  have hbout : p.vertices 2 ∉ (insert p.leaf ({d i, p.center} ∪ j)) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, ⟨hbz, hbr⟩, fun hh ↦ disjoint_left.mp hFJ (hm 2) hh⟩,
      fun hh ↦ disjoint_left.mp hFQ (hm 2) hh⟩
  have hym : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hrep := h.pattern.universal p q hFQ (q 3) hym
  obtain ⟨part⟩ := hf.partition
  let parts := part.replacementUnion hdis hbout hym (BlockPartition.single hrep)
  have he : insert (p.vertices 2) ((insert p.leaf ({d i, p.center} ∪ j)) ∪ q.support) =
      insert p.leaf ({d i, p.center, p.vertices 2} ∪
        ({q.support, j} : Finset (Finset V)).biUnion id) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, insert_union, singleton_union]
    rw [union_comm j q.support, insert_comm (p.vertices 2) p.leaf,
      insert_comm (p.vertices 2) (d i), insert_comm (p.vertices 2) p.center]
  have hsel : ({q.support, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr hj)
  have hna : d.support ∉ ({q.support, j} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro h.different hjd.symm
  have hu : ({d i, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ d.support :=
    insert_subset (mem_union_right _ hz) (insert_subset (mem_union_left _ p.center_mem_triangle)
      (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
  exact hn (JointFirst.hasPacking_of_selected_core hcard p h.paw h.core {q.support, j}
    hsel hna hu (h.pair.mixed_complement i hi) ⟨he ▸ parts⟩)

end Erdos577.WeightedTwelve
