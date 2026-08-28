import ErdosProblems.Erdos577.TwoCoreComplementFactor

/-! Complete a local partition with any complementary core quadrilateral.
The used triple may contain two triangle vertices and one block vertex. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_partial_core {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    {a s : Finset V} (ha : a ∈ c.blocks) (hs : s ∈ c.blocks) (has : a ≠ s)
    {used : Finset V} (hu : used ⊆ p.triangle ∪ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ used))
    (hf : Nonempty (BlockPartition G (insert p.leaf (used ∪ s)))) : HasPacking G k := by
  have hFS : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAS : Disjoint a s := c.property.blocks_disjoint ha hs has
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hKS : Disjoint (p.triangle ∪ a) s := disjoint_union_left.mpr ⟨hFS.mono_left hT, hAS⟩
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hx : p.leaf ∉ (p.triangle ∪ a) ∪ s := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact p.leaf_not_mem_triangle h
      · exact disjoint_left.mp hFA hxF h
    · exact disjoint_left.mp hFS hxF h
  obtain ⟨parts⟩ := TwoCore.partition_with_core_complement hKS hx hu hr hf
  have hsel : ({a, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hs)
  have he : insert p.leaf ((p.triangle ∪ a) ∪ s) =
      c.remainder ∪ ({a, s} : Finset (Finset V)).biUnion id := by
    rw [← insert_union, ← insert_union, ← p.support_eq, hp]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard {a, s} hsel (he ▸ parts)

end Erdos577.JointCore
