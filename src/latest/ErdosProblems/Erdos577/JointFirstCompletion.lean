import ErdosProblems.Erdos577.JointCoreCompletion
import ErdosProblems.Erdos577.PartitionReplacement

/-! Core complements extend a factor on any selected outside family,
with all other blocks retained. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_selected_core {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (bs : Finset (Finset V))
    (hbs : bs ⊆ c.blocks) (hna : a ∉ bs) {used : Finset V} (hu : used ⊆ p.triangle ∪ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ used))
    (hf : Nonempty (BlockPartition G (insert p.leaf (used ∪ bs.biUnion id)))) : HasPacking G k := by
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFO : Disjoint p.support (bs.biUnion id) := by
    apply disjoint_left.mpr
    intro v hv hvo
    obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hvo
    have hd := c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset (hbs hb))
    have hvR : v ∈ c.remainder := by rwa [← hp]
    exact disjoint_left.mp hd hvR hvb
  have hAO : Disjoint a (bs.biUnion id) := by
    apply disjoint_left.mpr
    intro v hv hvo
    obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hvo
    exact disjoint_left.mp (c.property.blocks_disjoint ha (hbs hb)
      (fun he ↦ hna (he.symm ▸ hb))) hv hvb
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hKO : Disjoint (p.triangle ∪ a) (bs.biUnion id) :=
    disjoint_union_left.mpr ⟨hFO.mono_left hT, hAO⟩
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hx : p.leaf ∉ (p.triangle ∪ a) ∪ bs.biUnion id := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact p.leaf_not_mem_triangle h
      · exact disjoint_left.mp hFA hxF h
    · exact disjoint_left.mp hFO hxF h
  obtain ⟨parts⟩ := TwoCore.partition_with_core_complement hKO hx hu hr hf
  have hsel : insert a bs ⊆ c.blocks := insert_subset ha hbs
  have he : insert p.leaf ((p.triangle ∪ a) ∪ bs.biUnion id) =
      c.remainder ∪ (insert a bs).biUnion id := by
    rw [← insert_union, ← insert_union, ← p.support_eq, hp]
    simp only [biUnion_insert, id_eq, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard (insert a bs) hsel (he ▸ parts)

end Erdos577.JointFirst
